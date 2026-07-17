open Monad_lib
open Chain.Ethereum
open Numeric
open Byte_string

let failwith fmt =
  Format.kfprintf (fun ppf -> Format.pp_print_newline ppf () ; exit 1) Format.err_formatter fmt

let input_file = ref None
let output_file = ref None
let chain_id = ref Chain.Monad.Testnet.chain_id

let usage_str = "Usage: resign --input FILE --output FILE [--chain_id ID]\n"

let () =
  Arg.(
    parse
      [ ( "--input"
        , Arg.String (fun filename -> input_file := Some filename)
        , "Blockchain test fixture input file" )
      ; ( "--output"
        , Arg.String (fun filename -> output_file := Some filename)
        , "Blockchain test fixture output file" )
      ; ( "--chain_id"
        , Arg.Int (fun id -> chain_id := Uint.of_int id)
        , Format.sprintf "Chain id (default: %s)" (Uint.to_string !chain_id) ) ]
      (fun extra_arg ->
        Format.printf "Unknown argument %s\n" extra_arg ;
        Format.printf "%s" usage_str ;
        exit (-1) )
      usage_str )

let input_file = Option.get !input_file
let output_file = Option.get !output_file
let chain_id = !chain_id

module Wallet = struct
  open Libsecp256k1.External

  type wallet = {secret_key : Key.secret Key.t; address : Address.t}

  let of_secret_key (pk : B32.t) =
    let secret_key = Key.read_sk_exn Crypto.context (Bigstring.of_string (B32.to_bytes pk)) in
    let public_key = Key.neuterize_exn Crypto.context secret_key in
    let pkey_bytes =
      let bytes = Key.to_bytes ~compress:false Crypto.context public_key in
      Bytes.init 64 (fun i -> bytes.{i + 1})
    in
    let address = Address.of_bytes32_truncating (Crypto.keccak_256 pkey_bytes) in
    {secret_key; address}

  let known_wallets : (Address.t * wallet) list =
    List.map
      (fun pk ->
        let wallet = of_secret_key (B32.of_hex_string pk) in
        (wallet.address, wallet) )
      [ "0x0000000000000000000000000000000000000000000000000000000000000001"
        (*0x7E5F4552091A69125d5DfCb7b8C2659029395Bdf*)
      ; "0x0000000000000000000000000000000000000000000000000000000000000002"
        (*0x2B5AD5c4795c026514f8317c7a215E218DcCD6cF*)
      ; "0x0000000000000000000000000000000000000000000000000000000000000003"
        (*0x6813Eb9362372EEF6200f3b1dbC3f819671cBA69*)
      ; "0x0000000000000000000000000000000000000000000000000000000000000004"
        (*0x1efF47bc3a10a45D4B230B5d10E37751FE6AA718*) ]

  let re_sign_tx sender wallet tx =
    if sender = Option.get (Transaction.sender chain_id tx) then tx
    else
      match tx with
      | Legacy {nonce; gas_price; gas_limit; to_; value; data; _} ->
          let tx_hash =
            let tx_encoded =
              Rlp.(
                encode
                  (List
                     [ U64.to_rlp nonce
                     ; Uint.to_rlp gas_price
                     ; Uint.to_rlp gas_limit
                     ; Address.t_opt_to_rlp to_
                     ; U256.to_rlp value
                     ; Rlp.of_bytes data ] ) )
            in
            tx_encoded |> Crypto.keccak_256 |> B32.to_bytes |> Bigstring.of_string
          in
          let signature = Sign.sign_recoverable_exn Crypto.context ~sk:wallet.secret_key tx_hash in
          let rs = Sign.to_bytes Crypto.context signature in
          let r = U256.of_repr (B32.init (fun i -> rs.{i})) in
          let s = U256.of_repr (B32.init (fun i -> rs.{i + 32})) in
          let recid = Char.code rs.{64} in
          let v = U256.of_int (27 + recid) in
          let tx = Transaction.Legacy {nonce; gas_limit; value; r; s; to_; data; gas_price; v} in
          let sender' = Transaction.sender chain_id tx in
          assert (Address.(wallet.address = Option.get sender')) ;
          tx
      | _ -> assert false
end

(* Json utils. *)
open Yojson.Safe.Util

let ( .${} ) obj field = List.assoc field (to_assoc obj)
let ( .${}<- ) obj field value : Yojson.Safe.t =
  let obj = to_assoc obj in
  let obj =
    let rec loop fields =
      match fields with
      | [] -> [(field, value)]
      | (field', _value') :: fields when field = field' -> (field, value) :: fields
      | (field', value') :: fields -> (field', value') :: loop fields
    in
    loop obj
  in
  `Assoc obj

(*
let ( .$() ) arr i = List.nth (to_list arr) i
let ( .$()<- ) arr i value : Yojson.Safe.t =
  let l = to_list arr in
  assert (List.length l > i) ;
  let before = List.take (i - 1) l in
  let after = List.drop i l in
  `List (before @ (value :: after))
 *)

type acc = {wallet : Wallet.wallet; nonce : U256.t}
type state = acc Address.Map.t

let load_pre_state (pre_state : Yojson.Safe.t) : state =
  to_assoc pre_state
  |> List.map (fun (address, acc) ->
      let address = Address.of_hex_string address in
      match List.assoc_opt address Wallet.known_wallets with
      | None ->
          Format.eprintf
            "Address %s does not correspond to a known private key; it won't be able to submit transactions\n"
            (Address.to_hex_string address) ;
          None
      | Some wallet ->
          let nonce = U256.of_yojson_exn acc.${"nonce"} in
          Some (address, {wallet; nonce}) )
  |> List.filter_map Fun.id
  |> Address.Map.of_list

let rewire_transaction (tx : Yojson.Safe.t) (state : state) =
  let sender = Result.get_ok' (Address.of_yojson tx.${"sender"}) in
  let {wallet; nonce} =
    match Address.Map.find_opt sender state with
    | Some acc -> acc
    | None ->
        failwith "Cannot find the state for sender %s (private key not known?)\n"
          (Address.to_hex_string sender)
  in

  (* Update the transaction's nonce and increment it in the state. *)
  if tx.${"nonce"} <> U256.to_yojson nonce then
    Format.eprintf "Updating nonce for %s\n" (Yojson.Safe.pretty_to_string tx) ;
  let tx = tx.${"nonce"} <- U256.to_yojson nonce in
  let nonce = U256.(nonce + one) in
  let state = Address.Map.add sender {wallet; nonce} state in

  (* Parse and re-sign the transaction. *)
  let signed_tx =
    match Transaction.of_yojson tx with Ok tx -> Wallet.re_sign_tx sender wallet tx | _ -> assert false
  in
  let r, s, v = match signed_tx with Legacy {r; s; v; _} -> (r, s, v) | _ -> assert false in
  if tx.${"r"} <> U256.to_yojson r then
    Format.eprintf "Updating signature for %s\n" (Yojson.Safe.pretty_to_string tx) ;
  let tx = tx.${"r"} <- U256.to_yojson r in
  let tx = tx.${"s"} <- U256.to_yojson s in
  let tx = tx.${"v"} <- U256.to_yojson v in
  (tx, state)

let rewire_transactions_in_block (block : Yojson.Safe.t) (state : state) : Yojson.Safe.t * state =
  let txs = to_list block.${"transactions"} in
  let txs, state =
    let rec loop txs state =
      match txs with
      | [] -> ([], state)
      | tx :: txs ->
          let tx, state = rewire_transaction tx state in
          let txs, state = loop txs state in
          (tx :: txs, state)
    in
    loop txs state
  in
  ((block.${"transactions"} <- `List txs), state)

let rewire_test_case (test_case : Yojson.Safe.t) =
  let state = load_pre_state test_case.${"pre"} in
  let blocks = to_list test_case.${"blocks"} in
  let blocks, _state =
    let rec loop blocks state =
      match blocks with
      | [] -> ([], state)
      | b :: blocks ->
          let b, state = rewire_transactions_in_block b state in
          let blocks, state = loop blocks state in
          (b :: blocks, state)
    in
    loop blocks state
  in
  test_case.${"blocks"} <- `List blocks

let () =
  Yojson.Safe.from_file input_file
  |> to_assoc
  |> List.map (fun (name, test_case) -> (name, rewire_test_case test_case))
  |> fun assoc ->
  `Assoc assoc
  |> fun fixtures ->
  Out_channel.with_open_text output_file (fun out_channel ->
      Yojson.Safe.pretty_to_channel out_channel fixtures )
