open Monad_lib
open Test_utils.Utils
open Numeric
open Byte_string
open Chain.Ethereum
open Chain.Monad
open State

module ChainParams = struct
  let chain_id = Mainnet.chain_id
  let revision = `Eight
  let trace = false
end

module Wallet = struct
  open Libsecp256k1.External
  type t = {secret_key : Key.secret Key.t; address : Address.t}

  let of_secret_key (pk : B32.t) =
    let secret_key = Key.read_sk_exn Crypto.context (Bigstring.of_string (B32.to_bytes pk)) in
    let public_key = Key.neuterize_exn Crypto.context secret_key in
    let pkey_bytes =
      let bytes = Key.to_bytes ~compress:false Crypto.context public_key in
      Bytes.init 64 (fun i -> bytes.{i + 1})
    in
    let address = Address.of_bytes32_truncating (Crypto.keccak_256 pkey_bytes) in
    {secret_key; address}
end

type state = {nonces : U64.t Address.Map.t; blocks_rev : Block.t list}

let increment_and_get_nonce (addr : Address.t) (state : state) =
  let nonce = Address.Map.find_opt addr state.nonces |> Option.value ~default:U64.zero in
  let nonces = Address.Map.add addr U64.(one + nonce) state.nonces in
  (nonce, {state with nonces})

let mon x = mon_to_wei (U256.of_int x)
let wei x = U256.of_int x

let send
    ~(sender : Wallet.t)
    ~(receiver : Address.t)
    ~(value : U256.t)
    ?(gas_limit = Uint.(~$50_000))
    ?(data = Bytes.empty)
    ?(gas_price = Uint.(~$1)) =
 fun (state : state) ->
  let open Libsecp256k1.External in
  let nonce, state = increment_and_get_nonce sender.address state in
  let tx_hash =
    let tx_encoded =
      Rlp.(
        encode
          (List
             [ U64.to_rlp nonce
             ; Uint.to_rlp gas_price
             ; Uint.to_rlp gas_limit
             ; Address.to_rlp receiver
             ; U256.to_rlp value
             ; Rlp.of_bytes data ] ) )
    in
    tx_encoded |> Crypto.keccak_256 |> B32.to_bytes |> Bigstring.of_string
  in
  let signature = Sign.sign_recoverable_exn Crypto.context ~sk:sender.secret_key tx_hash in
  let rs = Sign.to_bytes Crypto.context signature in
  let r = U256.of_repr (B32.init (fun i -> rs.{i})) in
  let s = U256.of_repr (B32.init (fun i -> rs.{i + 32})) in
  let recid = Char.code rs.{64} in
  let v = U256.of_int (27 + recid) in
  let tx = Transaction.Legacy {nonce; gas_limit; value; r; s; to_ = Some receiver; data; gas_price; v} in
  let sender' = Transaction.sender Params.chain_id tx in
  assert (Address.(sender.address = Option.get sender')) ;
  (tx, state)

let block ?(gas_limit = Uint.(~$200_000_000)) transactions =
 fun (state : state) ->
  let n = Uint.of_int (List.length state.blocks_rev) in
  let last_block = List.hd state.blocks_rev in
  let block_header =
    { Block.Header.empty with
      gas_limit
    ; number = n
    ; timestamp = U256.(last_block.header.timestamp + one)
    ; ommers_hash = Crypto.keccak_256 Rlp.(encode (List [])) }
  in
  let transactions_rev, state =
    List.fold_left
      (fun (txs, state) tx ->
        let tx, state = tx state in
        (tx :: txs, state) )
      ([], state) transactions
  in
  let state =
    { state with
      blocks_rev =
        Block.{header = block_header; transactions = List.rev transactions_rev; ommers = []; withdrawals = []}
        :: state.blocks_rev }
  in
  ((), state)

let alice = Wallet.of_secret_key B32.(~@"45a915e4d060149eb4365960e6a7a45f334393093061116b197e3240065ff2d8")
let bob = Wallet.of_secret_key B32.(~@"45a915e4d060149eb4365960e6a7a45f334393093061116b197e3240065ff2d9")

let ( let$ ) x f =
 fun state ->
  let x, state = x state in
  f x state

let genesis_block =
  let header =
    { Block.Header.empty with
      gas_limit = Uint.(~$200_000_000)
    ; ommers_hash = Crypto.keccak_256 Rlp.(encode (List [])) }
  in
  {Block.header; transactions = []; ommers = []; withdrawals = []}

module Execution = Execution.Make (ChainParams)

let run_proc ~initial_allocation action =
  let (), {blocks_rev; _} = action {nonces = Address.Map.empty; blocks_rev = [genesis_block]} in
  let blocks = List.tl (List.rev blocks_rev) in
  let state =
    List.fold_left
      (fun s ({Wallet.address; _}, alloc) ->
        let open Lens.Infix in
        s.^(WorldState.account address |-- Account.balance) <- alloc )
      WorldState.empty initial_allocation
  in
  let state = {state with history = [genesis_block]} in
  List.fold_left
    (fun state block -> Result.get_ok (Execution.process_block ~verify:false state block))
    state blocks

let proc_test name ~initial_allocation ~postconditions action =
  Alcotest.test_case name `Quick (fun () ->
      let state = run_proc ~initial_allocation action in
      List.iter
        (fun ({Wallet.address; _}, expected_balance) ->
          let actual_balance = state.^(WorldState.account address).balance in
          Alcotest.check' u256
            ~msg:(Format.sprintf "Balance for %s" (Address.to_hex_string address))
            ~expected:expected_balance ~actual:actual_balance )
        postconditions )

let transfer_cost = wei 50_000

let () =
  let open Alcotest in
  run "Reserve balance checks"
    [ ( "Transactions in same block"
      , [ proc_test "Above reserve"
            ~initial_allocation:[(alice, mon 30)]
            ~postconditions:[(alice, U256.(mon 20 - transfer_cost - transfer_cost)); (bob, mon 10)]
            (block
               [ send ~sender:alice ~receiver:bob.address ~value:(mon 5)
               ; send ~sender:alice ~receiver:bob.address ~value:(mon 5) ] )
        ; proc_test "Dips into reserve"
            ~initial_allocation:[(alice, mon 19)]
            ~postconditions:[(alice, U256.(mon 14 - transfer_cost - transfer_cost)); (bob, mon 5)]
            (block
               [ send ~sender:alice ~receiver:bob.address ~value:(mon 5)
               ; send ~sender:alice ~receiver:bob.address ~value:(mon 5) ] ) ] )
    ; ( "One block later"
      , [ proc_test "Above reserve"
            ~initial_allocation:[(alice, mon 30)]
            ~postconditions:[(alice, U256.(mon 20 - transfer_cost - transfer_cost)); (bob, mon 10)]
            (let$ () = block [send ~sender:alice ~receiver:bob.address ~value:(mon 5)] in
             block [send ~sender:alice ~receiver:bob.address ~value:(mon 5)] )
        ; proc_test "Dips into reserve"
            ~initial_allocation:[(alice, mon 19)]
            ~postconditions:[(alice, U256.(mon 14 - transfer_cost - transfer_cost)); (bob, mon 5)]
            (let$ () = block [send ~sender:alice ~receiver:bob.address ~value:(mon 5)] in
             block [send ~sender:alice ~receiver:bob.address ~value:(mon 5)] ) ] )
    ; ( "Two blocks later"
      , [ proc_test "Above reserve"
            ~initial_allocation:[(alice, mon 30)]
            ~postconditions:[(alice, U256.(mon 20 - transfer_cost - transfer_cost)); (bob, mon 10)]
            (let$ () = block [send ~sender:alice ~receiver:bob.address ~value:(mon 5)] in
             let$ () = block [] in
             block [send ~sender:alice ~receiver:bob.address ~value:(mon 5)] )
        ; proc_test "Dips into reserve"
            ~initial_allocation:[(alice, mon 19)]
            ~postconditions:[(alice, U256.(mon 14 - transfer_cost - transfer_cost)); (bob, mon 5)]
            (let$ () = block [send ~sender:alice ~receiver:bob.address ~value:(mon 5)] in
             let$ () = block [] in
             block [send ~sender:alice ~receiver:bob.address ~value:(mon 5)] ) ] )
    ; ( "Three blocks later"
      , [ proc_test "Above reserve"
            ~initial_allocation:[(alice, mon 30)]
            ~postconditions:[(alice, U256.(mon 20 - transfer_cost - transfer_cost)); (bob, mon 10)]
            (let$ () = block [send ~sender:alice ~receiver:bob.address ~value:(mon 5)] in
             let$ () = block [] in
             let$ () = block [] in
             block [send ~sender:alice ~receiver:bob.address ~value:(mon 5)] )
        ; proc_test "Dips into reserve"
            ~initial_allocation:[(alice, mon 19)]
            ~postconditions:[(alice, U256.(mon 9 - transfer_cost - transfer_cost)); (bob, mon 10)]
            (let$ () = block [send ~sender:alice ~receiver:bob.address ~value:(mon 5)] in
             let$ () = block [] in
             let$ () = block [] in
             block [send ~sender:alice ~receiver:bob.address ~value:(mon 5)] ) ] ) ]
