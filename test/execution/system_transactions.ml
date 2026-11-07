open Monad_lib
open Test_utils.Utils
open Numeric
open Byte_string
open Chain.Ethereum

module Validator = Execution.Make (Params)

(* Public protocol signing key, not a user credential:
   category-labs/monad-bft, monad-system-calls/src/lib.rs, SYSTEM_SENDER_PRIV_KEY. *)
let system_key =
  B32.of_hex_string "b0358e6d701a955d9926676f227e40172763296b317ff554e49cdf2c2c35f8a7"

let sign ?(key = system_key) (tx : Transaction.legacy_tx) =
  let open Libsecp256k1.External in
  let secret_key = Key.read_sk_exn Crypto.context (Bigstring.of_string (B32.to_bytes key)) in
  let hash = Transaction.signing_hash Params.chain_id (Legacy tx) in
  let signature =
    Sign.sign_recoverable_exn Crypto.context ~sk:secret_key (Bigstring.of_string (B32.to_bytes hash))
    |> Sign.to_bytes Crypto.context
  in
  Transaction.Legacy
    { tx with
      r = U256.of_repr (B32.init (fun i -> signature.{i}))
    ; s = U256.of_repr (B32.init (fun i -> signature.{i + 32}))
    ; v = U256.of_int (27 + Char.code signature.{64}) }

let transaction ~nonce ~value ~data : Transaction.legacy_tx =
  { nonce = U64.of_int nonce
  ; gas_limit = Uint.zero
  ; value
  ; r = U256.zero
  ; s = U256.zero
  ; to_ = Some Staking.staking_address
  ; data
  ; gas_price = Uint.zero
  ; v = U256.of_int 27 }

let calldata (fn : ('i, 'o) Staking.Function.impl) (input : 'i) =
  let selector = Contract.Abi.Selector.to_bytes fn.signature.selector in
  let args = Contract.Type.enc_tup fn.signature.input input |> List.map B32.to_bytes in
  Bytes.concat Bytes.empty (selector :: args)

let snapshot = calldata Staking.syscall_snapshot_function []
let epoch_change = calldata Staking.syscall_on_epoch_change_function [Staking.Epoch.Epoch U64.one]
let reward = calldata Staking.syscall_reward_function [Address.zero]

let ordinary_transaction =
  sign ~key:(U256.to_repr U256.one) (transaction ~nonce:0 ~value:U256.zero ~data:Bytes.empty)

let reward_cap_case name prefix suffix ~value ~valid =
  Alcotest.test_case name `Quick (fun () ->
      let system_transactions =
        List.mapi
          (fun nonce (data, value) -> sign (transaction ~nonce ~value ~data))
          (List.map (fun data -> (data, U256.zero)) prefix @ [(reward, value)])
      in
      List.iter
        (fun tx ->
          Alcotest.check (Alcotest.option address) "system sender"
            (Some Chain.Monad.system_sender) (Transaction.sender Params.chain_id tx) )
        system_transactions ;
      let block = {Block.empty with transactions = system_transactions @ suffix} in
      let expected =
        if valid then Ok ()
        else Error Execution.Error.(Invalid_block {block; reason = Invalid_reward_value})
      in
      let error = Alcotest.testable (Fmt.of_to_string Execution.Error.to_string) Stdlib.( = ) in
      Alcotest.check (Alcotest.result Alcotest.unit error) "reward cap" expected
        (Validator.validate_monad_block block) )

let () =
  Alcotest.run "System transaction validation"
    [ ( "Reward cap"
      , List.concat_map
          (fun (name, prefix, suffix) ->
            [ reward_cap_case (name ^ ": exactly cap") prefix suffix ~value:Staking.max_block_reward
                ~valid:true
            ; reward_cap_case (name ^ ": above cap") prefix suffix
                ~value:U256.(Staking.max_block_reward + one) ~valid:false ] )
          [ ("only transaction", [], [])
          ; ("first before ordinary transaction", [], [ordinary_transaction])
          ; ("after snapshot", [snapshot], [])
          ; ("after epoch change", [epoch_change], [])
          ; ("after both syscalls", [snapshot; epoch_change], []) ] ) ]
