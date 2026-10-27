open Monad_lib
open Numeric
open Byte_string
open Chain.Ethereum
open State
open Lens.Infix
open Test_utils.Utils

let chain_id = Uint.one
let recipient = Address.of_hex_string "0x2000"
let delegate = Address.of_hex_string "0x3000"
let initial_balance = Chain.Monad.mon_to_wei (U256.of_int 10)
let gas_limit = Uint.of_int 200_000

let sign hash =
  let open Libsecp256k1.External in
  let key =
    Key.read_sk_exn Crypto.context
      (Bigstring.of_string
         B32.(to_bytes ~@"45a915e4d060149eb4365960e6a7a45f334393093061116b197e3240065ff2d8") )
  in
  let signature =
    Sign.sign_recoverable_exn Crypto.context ~sk:key (Bigstring.of_string (B32.to_bytes hash))
  in
  let bytes = Sign.to_bytes Crypto.context signature in
  ( U8.of_int (Char.code bytes.{64})
  , U256.of_repr (B32.init (fun i -> bytes.{i}))
  , U256.of_repr (B32.init (fun i -> bytes.{i + 32})) )

let authorization =
  let hash =
    Crypto.keccak_256
      ( Delegation.magic
      ^ Rlp.(encode (List [U256.to_rlp U256.one; Address.to_rlp delegate; U64.to_rlp U64.zero])) )
  in
  let y_parity, r, s = sign hash in
  Transaction.Authorization.{chain_id = U256.one; address = delegate; nonce = U64.zero; y_parity; r; s}

let transaction =
  let tx : Transaction.set_code_tx =
    { nonce = U64.zero
    ; gas_limit
    ; value = U256.one
    ; r = U256.zero
    ; s = U256.zero
    ; to_ = recipient
    ; data = Bytes.empty
    ; max_fee_per_gas = Uint.one
    ; max_priority_fee_per_gas = Uint.one
    ; access_list = []
    ; authorization_list = [authorization]
    ; chain_id
    ; y_parity = U8.zero }
  in
  let y_parity, r, s = sign (Transaction.signing_hash chain_id (Transaction.SetCode tx)) in
  Transaction.SetCode {tx with y_parity; r; s}

(* The C++ reproducer decodes these same bytes. *)
let encoded_transaction =
  "04f8c10180010183030d409400000000000000000000000000000000000020000180c0f85cf85a019400000000000000000000000000000000000030008080a085fd3f8aaa96b30ca6948aa2ad02b8b360f733cddad2fc791b9debeddb66e1a5a0774116115f9a9e4cfe242480146e744dcb739cf0d1dcb8bb03cac9942aa0cda101a0264d31e45b11e09c53ef76e605b4aa99458321861ff358bca2a6fafadce1ab24a063e37432a701ed3dcbff121852859d1b463b07b00a9fbb6dc78a652af399e8a0"

let test revision =
  Alcotest.test_case "rejected self-authorization currently permits emptying" `Quick (fun () ->
      let module E = Execution.Make (struct
        let revision = revision
        let chain_id = chain_id
        let trace = false
      end) in
      let alice = Address.of_hex_string "0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b" in
      Alcotest.check Alcotest.string "same signed transaction as C++" encoded_transaction
        (Bytes.to_hex_string (Transaction.encode transaction)) ;
      let address = Alcotest.testable (Fmt.of_to_string Address.to_hex_string) Address.equal in
      Alcotest.check (Alcotest.option address) "recover transaction sender" (Some alice)
        (Transaction.sender chain_id transaction) ;
      Alcotest.check (Alcotest.option address) "recover rejected authority" (Some alice)
        (Transaction.Authorization.authority authorization) ;
      let world = WorldState.empty.^(WorldState.account alice |-- Account.balance) <- initial_balance in
      let block =
        { Block.empty with
          header = {Block.Header.empty with number = Uint.of_int 10; gas_limit = Uint.of_int 1_000_000}
        ; transactions = [transaction] }
      in
      let after = Result.get_ok (E.process_transaction (BlockState.make world block) transaction) in
      let receipt = snd (List.hd after.transactions_processed) in
      (* Characterizes issue #72, not the desired behavior: C++ reverts this transfer.
         The sender nonce becomes 1 before authorization nonce 0 is checked. *)
      Alcotest.check Alcotest.bool "OCaml currently succeeds, unlike C++" true receipt.succeeded ;
      Alcotest.check u256 "recipient receives 1 wei" U256.one
        after.world_state.^(WorldState.account recipient).balance ;
      Alcotest.check u256 "sender pays fees and transfers 1 wei"
        U256.(initial_balance - of_uint_exn gas_limit - one)
        after.world_state.^(WorldState.account alice).balance ;
      Alcotest.check
        (Alcotest.testable (Fmt.of_to_string U64.to_string) U64.equal)
        "only transaction nonce consumed" U64.one after.world_state.^(WorldState.account alice).nonce ;
      Alcotest.check
        (Alcotest.testable (Fmt.of_to_string Bytes.to_hex_string) Bytes.equal)
        "rejected authorization leaves code empty" Bytes.empty
        after.world_state.^(WorldState.account alice).code )

let () =
  Alcotest.run "Rejected authorization reserve discrepancy" [("Eight", [test `Eight]); ("Nine", [test `Nine])]
