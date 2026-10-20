open Monad_lib
open Monad_lib.Byte_string
open Monad_lib.Numeric
open Monad_lib.Chain.Ethereum
open Test_utils.Utils

(* Native structural equality is intentionally retained here as the regression
   oracle, not as an implementation dependency of the library. *)
let check_pairs eq values =
  List.iter
    (fun x -> List.iter (fun y -> Alcotest.(check bool "matches native equality" (x = y) (eq x y))) values)
    values

(* Change each serialized field independently. This catches omitted fields in
   an explicit equality function, including fields added to records later. *)
let check_fields to_json of_json eq x y =
  let x_fields = Yojson.Safe.Util.to_assoc (to_json x) in
  let y_fields = Yojson.Safe.Util.to_assoc (to_json y) in
  let copy = expect_ok (of_json (to_json x)) in
  Alcotest.(check bool "separately allocated copy" true (eq x copy)) ;
  List.iter
    (fun (key, value) ->
      let fields = List.map (fun (k, v) -> (k, if String.equal key k then value else v)) x_fields in
      let changed = expect_ok (of_json (`Assoc fields)) in
      Alcotest.(check bool (key ^ ": fixture changes field") false (x = changed)) ;
      check_pairs eq [x; copy; changed] )
    (List.filter (fun (key, _) -> not (String.equal key "type")) y_fields)

let bytes seed = if Int.equal seed 0 then "" else "\x00\xff"
let address seed = Address.make (Char.chr seed)
let b32 seed = B32.make (Char.chr seed)

let access seed : Transaction.Access.t =
  {address = address seed; storage_keys = (if Int.equal seed 0 then [] else [b32 seed])}

let authorization seed : Transaction.Authorization.t =
  { chain_id = U256.of_int seed
  ; address = address seed
  ; nonce = U64.of_int seed
  ; y_parity = U8.of_int seed
  ; r = U256.of_int seed
  ; s = U256.of_int seed }

let transaction seed kind =
  let open Transaction in
  let nonce = U64.of_int seed in
  let gas_limit = Uint.of_int seed in
  let value = U256.of_int seed in
  let r = value and s = value in
  let to_ = if Int.equal seed 0 then None else Some (address seed) in
  let data = bytes seed in
  let gas_price = gas_limit in
  let access_list = if Int.equal seed 0 then [] else [access seed] in
  let chain_id = gas_limit in
  let y_parity = U8.of_int seed in
  let max_fee_per_gas = gas_limit and max_priority_fee_per_gas = gas_limit in
  match kind with
  | `Legacy -> Legacy {nonce; gas_limit; value; r; s; to_; data; gas_price; v = value}
  | `AccessList ->
      AccessList {nonce; gas_limit; value; r; s; to_; data; gas_price; access_list; chain_id; y_parity}
  | `FeeMarket ->
      FeeMarket
        { nonce
        ; gas_limit
        ; value
        ; r
        ; s
        ; to_
        ; data
        ; max_fee_per_gas
        ; max_priority_fee_per_gas
        ; access_list
        ; chain_id
        ; y_parity }
  | `SetCode ->
      let authorization_list = if Int.equal seed 0 then [] else [authorization seed] in
      SetCode
        { nonce
        ; gas_limit
        ; value
        ; r
        ; s
        ; to_ = address seed
        ; data
        ; max_fee_per_gas
        ; max_priority_fee_per_gas
        ; access_list
        ; authorization_list
        ; chain_id
        ; y_parity }

let kinds = [`Legacy; `AccessList; `FeeMarket; `SetCode]

let header seed : Block.Header.t =
  { parent_hash = b32 seed
  ; ommers_hash = b32 seed
  ; beneficiary = address seed
  ; state_root = b32 seed
  ; transactions_root = b32 seed
  ; receipts_root = b32 seed
  ; logs_bloom = Bloom.make (Char.chr seed)
  ; difficulty = Uint.of_int seed
  ; number = Uint.of_int seed
  ; gas_limit = Uint.of_int seed
  ; gas_used = Uint.of_int seed
  ; timestamp = U256.of_int seed
  ; extra_data = bytes seed
  ; prev_randao = b32 seed
  ; nonce = B8.make (Char.chr seed)
  ; base_fee_per_gas = Uint.of_int seed
  ; withdrawals_root = b32 seed
  ; blob_gas_used = U64.of_int seed
  ; excess_blob_gas = U64.of_int seed
  ; parent_beacon_block_root = b32 seed
  ; requests_hash = b32 seed }

let withdrawal seed : Withdrawal.t =
  { global_index = U64.of_int seed
  ; validator_index = U64.of_int seed
  ; recipient = address seed
  ; amount = U64.of_int seed }

let block seed : Block.t =
  { header = header seed
  ; transactions = (if Int.equal seed 0 then [] else List.map (transaction seed) kinds)
  ; ommers = (if Int.equal seed 0 then [] else [header seed])
  ; withdrawals = (if Int.equal seed 0 then [] else [withdrawal seed]) }

let test_records () =
  check_fields Transaction.Access.to_yojson Transaction.Access.of_yojson Transaction.Access.equal (access 0)
    (access 1) ;
  check_fields Transaction.Authorization.to_yojson Transaction.Authorization.of_yojson
    Transaction.Authorization.equal (authorization 0) (authorization 1) ;
  List.iter
    (fun kind ->
      check_fields Transaction.to_yojson Transaction.of_yojson Transaction.equal (transaction 0 kind)
        (transaction 1 kind) )
    kinds ;
  check_pairs Transaction.equal (List.concat_map (fun seed -> List.map (transaction seed) kinds) [0; 1]) ;
  check_fields Block.Header.to_yojson Block.Header.of_yojson Block.Header.equal (header 0) (header 1) ;
  check_fields Withdrawal.to_yojson Withdrawal.of_yojson Withdrawal.equal (withdrawal 0) (withdrawal 1) ;
  check_fields Block.to_yojson Block.of_yojson Block.equal (block 0) (block 1)

let test_variants () =
  let open Evmc.Result.StatusCode in
  check_pairs equal
    [ Success
    ; Failure
    ; Revert
    ; Out_of_gas
    ; Invalid_instruction
    ; Undefined_instruction
    ; Stack_overflow
    ; Stack_underflow
    ; Bad_jump_destination
    ; Invalid_memory_access
    ; Call_depth_exceeded
    ; Static_mode_violation
    ; Precompile_failure
    ; Contract_validation_failure
    ; Argument_out_of_range
    ; Wasm_unreachable_instruction
    ; Wasm_trap
    ; Insufficient_balance
    ; Monad_reserve_balance_violation
    ; Internal_error
    ; Rejected
    ; Out_of_memory
    ; Create_from_delegated_eoa ] ;
  Evmc.Message.CallKind.(check_pairs equal [Call; DelegateCall; CallCode; Create; Create2]) ;
  Chain.Monad.Revision.(check_pairs equal all_revisions) ;
  let open Fixtures.BlockchainTest in
  let revisions = Chain.Monad.Revision.all_revisions in
  let transitions =
    List.concat_map
      (fun pre ->
        List.concat_map
          (fun post -> List.map (fun timestamp -> Transition {pre; post; timestamp}) [U256.zero; U256.one])
          revisions )
      revisions
  in
  check_pairs equal_revision ((Invalid :: List.map (fun rev -> Single rev) revisions) @ transitions)

let test_nested () =
  let x = block 1 in
  let access_change = Transaction.Access.{(access 1) with storage_keys = [b32 2]} in
  let auth_change = Transaction.Authorization.{(authorization 1) with nonce = U64.of_int 2} in
  let tx = match transaction 1 `SetCode with SetCode tx -> tx | _ -> assert false in
  check_pairs Block.equal
    [ x
    ; {x with transactions = [SetCode {tx with access_list = [access_change]}]}
    ; {x with transactions = [SetCode {tx with authorization_list = [auth_change]}]}
    ; {x with transactions = List.rev x.transactions}
    ; {x with ommers = [{(header 1) with number = Uint.of_int 2}]}
    ; {x with withdrawals = [{(withdrawal 1) with amount = U64.of_int 2}]} ] ;
  check_pairs Transaction.equal
    [ SetCode tx
    ; SetCode {tx with access_list = [access_change]}
    ; SetCode {tx with authorization_list = [auth_change]} ] ;
  Rlp.(check_pairs equal [Bytes ""; Bytes "\x00"; List []; List [Bytes ""]; List [List []]]) ;
  let open Ec.Secp256r1 in
  Alcotest.(check bool "curve infinity" true (G_1.is_zero G_1.zero)) ;
  Alcotest.(check bool "curve generator" false (G_1.is_zero G_1.generator))

let () =
  let unsigned = QCheck2.Gen.(frequency [(1, map U256.of_int (int_range 0 100)); (4, u256)]) in
  let signed = QCheck2.Gen.(frequency [(1, map I256.of_int (int_range (-100) 100)); (4, i256)]) in
  let same_order compare (x, y) =
    Int.equal (Int.compare (compare x y) 0) (Int.compare (Stdlib.compare x y) 0)
  in
  Alcotest.run "Explicit equality"
    [ ( "Regression"
      , Alcotest.
          [ test_case "record fields" `Quick test_records
          ; test_case "variant pairs" `Quick test_variants
          ; test_case "nested values" `Quick test_nested ] )
    ; ( "RLP"
      , [ check_prop ~name:"equality agrees with native OCaml"
            QCheck2.Gen.(pair (rlp ~nonempty:false) (rlp ~nonempty:false))
            (fun (x, y) -> Rlp.equal x (Rlp.decode (Rlp.encode x)) && Bool.equal (Rlp.equal x y) (x = y)) ] )
    ; ( "Numeric ordering"
      , [ check_prop ~name:"unsigned ordering agrees with native OCaml"
            QCheck2.Gen.(pair unsigned unsigned)
            (same_order U256.compare)
        ; check_prop ~name:"signed ordering agrees with native OCaml"
            QCheck2.Gen.(pair signed signed)
            (same_order I256.compare) ] ) ]
