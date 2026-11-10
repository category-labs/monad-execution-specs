open Alcotest
open Test_utils
open Test_utils.Utils
open Lens.Infix

open Monad_lib
open Monad_lib.Numeric
open Monad_lib.Byte_string

module Evm = Utils.Make (Monad_ten)

let gas_used ?prepare_env (bc : Bytes.t) =
  let msg = Evm.bytecode_to_call_message bc in
  let result, _ = Evm.test_message ?prepare_env msg in
  Gas.(of_uint64 msg.gas - of_uint64 result.gas_left)

let push_gas (w : U256.t) = if U256.(w = zero) then Gas.base else Gas.very_low
let sload_gas k = push_gas k
let sstore_gas k v = Gas.(push_gas k + push_gas v)

let sload k = Program.(sload (Lit k))
let sstore k v = Program.(sstore (Lit k) (Lit v))

let page_base = Gas.page_base_cost
let page_load = Gas.page_load_cost
let page_write = Gas.page_write_cost
let growth = Gas.page_state_growth_cost

let second_page_slot = U256.(~$128)

let access_list_tx keys =
  Chain.Ethereum.Transaction.AccessList
    { nonce = U64.zero
    ; gas_limit = Uint.zero
    ; value = U256.zero
    ; r = U256.zero
    ; s = U256.zero
    ; to_ = Some Chain.Ethereum.Address.zero
    ; data = ""
    ; gas_price = Uint.zero
    ; access_list =
        [ Chain.Ethereum.Transaction.Access.
            {address = Chain.Ethereum.Address.zero; storage_keys = List.map U256.to_repr keys} ]
    ; chain_id = Monad_ten.chain_id
    ; y_parity = U8.zero }

let declaring keys (state : State.TransactionState.t) =
  State.TransactionState.initialize_access_sets `Ten (access_list_tx keys) state
    Chain.Ethereum.Address.Set.empty

let warmed_by_access_list keys =
  let state = declaring keys State.TransactionState.empty in
  State.TransactionState.StorageKey.Set.cardinal state.accessed_keys

let check_gas name expected actual = check string name (Gas.to_string expected) (Gas.to_string actual)

let case name expected program = test_case name `Quick (fun () -> check_gas name expected (gas_used program))

(* StorageOriginalNonEmpty in monad/test/vm/unit/runtime/storage_tests.cpp. *)
let case_with_storage name slots expected program =
  test_case name `Quick (fun () ->
      check_gas name expected (gas_used ~prepare_env:(Evm.with_storage slots) program) )

let () =
  run "MIP-8 storage gas"
    [ ( "SLOAD"
      , [ case "cold page pays load cost" Gas.(sload_gas U256.zero + page_base + page_load) (sload U256.zero)
        ; case "new slots in warm page don't pay load"
            Gas.(sload_gas U256.zero + page_base + page_load + sload_gas U256.one + page_base)
            (sload U256.zero ^ sload U256.one)
        ; case "new page is cold again"
            Gas.(
              sload_gas U256.(~$127)
              + page_base
              + page_load
              + sload_gas second_page_slot
              + page_base
              + page_load )
            (sload U256.(~$127) ^ sload second_page_slot) ] )
    ; ( "SSTORE"
      , [ case "creating a slot in a cold page"
            Gas.(sstore_gas U256.zero U256.one + page_base + page_load + page_write + growth)
            (sstore U256.zero U256.one)
        ; case "second slot in the page does not charge load or write"
            Gas.(
              sstore_gas U256.zero U256.one
              + page_base
              + page_load
              + page_write
              + growth
              + sstore_gas U256.one U256.one
              + page_base
              + growth )
            (sstore U256.zero U256.one ^ sstore U256.one U256.one)
        ; case "state growth is counted per slot"
            Gas.(
              sstore_gas U256.zero U256.one
              + page_base
              + page_load
              + page_write
              + growth
              + sstore_gas U256.one U256.one
              + page_base
              + growth
              + sstore_gas U256.(~$2) U256.one
              + page_base
              + growth )
            (sstore U256.zero U256.one ^ sstore U256.one U256.one ^ sstore U256.(~$2) U256.one)
        ; case "rewriting the same value charges base"
            Gas.(
              sstore_gas U256.zero U256.one
              + page_base
              + page_load
              + page_write
              + growth
              + sstore_gas U256.zero U256.one
              + page_base )
            (sstore U256.zero U256.one ^ sstore U256.zero U256.one)
        ; case "clearing a slot charges base"
            Gas.(
              sstore_gas U256.zero U256.one
              + page_base
              + page_load
              + page_write
              + growth
              + sstore_gas U256.zero U256.zero
              + page_base )
            (sstore U256.zero U256.one ^ sstore U256.zero U256.zero)
        ; case "restoring a cleared slot does not charge growth"
            Gas.(
              sstore_gas U256.zero U256.one
              + page_base
              + page_load
              + page_write
              + growth
              + sstore_gas U256.zero U256.zero
              + page_base
              + sstore_gas U256.one U256.one
              + page_base )
            (sstore U256.zero U256.one ^ sstore U256.zero U256.zero ^ sstore U256.one U256.one)
        ; case "different pages have their own costs"
            Gas.(
              sstore_gas U256.zero U256.one
              + page_base
              + page_load
              + page_write
              + growth
              + sstore_gas second_page_slot U256.one
              + page_base
              + page_load
              + page_write
              + growth )
            (sstore U256.zero U256.one ^ sstore second_page_slot U256.one)
        ; case "SLOAD already paid load cost"
            Gas.(
              sload_gas U256.zero
              + page_base
              + page_load
              + sstore_gas U256.zero U256.one
              + page_base
              + page_write
              + growth )
            (sload U256.zero ^ sstore U256.zero U256.one)
        ; case_with_storage "writing same value does not charge write"
            [(U256.zero, U256.one)]
            Gas.(sstore_gas U256.zero U256.one + page_base + page_load)
            (sstore U256.zero U256.one)
        ; case_with_storage "changing value does not charge growth"
            [(U256.zero, U256.one)]
            Gas.(sstore_gas U256.zero U256.(~$2) + page_base + page_load + page_write)
            (sstore U256.zero U256.(~$2))
        ; case_with_storage "clearing slot does not charge growth"
            [(U256.zero, U256.one)]
            Gas.(sstore_gas U256.zero U256.zero + page_base + page_load + page_write)
            (sstore U256.zero U256.zero)
        ; case_with_storage "changing value twice charges write once"
            [(U256.zero, U256.one)]
            Gas.(
              sstore_gas U256.zero U256.(~$2)
              + page_base
              + page_load
              + page_write
              + sstore_gas U256.zero U256.(~$3)
              + page_base )
            (sstore U256.zero U256.(~$2) ^ sstore U256.zero U256.(~$3))
        ; case_with_storage "restoring a cleared slot charges write once"
            [(U256.zero, U256.one)]
            Gas.(
              sstore_gas U256.zero U256.zero
              + page_base
              + page_load
              + page_write
              + sstore_gas U256.zero U256.one
              + page_base )
            (sstore U256.zero U256.zero ^ sstore U256.zero U256.one) ] )
    ; ( "Storage refunds"
      , [ test_case "no refund for clearing a slot" `Quick (fun () ->
              let program = sstore U256.zero U256.one ^ sstore U256.zero U256.zero in
              let result, _ = Evm.test_message (Evm.bytecode_to_call_message program) in
              check int64 "gas refund" 0L result.gas_refund ) ] )
    ; ( "EIP-2930 access lists"
      , [ test_case "declared keys sharing a page are warmed once" `Quick (fun () ->
              check' int ~msg:"three keys of one page warm one entry" ~expected:1
                ~actual:(warmed_by_access_list U256.[~$0; ~$1; ~$127]) )
        ; test_case "declared keys in different pages are warmed separately" `Quick (fun () ->
              check' int ~msg:"keys of two pages warm two entries" ~expected:2
                ~actual:(warmed_by_access_list U256.[~$0; second_page_slot]) )
        ; test_case "declared key warms the rest of its page" `Quick (fun () ->
              check_gas "SLOAD of an undeclared slot on a declared page is warm"
                Gas.(sload_gas U256.(~$5) + page_base)
                (gas_used ~prepare_env:(declaring [U256.zero]) (sload U256.(~$5))) )
        ; test_case "declared key has no load cost for store" `Quick (fun () ->
              check_gas "SSTORE to the declared slot"
                Gas.(sstore_gas U256.zero U256.one + page_base + page_write + growth)
                (gas_used ~prepare_env:(declaring [U256.zero]) (sstore U256.zero U256.one)) ;
              check_gas "SSTORE to an undeclared slot on the declared page"
                Gas.(sstore_gas U256.(~$5) U256.one + page_base + page_write + growth)
                (gas_used ~prepare_env:(declaring [U256.zero]) (sstore U256.(~$5) U256.one)) ) ] )
    ; ( "Reverted calls"
      , let callee = Chain.Ethereum.Address.of_hex_string "0x00000000000000000000000000000000000000ca" in
        let call_message code =
          { (Evm.bytecode_to_call_message code) with
            Evmc.Message.recipient = callee
          ; code_address = callee
          ; value = U256.zero }
        in
        let deploy code (state : State.TransactionState.t) =
          let open State in
          state.^$(TransactionState.account ~keep_empty:true callee |-- Chain.Ethereum.Account.TLens.code) <-
            (fun _ -> code)
        in
        let run code =
          let state = deploy code State.TransactionState.empty in
          Evm.Evm.Host.call (call_message code) state
        in
        let revert = Program.(push U256.zero ^ push U256.zero ^ to_bytecode [Revert]) in
        [ test_case "a successful call records the page it wrote to" `Quick (fun () ->
              let result, state = run (sstore U256.zero U256.one) in
              check status_code "call succeeded" Success result.status_code ;
              check' bool ~msg:"written page was recorded" ~expected:false
                ~actual:(State.TransactionState.StorageKey.Set.is_empty state.written_pages) ;
              check' bool ~msg:"page accrued state growth" ~expected:false
                ~actual:(State.TransactionState.StorageKey.Map.is_empty state.page_growth) )
        ; test_case "a reverted call rolls back the page write set and growth counters" `Quick (fun () ->
              let result, state = run (sstore U256.zero U256.one ^ revert) in
              check status_code "call reverted" Revert result.status_code ;
              check' bool ~msg:"page write set is empty" ~expected:true
                ~actual:(State.TransactionState.StorageKey.Set.is_empty state.written_pages) ;
              check' bool ~msg:"growth counters are empty" ~expected:true
                ~actual:(State.TransactionState.StorageKey.Map.is_empty state.page_growth) ;
              check' bool ~msg:"accessed page set is empty" ~expected:true
                ~actual:(State.TransactionState.StorageKey.Set.is_empty state.accessed_keys) ) ] ) ]
