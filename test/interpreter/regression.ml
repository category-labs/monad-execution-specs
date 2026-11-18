open Test_utils
open Test_utils.Utils
open Make (Monad_nine)
open Alcotest

open Monad_lib
open Numeric
open Byte_string

let initial_gas = 100_000L
let gas_spent_is (diff : Gas.t) (result : Evmc.Result.t) =
  check' int64 ~expected:(Gas.to_int64 diff)
    ~actual:Int64.(initial_gas - result.gas_left)
    ~msg:"Gas spent is correct"

let () =
  run "Regression tests"
    [ ( "G_newaccount is only paid by CALL"
      , [ test_case "CALLCODE does not pay G_newaccount" `Quick (fun () ->
              let code = Bytes.(~@"6000600060006000600160aa61fffff200") in
              let msg = {(bytecode_to_call_message code) with value = U256.one; gas = initial_gas} in
              ignore
                (test_message
                   ~check_result:
                     (gas_spent_is
                        Gas.((~$7 * very_low) + cold_account_access_cost + call_value - call_stipend) )
                   msg ) )
        ; test_case "CALL does pay G_newaccount" `Quick (fun () ->
              let code = Bytes.(~@"6000600060006000600160aa61fffff100") in
              let msg = {(bytecode_to_call_message code) with value = U256.one; gas = initial_gas} in
              ignore
                (test_message
                   ~check_result:
                     (gas_spent_is
                        Gas.(
                          (~$7 * very_low)
                          + cold_account_access_cost
                          + call_value
                          + new_account_cost
                          - call_stipend ) )
                   msg ) ) ] ) ]
