open Test_utils.Utils
open Monad_lib
open Numeric
open Byte_string
open Opcode
open Alcotest

module Eight = Test_utils.Utils.Make (Monad_eight)
module Nine = Test_utils.Utils.Make (Monad_nine)

let () =
  run "EIP-7939: Count leading zeros (CLZ) opcode"
    [ Nine.test_cases_opcode_1 Clz
        U256.
          [ ( ~@"0x0000000000000000000000000000000000000000000000000000000000000000"
            , ~@"0x0000000000000000000000000000000000000000000000000000000000000100" )
          ; ( ~@"0x8000000000000000000000000000000000000000000000000000000000000000"
            , ~@"0x0000000000000000000000000000000000000000000000000000000000000000" )
          ; ( ~@"0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
            , ~@"0x0000000000000000000000000000000000000000000000000000000000000000" )
          ; ( ~@"0x4000000000000000000000000000000000000000000000000000000000000000"
            , ~@"0x0000000000000000000000000000000000000000000000000000000000000001" )
          ; ( ~@"0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
            , ~@"0x0000000000000000000000000000000000000000000000000000000000000001" )
          ; ( ~@"0x0000000000000000000000000000000000000000000000000000000000000001"
            , ~@"0x00000000000000000000000000000000000000000000000000000000000000ff" ) ]
    ; ( "CLZ undefined on MONAD_EIGHT"
      , [ Alcotest.test_case "0x1e" `Quick (fun () ->
              let msg = Eight.bytecode_to_call_message (Bytes.make 1 (Opcode.to_byte Clz)) in
              let result, _ = Eight.Evm.Vm.execute msg msg.code State.TransactionState.empty in
              expect_result_status Evmc.Result.StatusCode.Undefined_instruction result ) ] ) ]
