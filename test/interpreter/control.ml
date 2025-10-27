open Monad_lib
open Monad_lib.Numeric

open Test_utils.Utils
open Alcotest

let test_bytecode_output (name, bytecode, output_stack) =
  test_case name `Quick (fun () -> test_bytecode_pure bytecode ~input_stack:[] ~output_stack)

let test_invalid_jumpdest (name, bytecode) =
  test_case name `Quick (fun () ->
      ignore
        (test_message (bytecode_to_call_message bytecode)
           ~check_result:(expect_result_status Bad_jump_destination) ) )

let test_cases_jump =
  let codes_ok =
    [ ( "Forward jump"
      , Bytes.of_hex_string "6004565f5b6001"
        (*
           0x00 PUSH1 0x04
           0x02 JUMP
           0x03 PUSH0
           0x04 JUMPDEST
           0x05 PUSH1 0x01
         *)
      , U256.[~$1] )
    ; ( "Forward and backwards jump"
      , Bytes.of_hex_string "6001600b565b60036011565b60026005565b"
        (*
           0x00 PUSH1 0x01
           0x02 PUSH1 0x0b
           0x04 JUMP
           0x05 JUMPDEST
           0x06 PUSH1 0x03
           0x08 PUSH1 0x11
           0x0a JUMP
           0x0b JUMPDEST
           0x0c PUSH1 0x02
           0x0e PUSH1 0x05
           0x10 JUMP
           0x11 JUMPDEST
         *)
      , U256.[~$3; ~$2; ~$1] ) ]
  in
  let codes_err = [("Invalid destination", Bytes.of_hex_string "600056" (* PUSH1 0x0; JUMP *))] in
  let test_cases = List.map test_bytecode_output codes_ok @ List.map test_invalid_jumpdest codes_err in
  ("Jump", test_cases)

let test_cases_jumpi =
  let codes_ok =
    [ ( "Jumpi not taken"
      , Bytes.of_hex_string "60006008576001005b600200"
        (*
           0x0 PUSH1 0x00
           0x2 PUSH1 0x08
           0x4 JUMPI
           0x5 PUSH1 0x01
           0x7 STOP
           0x8 JUMPDEST
           0x9 PUSH1 0x02
           0xb STOP
         *)
      , U256.[~$1] )
    ; ( "Jumpi taken"
      , Bytes.of_hex_string "60016008576001005b600200"
        (*
           0x0 PUSH1 0x01
           0x2 PUSH1 0x08
           0x4 JUMPI
           0x5 PUSH1 0x01
           0x7 STOP
           0x8 JUMPDEST
           0x9 PUSH1 0x02
           0xb STOP
         *)
      , U256.[~$2] )
    ; ( "Jumpi to invalid destination not taken"
      , Bytes.of_hex_string "6000600857600100600200"
        (*
           0x0 PUSH1 0x00
           0x2 PUSH1 0x08
           0x4 JUMPI
           0x5 PUSH1 0x01
           0x7 STOP
           0x8 PUSH1 0x02
           0xa STOP
         *)
      , U256.[~$1] ) ]
  in
  let codes_err =
    [ ( "Jumpi to invalid destination taken"
      , Bytes.of_hex_string "6001600857600100600200"
        (*
           0x0 PUSH1 0x01
           0x2 PUSH1 0x08
           0x4 JUMPI
           0x5 PUSH1 0x01
           0x7 STOP
           0x8 PUSH1 0x02
           0xa STOP
         *) ) ]
  in
  let test_cases = List.map test_bytecode_output codes_ok @ List.map test_invalid_jumpdest codes_err in
  ("Jumpi", test_cases)

let test_cases_stop =
  let codes = [("Stop terminates execution", Bytes.of_hex_string "60010060ff", U256.[~$1])] in
  let test_cases = List.map test_bytecode_output codes in
  ("Stop", test_cases)

let () = run "Control flow tests" [test_cases_jump; test_cases_jumpi; test_cases_stop]
