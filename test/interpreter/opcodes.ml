open Monad_lib.Utils
open Monad_lib.Opcode
open Monad_lib.Numeric

open Test_utils
open Test_utils.Utils
open Alcotest

open Lens.Infix

module Address = Monad_lib.Chain.Ethereum.Address

let test_keccak (input : Bytes.t) (output : U256.t) =
  let msg =
    bytecode_to_call_message (Program.keccak (Lit U256.zero) (Lit (U256.of_int (Bytes.length input))))
  in
  let open Evm.Vm in
  ignore
    (test_message
       ~prepare_vm:
         M.(
           update_field
             (Context.machine_state |-- MachineState.memory)
             (Evm.Vm.Memory.write_block_at U256.zero input) )
       ~check_vm_state:(expect_stack [output]) msg )

let test_cases_keccak test_cases =
  ( "Keccak"
  , ListLabels.map test_cases ~f:(fun (input, output) ->
        test_case
          (Format.sprintf "Keccak(%s) -> %s" (Bytes.to_hex_string input) (U256.to_short_hex_string output))
          `Quick
          (fun () -> test_keccak input output) ) )

let () =
  run "Individual opcode tests"
    [ test_cases_opcode_2 Add
        U256.
          [ ((~$1, ~$2), ~$3)
          ; ((~$0, max_t), max_t)
          ; ((~$1, max_t), ~$0)
          ; ((~$0xfffff1, max_t), ~$0xfffff0) ]
    ; test_cases_opcode_2 Mul [U256.((~$2, ~$3), ~$6)]
    ; test_cases_opcode_2 Sub
        U256.
          [ ((~$2, ~$1), ~$1)
          ; ((~$1, ~$2), max_t)
          ; ((~$0, max_t), ~$1)
          ; ((~$1, max_t), ~$2)
          ; ((~$1, ~$1), ~$0) ]
    ; test_cases_opcode_2 Udiv
        U256.
          [ ((~$16, ~$8), ~$2)
          ; ((~$17, ~$8), ~$2)
          ; ((~$23, ~$8), ~$2)
          ; ((~$24, ~$8), ~$3)
          ; ((~$16, ~$7), ~$2)
          ; ((~$20, ~$7), ~$2)
          ; ((~$21, ~$7), ~$3)
          ; ((~$21, ~$0), ~$0) ]
    ; test_cases_opcode_2 Sdiv
        U256.
          [ ((~$16, ~$8), ~$2)
          ; ((~$17, ~$8), ~$2)
          ; ((~$23, ~$8), ~$2)
          ; ((~$24, ~$8), ~$3)
          ; ((of_signed_int (-16), ~$8), of_signed_int (-2))
          ; ((of_signed_int (-17), ~$8), of_signed_int (-2))
          ; ((of_signed_int (-23), ~$8), of_signed_int (-2))
          ; ((of_signed_int (-24), ~$8), of_signed_int (-3))
          ; ((~$16, of_signed_int (-8)), of_signed_int (-2))
          ; ((~$17, of_signed_int (-8)), of_signed_int (-2))
          ; ((~$23, of_signed_int (-8)), of_signed_int (-2))
          ; ((~$24, of_signed_int (-8)), of_signed_int (-3))
          ; ((of_signed_int (-16), of_signed_int (-8)), ~$2)
          ; ((of_signed_int (-17), of_signed_int (-8)), ~$2)
          ; ((of_signed_int (-23), of_signed_int (-8)), ~$2)
          ; ((of_signed_int (-24), of_signed_int (-8)), ~$3)
          ; ((~$21, ~$0), ~$0)
          ; ((of_signed_int (-21), ~$0), ~$0) ]
    ; test_cases_opcode_2 Umod
        U256.
          [ ((~$16, ~$8), ~$0)
          ; ((~$17, ~$8), ~$1)
          ; ((~$23, ~$8), ~$7)
          ; ((~$24, ~$8), ~$0)
          ; ((~$16, ~$7), ~$2)
          ; ((~$17, ~$7), ~$3)
          ; ((~$23, ~$7), ~$2)
          ; ((~$24, ~$7), ~$3)
          ; ((~$10, ~$0), ~$0) ]
    ; test_cases_opcode_2 Smod
        U256.
          [ ((~$16, ~$8), ~$0)
          ; ((~$17, ~$8), ~$1)
          ; ((~$23, ~$8), ~$7)
          ; ((~$24, ~$8), ~$0)
          ; ((of_signed_int (-16), ~$8), ~$0)
          ; ((of_signed_int (-17), ~$8), of_signed_int (-1))
          ; ((of_signed_int (-23), ~$8), of_signed_int (-7))
          ; ((of_signed_int (-24), ~$8), ~$0)
          ; ((~$16, of_signed_int (-8)), ~$0)
          ; ((~$17, of_signed_int (-8)), ~$1)
          ; ((~$23, of_signed_int (-8)), ~$7)
          ; ((~$24, of_signed_int (-8)), ~$0)
          ; ((of_signed_int (-16), of_signed_int (-8)), ~$0)
          ; ((of_signed_int (-17), of_signed_int (-8)), of_signed_int (-1))
          ; ((of_signed_int (-23), of_signed_int (-8)), of_signed_int (-7))
          ; ((of_signed_int (-24), of_signed_int (-8)), ~$0)
          ; ((~$5, ~$0), ~$0)
          ; ((of_signed_int (-5), ~$0), ~$0) ]
    ; test_cases_opcode_3 Addmod
        U256.
          [ ((~$4, ~$5, ~$10), ~$9)
          ; ((~$4, ~$5, ~$9), ~$0)
          ; ((~$4, ~$5, ~$8), ~$1)
          ; ((max_t, ~$1, max_t), ~$1)
          ; ((~$5, ~$5, ~$0), ~$0) ]
    ; test_cases_opcode_3 Mulmod
        U256.
          [ ((~$4, ~$5, ~$21), ~$20)
          ; ((~$4, ~$5, ~$20), ~$0)
          ; ((~$4, ~$5, ~$19), ~$1)
          ; ((max_t, ~$2, max_t), ~$0)
          ; ((~$5, ~$5, ~$0), ~$0) ]
    ; test_cases_opcode_2 Exp
        U256.
          [ ((~$2, ~$2), ~$4)
          ; ((~$2, ~$3), ~$8)
          ; ((~$2, ~$4), ~$16)
          ; ((~$7, ~$2), ~$49)
          ; ( (~@"0x8000000000000000000000000000000000000000000000000000000000000001", max_t)
            , ~@"0x8000000000000000000000000000000000000000000000000000000000000001" )
          ; ((~$1, ~$0), ~$1)
          ; ((~$0, ~$0), ~$1) ]
    ; test_cases_opcode_2 Signextend
        U256.
          [ ((~$0, ~$0), ~$0)
          ; ((~$1, ~$0), ~$0)
          ; ((~$256, ~$0), ~$0)
          ; ((max_t, ~$0), ~$0)
          ; ((~$0, ~$0xff), max_t)
          ; ((~$1, ~$0xff), ~$0xff)
          ; ((~$256, ~$0xff), ~$0xff)
          ; ((max_t, ~$0xff), ~$0xff)
          ; ((~$0, ~$0x87), ~@"0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff87")
          ; ((~$1, ~$0x87), ~$0x87)
          ; ((~$0, ~$0xff10), ~$0x10)
          ; ((~$1, ~$0xff10), ~@"0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff10") ]
    ; test_cases_opcode_2 Lt
        U256.
          [ ((~$0, ~$0), ~$0)
          ; ((~$0, ~$1), ~$1)
          ; ((~$1, ~$0), ~$0)
          ; ((~$0, ~$100), ~$1)
          ; ((~$100, ~$0), ~$0)
          ; ((max_t, ~$0), ~$0)
          ; ((~$0, max_t), ~$1)
          ; ((max_t, I256.(as_unsigned max_t)), ~$0)
          ; ((I256.(as_unsigned max_t), max_t), ~$1) ]
    ; test_cases_opcode_2 Gt
        U256.
          [ ((~$0, ~$0), ~$0)
          ; ((~$0, ~$1), ~$0)
          ; ((~$1, ~$0), ~$1)
          ; ((~$0, ~$100), ~$0)
          ; ((~$100, ~$0), ~$1)
          ; ((max_t, ~$0), ~$1)
          ; ((~$0, max_t), ~$0)
          ; ((max_t, I256.(as_unsigned max_t)), ~$1)
          ; ((I256.(as_unsigned max_t), max_t), ~$0) ]
    ; test_cases_opcode_2 Slt
        U256.
          [ ((~$0, ~$0), ~$0)
          ; ((~$0, ~$1), ~$1)
          ; ((~$1, ~$0), ~$0)
          ; ((~$0, ~$100), ~$1)
          ; ((~$100, ~$0), ~$0)
          ; ((max_t, ~$0), ~$1)
          ; ((~$0, max_t), ~$0)
          ; ((max_t, I256.(as_unsigned max_t)), ~$1)
          ; ((I256.(as_unsigned max_t), max_t), ~$0)
          ; ((of_signed_int (-5), ~$7), ~$1)
          ; ((~$5, of_signed_int (-7)), ~$0) ]
    ; test_cases_opcode_2 Sgt
        U256.
          [ ((~$0, ~$0), ~$0)
          ; ((~$0, ~$1), ~$0)
          ; ((~$1, ~$0), ~$1)
          ; ((~$0, ~$100), ~$0)
          ; ((~$100, ~$0), ~$1)
          ; ((max_t, ~$0), ~$0)
          ; ((~$0, max_t), ~$1)
          ; ((max_t, I256.(as_unsigned max_t)), ~$0)
          ; ((I256.(as_unsigned max_t), max_t), ~$1)
          ; ((of_signed_int (-5), ~$7), ~$0)
          ; ((~$5, of_signed_int (-7)), ~$1) ]
    ; test_cases_opcode_2 Eq
        U256.
          [ ((~$0, ~$0), ~$1)
          ; ((~$0, ~$1), ~$0)
          ; ((~$1, ~$0), ~$0)
          ; ((~$100, ~$100), ~$1)
          ; ((~$100, ~$0), ~$0)
          ; ((max_t, ~$0), ~$0)
          ; ((max_t, max_t), ~$1)
          ; ( ( ~@"0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
              , ~@"0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaabbaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" )
            , ~$0 ) ]
    ; test_cases_opcode_1 Iszero U256.[(~$0, ~$1); (~$1, ~$0); (~$100, ~$0); (max_t, ~$0)]
    ; test_cases_opcode_2 And
        U256.
          [ ((~$0, ~$0), ~$0)
          ; ((~$0, ~$1), ~$0)
          ; ((~$1, ~$0), ~$0)
          ; ((~$1, ~$1), ~$1)
          ; ((~$0x10, ~$0x00), ~$0x00)
          ; ((~$0x00, ~$0x10), ~$0x00)
          ; ((~$0x10, ~$0x10), ~$0x10) ]
    ; test_cases_opcode_2 Or
        U256.
          [ ((~$0, ~$0), ~$0)
          ; ((~$0, ~$1), ~$1)
          ; ((~$1, ~$0), ~$1)
          ; ((~$1, ~$1), ~$1)
          ; ((~$0x10, ~$0x00), ~$0x10)
          ; ((~$0x00, ~$0x10), ~$0x10)
          ; ((~$0x10, ~$0x10), ~$0x10) ]
    ; test_cases_opcode_2 Xor
        U256.
          [ ((~$0, ~$0), ~$0)
          ; ((~$0, ~$1), ~$1)
          ; ((~$1, ~$0), ~$1)
          ; ((~$1, ~$1), ~$0)
          ; ((~$0x10, ~$0x00), ~$0x10)
          ; ((~$0x00, ~$0x10), ~$0x10)
          ; ((~$0x10, ~$0x10), ~$0x00) ]
    ; test_cases_opcode_1 Not
        U256.
          [ (~$0, max_t)
          ; (max_t, ~$0)
          ; (~$1, ~@"0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe")
          ; ( ~@"0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0"
            , ~@"0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f" ) ]
    ; test_cases_opcode_2 Byte
        U256.
          [ ((~$0, ~@"0x00102030405060708090a0b0c0d0e0f0101112131415161718191a1b1c1d1e1f"), ~$0x00)
          ; ((~$1, ~@"0x00102030405060708090a0b0c0d0e0f0101112131415161718191a1b1c1d1e1f"), ~$0x10)
          ; ((~$2, ~@"0x00102030405060708090a0b0c0d0e0f0101112131415161718191a1b1c1d1e1f"), ~$0x20)
          ; ((~$3, ~@"0x00102030405060708090a0b0c0d0e0f0101112131415161718191a1b1c1d1e1f"), ~$0x30)
          ; ((~$4, ~@"0x00102030405060708090a0b0c0d0e0f0101112131415161718191a1b1c1d1e1f"), ~$0x40)
          ; ((~$28, ~@"0x00102030405060708090a0b0c0d0e0f0101112131415161718191a1b1c1d1e1f"), ~$0x1c)
          ; ((~$29, ~@"0x00102030405060708090a0b0c0d0e0f0101112131415161718191a1b1c1d1e1f"), ~$0x1d)
          ; ((~$30, ~@"0x00102030405060708090a0b0c0d0e0f0101112131415161718191a1b1c1d1e1f"), ~$0x1e)
          ; ((~$31, ~@"0x00102030405060708090a0b0c0d0e0f0101112131415161718191a1b1c1d1e1f"), ~$0x1f)
          ; ((~$32, ~@"0x00102030405060708090a0b0c0d0e0f0101112131415161718191a1b1c1d1e1f"), ~$0x00) ]
    ; (* Shifts are tested as part of EIP-145 *)
      test_cases_keccak
        U256.
          [ ( Bytes.of_hex_string "0x00"
            , ~@"0xbc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a" )
          ; ( Bytes.of_hex_string "0xdeadbeef"
            , ~@"0xd4fd4e189132273036449fc9e11198c739161b4c0116a9a2dccdfa1c492006f1" )
          ; (Bytes.make 128 '\xff', ~@"0x9ba516f6d50a9e61e3c197ae0f258483b03d7eb87d3c40becd88fa4a9ebfad0f") ]
    ]
