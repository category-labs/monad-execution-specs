open Monad_lib.Utils
open Monad_lib.Opcode

open Test_utils
open Test_utils.Utils
open Alcotest

open Lens.Infix

module Address = Monad_lib.Chain.Ethereum.Address

let test_keccak (input : Bytes.t) (output : Word.t) =
  let msg =
    bytecode_to_call_message (Program.keccak (Lit Word.zero) (Lit (Word.of_int (Bytes.length input))))
  in
  let open Vm in
  ignore
    (test_message
       ~prepare_vm:
         Vm.M.(
           update_field
             (Context.machine_state |-- MachineState.memory)
             (Vm.Memory.write_block_at Word.zero input) )
       ~check_vm_state:(expect_stack [output]) msg )

let test_cases_keccak test_cases =
  ( "Keccak"
  , ListLabels.map test_cases ~f:(fun (input, output) ->
        test_case
          (Format.sprintf "Keccak(0x%s) -> 0x%s" (Bytes.to_hex_string input) (Word.to_short_hex_string output))
          `Quick
          (fun () -> test_keccak input output) ) )

let () =
  run "Individual opcode tests"
    [ test_cases_opcode_2 Add
        Word.
          [ ((~$1, ~$2), ~$3)
          ; ((~$0, max_unsigned_t), max_unsigned_t)
          ; ((~$1, max_unsigned_t), ~$0)
          ; ((~$0xfffff1, max_unsigned_t), ~$0xfffff0) ]
    ; test_cases_opcode_2 Mul [Word.((~$2, ~$3), ~$6)]
    ; test_cases_opcode_2 Sub
        Word.
          [ ((~$2, ~$1), ~$1)
          ; ((~$1, ~$2), max_unsigned_t)
          ; ((~$0, max_unsigned_t), ~$1)
          ; ((~$1, max_unsigned_t), ~$2)
          ; ((~$1, ~$1), ~$0) ]
    ; test_cases_opcode_2 Udiv
        Word.
          [ ((~$16, ~$8), ~$2)
          ; ((~$17, ~$8), ~$2)
          ; ((~$23, ~$8), ~$2)
          ; ((~$24, ~$8), ~$3)
          ; ((~$16, ~$7), ~$2)
          ; ((~$20, ~$7), ~$2)
          ; ((~$21, ~$7), ~$3)
          ; ((~$21, ~$0), ~$0) ]
    ; test_cases_opcode_2 Sdiv
        Word.
          [ ((~$16, ~$8), ~$2)
          ; ((~$17, ~$8), ~$2)
          ; ((~$23, ~$8), ~$2)
          ; ((~$24, ~$8), ~$3)
          ; ((~$(-16), ~$8), ~$(-2))
          ; ((~$(-17), ~$8), ~$(-2))
          ; ((~$(-23), ~$8), ~$(-2))
          ; ((~$(-24), ~$8), ~$(-3))
          ; ((~$16, ~$(-8)), ~$(-2))
          ; ((~$17, ~$(-8)), ~$(-2))
          ; ((~$23, ~$(-8)), ~$(-2))
          ; ((~$24, ~$(-8)), ~$(-3))
          ; ((~$(-16), ~$(-8)), ~$2)
          ; ((~$(-17), ~$(-8)), ~$2)
          ; ((~$(-23), ~$(-8)), ~$2)
          ; ((~$(-24), ~$(-8)), ~$3)
          ; ((~$21, ~$0), ~$0)
          ; ((~$(-21), ~$0), ~$0) ]
    ; test_cases_opcode_2 Umod
        Word.
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
        Word.
          [ ((~$16, ~$8), ~$0)
          ; ((~$17, ~$8), ~$1)
          ; ((~$23, ~$8), ~$7)
          ; ((~$24, ~$8), ~$0)
          ; ((~$(-16), ~$8), ~$0)
          ; ((~$(-17), ~$8), ~$(-1))
          ; ((~$(-23), ~$8), ~$(-7))
          ; ((~$(-24), ~$8), ~$0)
          ; ((~$16, ~$(-8)), ~$0)
          ; ((~$17, ~$(-8)), ~$1)
          ; ((~$23, ~$(-8)), ~$7)
          ; ((~$24, ~$(-8)), ~$0)
          ; ((~$(-16), ~$(-8)), ~$0)
          ; ((~$(-17), ~$(-8)), ~$(-1))
          ; ((~$(-23), ~$(-8)), ~$(-7))
          ; ((~$(-24), ~$(-8)), ~$0)
          ; ((~$5, ~$0), ~$0)
          ; ((~$(-5), ~$0), ~$0) ]
    ; test_cases_opcode_3 Addmod
        Word.
          [ ((~$4, ~$5, ~$10), ~$9)
          ; ((~$4, ~$5, ~$9), ~$0)
          ; ((~$4, ~$5, ~$8), ~$1)
          ; ((max_unsigned_t, ~$1, max_unsigned_t), ~$1)
          ; ((~$5, ~$5, ~$0), ~$0) ]
    ; test_cases_opcode_3 Mulmod
        Word.
          [ ((~$4, ~$5, ~$21), ~$20)
          ; ((~$4, ~$5, ~$20), ~$0)
          ; ((~$4, ~$5, ~$19), ~$1)
          ; ((max_unsigned_t, ~$2, max_unsigned_t), ~$0)
          ; ((~$5, ~$5, ~$0), ~$0) ]
    ; test_cases_opcode_2 Exp
        Word.
          [ ((~$2, ~$2), ~$4)
          ; ((~$2, ~$3), ~$8)
          ; ((~$2, ~$4), ~$16)
          ; ((~$7, ~$2), ~$49)
          ; ( (~@"0x8000000000000000000000000000000000000000000000000000000000000001", max_unsigned_t)
            , ~@"0x8000000000000000000000000000000000000000000000000000000000000001" )
          ; ((~$1, ~$0), ~$1)
          ; ((~$0, ~$0), ~$1) ]
    ; test_cases_opcode_2 Signextend
        Word.
          [ ((~$0, ~$0), ~$0)
          ; ((~$1, ~$0), ~$0)
          ; ((~$256, ~$0), ~$0)
          ; ((max_unsigned_t, ~$0), ~$0)
          ; ((~$0, ~$0xff), max_unsigned_t)
          ; ((~$1, ~$0xff), ~$0xff)
          ; ((~$256, ~$0xff), ~$0xff)
          ; ((max_unsigned_t, ~$0xff), ~$0xff)
          ; ((~$0, ~$0x87), ~@"0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff87")
          ; ((~$1, ~$0x87), ~$0x87)
          ; ((~$0, ~$0xff10), ~$0x10)
          ; ((~$1, ~$0xff10), ~@"0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff10") ]
    ; test_cases_opcode_2 Lt
        Word.
          [ ((~$0, ~$0), ~$0)
          ; ((~$0, ~$1), ~$1)
          ; ((~$1, ~$0), ~$0)
          ; ((~$0, ~$100), ~$1)
          ; ((~$100, ~$0), ~$0)
          ; ((max_unsigned_t, ~$0), ~$0)
          ; ((~$0, max_unsigned_t), ~$1)
          ; ((max_unsigned_t, max_signed_t), ~$0)
          ; ((max_signed_t, max_unsigned_t), ~$1) ]
    ; test_cases_opcode_2 Gt
        Word.
          [ ((~$0, ~$0), ~$0)
          ; ((~$0, ~$1), ~$0)
          ; ((~$1, ~$0), ~$1)
          ; ((~$0, ~$100), ~$0)
          ; ((~$100, ~$0), ~$1)
          ; ((max_unsigned_t, ~$0), ~$1)
          ; ((~$0, max_unsigned_t), ~$0)
          ; ((max_unsigned_t, max_signed_t), ~$1)
          ; ((max_signed_t, max_unsigned_t), ~$0) ]
    ; test_cases_opcode_2 Slt
        Word.
          [ ((~$0, ~$0), ~$0)
          ; ((~$0, ~$1), ~$1)
          ; ((~$1, ~$0), ~$0)
          ; ((~$0, ~$100), ~$1)
          ; ((~$100, ~$0), ~$0)
          ; ((max_unsigned_t, ~$0), ~$1)
          ; ((~$0, max_unsigned_t), ~$0)
          ; ((max_unsigned_t, max_signed_t), ~$1)
          ; ((max_signed_t, max_unsigned_t), ~$0)
          ; ((~$(-5), ~$7), ~$1)
          ; ((~$5, ~$(-7)), ~$0) ]
    ; test_cases_opcode_2 Sgt
        Word.
          [ ((~$0, ~$0), ~$0)
          ; ((~$0, ~$1), ~$0)
          ; ((~$1, ~$0), ~$1)
          ; ((~$0, ~$100), ~$0)
          ; ((~$100, ~$0), ~$1)
          ; ((max_unsigned_t, ~$0), ~$0)
          ; ((~$0, max_unsigned_t), ~$1)
          ; ((max_unsigned_t, max_signed_t), ~$0)
          ; ((max_signed_t, max_unsigned_t), ~$1)
          ; ((~$(-5), ~$7), ~$0)
          ; ((~$5, ~$(-7)), ~$1) ]
    ; test_cases_opcode_2 Eq
        Word.
          [ ((~$0, ~$0), ~$1)
          ; ((~$0, ~$1), ~$0)
          ; ((~$1, ~$0), ~$0)
          ; ((~$100, ~$100), ~$1)
          ; ((~$100, ~$0), ~$0)
          ; ((max_unsigned_t, ~$0), ~$0)
          ; ((max_unsigned_t, max_unsigned_t), ~$1)
          ; ( ( ~@"0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
              , ~@"0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaabbaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" )
            , ~$0 ) ]
    ; test_cases_opcode_1 Iszero Word.[(~$0, ~$1); (~$1, ~$0); (~$100, ~$0); (max_unsigned_t, ~$0)]
    ; test_cases_opcode_2 And
        Word.
          [ ((~$0, ~$0), ~$0)
          ; ((~$0, ~$1), ~$0)
          ; ((~$1, ~$0), ~$0)
          ; ((~$1, ~$1), ~$1)
          ; ((~$0x10, ~$0x00), ~$0x00)
          ; ((~$0x00, ~$0x10), ~$0x00)
          ; ((~$0x10, ~$0x10), ~$0x10) ]
    ; test_cases_opcode_2 Or
        Word.
          [ ((~$0, ~$0), ~$0)
          ; ((~$0, ~$1), ~$1)
          ; ((~$1, ~$0), ~$1)
          ; ((~$1, ~$1), ~$1)
          ; ((~$0x10, ~$0x00), ~$0x10)
          ; ((~$0x00, ~$0x10), ~$0x10)
          ; ((~$0x10, ~$0x10), ~$0x10) ]
    ; test_cases_opcode_2 Xor
        Word.
          [ ((~$0, ~$0), ~$0)
          ; ((~$0, ~$1), ~$1)
          ; ((~$1, ~$0), ~$1)
          ; ((~$1, ~$1), ~$0)
          ; ((~$0x10, ~$0x00), ~$0x10)
          ; ((~$0x00, ~$0x10), ~$0x10)
          ; ((~$0x10, ~$0x10), ~$0x00) ]
    ; test_cases_opcode_1 Not
        Word.
          [ (~$0, max_unsigned_t)
          ; (max_unsigned_t, ~$0)
          ; (~$1, ~@"0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe")
          ; ( ~@"0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0"
            , ~@"0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f" ) ]
    ; test_cases_opcode_2 Byte
        Word.
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
        Word.
          [ ( Bytes.of_hex_string "0x00"
            , ~@"0xbc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a" )
          ; ( Bytes.of_hex_string "0xdeadbeef"
            , ~@"0xd4fd4e189132273036449fc9e11198c739161b4c0116a9a2dccdfa1c492006f1" )
          ; (Bytes.make 128 '\xff', ~@"0x9ba516f6d50a9e61e3c197ae0f258483b03d7eb87d3c40becd88fa4a9ebfad0f") ]
    ]
