open Test_utils.Utils
open Make (Monad_nine)
open Monad_lib
open Monad_lib.Numeric
open Opcode
open Alcotest

let () =
  run "EIP-145: Bitwise shifting instructions in EVM"
    [ test_cases_opcode_2 Shl
        U256.
          [ ((~@"0x0", ~@"0x1"), ~@"0x1")
          ; ((~@"0x1", ~@"0x1"), ~@"0x2")
          ; ((~@"0xff", ~@"0x1"), ~@"0x8000000000000000000000000000000000000000000000000000000000000000")
          ; ((~@"0x100", ~@"0x1"), ~@"0x0")
          ; ((~@"0x0101", ~@"0x1"), ~@"0x0")
          ; ( (~@"0x1", ~@"0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff")
            , ~@"0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe" )
          ; ( (~@"0xff", ~@"0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff")
            , ~@"0x8000000000000000000000000000000000000000000000000000000000000000" )
          ; ((~@"0x100", ~@"0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"), ~@"0x0")
          ; ((~@"0x1", ~@"0x0"), ~@"0x0")
          ; ( (~@"0x1", ~@"0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff")
            , ~@"0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe" ) ]
    ; test_cases_opcode_2 Shr
        U256.
          [ ((~@"0x0", ~@"0x1"), ~@"0x1")
          ; ((~@"0x1", ~@"0x1"), ~@"0x0")
          ; ( (~@"0x1", ~@"0x8000000000000000000000000000000000000000000000000000000000000000")
            , ~@"0x4000000000000000000000000000000000000000000000000000000000000000" )
          ; ((~@"0xff", ~@"0x8000000000000000000000000000000000000000000000000000000000000000"), ~@"0x1")
          ; ((~@"0x100", ~@"0x8000000000000000000000000000000000000000000000000000000000000000"), ~@"0x0")
          ; ((~@"0x101", ~@"0x8000000000000000000000000000000000000000000000000000000000000000"), ~@"0x0")
          ; ( (~@"0x0", ~@"0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff")
            , ~@"0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" )
          ; ( (~@"0x1", ~@"0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff")
            , ~@"0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" )
          ; ((~@"0xff", ~@"0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"), ~@"0x1")
          ; ((~@"0x100", ~@"0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"), ~@"0x0")
          ; ((~@"0x1", ~@"0x0"), ~@"0x0") ]
    ; test_cases_opcode_2 Sar
        U256.
          [ ((~@"0x0", ~@"0x1"), ~@"0x1")
          ; ((~@"0x1", ~@"0x1"), ~@"0x0")
          ; ( (~@"0x1", ~@"0x8000000000000000000000000000000000000000000000000000000000000000")
            , ~@"0xc000000000000000000000000000000000000000000000000000000000000000" )
          ; ( (~@"0xff", ~@"0x8000000000000000000000000000000000000000000000000000000000000000")
            , ~@"0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" )
          ; ( (~@"0x100", ~@"0x8000000000000000000000000000000000000000000000000000000000000000")
            , ~@"0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" )
          ; ( (~@"0x101", ~@"0x8000000000000000000000000000000000000000000000000000000000000000")
            , ~@"0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" )
          ; ( (~@"0x0", ~@"0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff")
            , ~@"0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" )
          ; ( (~@"0x1", ~@"0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff")
            , ~@"0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" )
          ; ( (~@"0xff", ~@"0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff")
            , ~@"0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" )
          ; ( (~@"0x100", ~@"0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff")
            , ~@"0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" )
          ; ((~@"0x1", ~@"0x0"), ~@"0x0")
          ; ((~@"0xfe", ~@"0x4000000000000000000000000000000000000000000000000000000000000000"), ~@"0x1")
          ; ((~@"0xf8", ~@"0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"), ~@"0x7f")
          ; ((~@"0xfe", ~@"0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"), ~@"0x1")
          ; ((~@"0xff", ~@"0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"), ~@"0x0")
          ; ((~@"0x100", ~@"0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"), ~@"0x0") ]
    ]
