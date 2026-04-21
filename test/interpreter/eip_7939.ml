open Test_utils.Utils
open Monad_lib
open Monad_lib.Numeric
open Opcode
open Alcotest

let () =
  run "EIP-7939: Count leading zeros (CLZ) opcode"
    [ test_cases_opcode_1 Clz
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
    ]
