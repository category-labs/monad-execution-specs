open Utils
open Monad_lib
open Opcode

(*
let () = test_program_pure
           ~inputs:[]
           ~outputs:[]
           [Shl]

let () = test_program_pure
           ~inputs:[]
           ~outputs:[]
           [Shr]
 *)

let () =
  let open Alcotest in
  run "EIP-145: Bitwise shifting instructions in EVM"
    [ ( "SHL"
      , tests_pure [Shl]
          [ (["0x1"; "0x0"], ["0x1"])
          ; (["0x1"; "0x1"], ["0x2"])
          ; (["0x1"; "0xff"], ["0x8000000000000000000000000000000000000000000000000000000000000000"])
          ; (["0x1"; "0x100"], ["0x0"])
          ; (["0x1"; "0x0101"], ["0x0"])
          ; ( ["0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"; "0x1"]
            , ["0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe"] )
          ; ( ["0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"; "0xff"]
            , ["0x8000000000000000000000000000000000000000000000000000000000000000"] )
          ; (["0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"; "0x100"], ["0x0"])
          ; (["0x0"; "0x1"], ["0x0"])
          ; ( ["0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"; "0x1"]
            , ["0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe"] ) ] )
    ; ( "SHR"
      , tests_pure [Shr]
          [ (["0x1"; "0x0"], ["0x1"])
          ; (["0x1"; "0x1"], ["0x0"])
          ; ( ["0x8000000000000000000000000000000000000000000000000000000000000000"; "0x1"]
            , ["0x4000000000000000000000000000000000000000000000000000000000000000"] )
          ; (["0x8000000000000000000000000000000000000000000000000000000000000000"; "0xff"], ["0x1"])
          ; (["0x8000000000000000000000000000000000000000000000000000000000000000"; "0x100"], ["0x0"])
          ; (["0x8000000000000000000000000000000000000000000000000000000000000000"; "0x101"], ["0x0"])
          ; ( ["0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"; "0x0"]
            , ["0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"] )
          ; ( ["0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"; "0x1"]
            , ["0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"] )
          ; (["0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"; "0xff"], ["0x1"])
          ; (["0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"; "0x100"], ["0x0"])
          ; (["0x0"; "0x1"], ["0x0"]) ] )
    ; ( "SAR"
      , tests_pure [Sar]
          [ (["0x1"; "0x0"], ["0x1"])
          ; (["0x1"; "0x1"], ["0x0"])
          ; ( ["0x8000000000000000000000000000000000000000000000000000000000000000"; "0x1"]
            , ["0xc000000000000000000000000000000000000000000000000000000000000000"] )
          ; ( ["0x8000000000000000000000000000000000000000000000000000000000000000"; "0xff"]
            , ["0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"] )
          ; ( ["0x8000000000000000000000000000000000000000000000000000000000000000"; "0x100"]
            , ["0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"] )
          ; ( ["0x8000000000000000000000000000000000000000000000000000000000000000"; "0x101"]
            , ["0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"] )
          ; ( ["0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"; "0x0"]
            , ["0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"] )
          ; ( ["0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"; "0x1"]
            , ["0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"] )
          ; ( ["0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"; "0xff"]
            , ["0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"] )
          ; ( ["0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"; "0x100"]
            , ["0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"] )
          ; (["0x0"; "0x1"], ["0x0"])
          ; (["0x4000000000000000000000000000000000000000000000000000000000000000"; "0xfe"], ["0x1"])
          ; (["0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"; "0xf8"], ["0x7f"])
          ; (["0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"; "0xfe"], ["0x1"])
          ; (["0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"; "0xff"], ["0x0"])
          ; (["0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"; "0x100"], ["0x0"]) ] ) ]
