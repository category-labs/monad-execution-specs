open Test_utils
open Test_utils.Utils
open Alcotest

open Monad_lib.Numeric
open Monad_lib.Byte_string

let () =
  run "Memory opcodes"
    [ ( "Unset values" (* Check that uninitialized keys contain zero *)
      , let test_keys = U256.[~$0 * ~$32; ~$1 * ~$32; ~$2 * ~$32; ~$3 * ~$32] in
        let test k =
          test_case
            (Format.sprintf "Mload(%s)" (U256.to_hex_string k))
            `Quick
            (fun () -> test_bytecode_pure ~input_stack:[] Program.(mload (Lit k)) ~output_stack:[U256.zero])
        in
        List.map test test_keys )
    ; ( "MLOAD after MSTORE" (* Check that mload sees stored values *)
      , let test_keys = U256.[~$0 * ~$32; ~$1 * ~$32; ~$2 * ~$32; ~$3 * ~$32] in
        let test k =
          test_case
            (Format.sprintf "Mload(%s)" (U256.to_hex_string k))
            `Quick
            (fun () ->
              test_bytecode_pure ~input_stack:[]
                Program.(
                  let stores = test_keys |> List.map (fun k -> mstore (Lit k) (Lit k)) |> Bytes.concat "" in
                  stores ^ mload (Lit k) )
                ~output_stack:[k] )
        in
        List.map test test_keys )
    ; ( "MLOAD near MSTORE" (* Check that memory is byte-addressed *)
      , (* Writes start at position 1 so that we can read at p-1 without running out of gas. *)
        let write_keys =
          U256.[one + (~$0 * ~$32); one + (~$1 * ~$32); one + (~$2 * ~$32); one + (~$3 * ~$32)]
        in
        let write_word =
          U256.of_string "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffffffffffffffffff"
        in
        let test write_key =
          let read_key_before = U256.(write_key - one) in
          let read_word_before =
            U256.of_string "0x00aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffffffffffffffff"
          in
          let read_key_after = U256.(write_key + one) in
          let read_word_after =
            U256.of_string "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffffffffffffffffff00"
          in
          test_case
            (Format.sprintf "Mload(%s); Mload(%s); Mload(%s)" (U256.to_hex_string write_key)
               (U256.to_hex_string read_key_before)
               (U256.to_hex_string read_key_after) )
            `Quick
            (fun () ->
              test_bytecode_pure ~input_stack:[]
                Program.(
                  mstore (Lit write_key) (Lit write_word)
                  ^ mload (Lit read_key_before)
                  ^ mload (Lit write_key)
                  ^ mload (Lit read_key_after) )
                ~output_stack:[read_word_after; write_word; read_word_before] )
        in
        List.map test write_keys ) ]
