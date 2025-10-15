open Test_utils
open Test_utils.Utils
open Alcotest

open Monad_lib.Utils
module Word = Monad_lib.Word

let () =
  run "Memory opcodes"
    [ ( "Unset values" (* Check that uninitialized keys contain zero *)
      , let test_keys = Word.[~$0 * ~$32; ~$1 * ~$32; ~$2 * ~$32; ~$3 * ~$32] in
        let test k =
          test_case
            (Format.sprintf "Mload(0x%s)" (Word.to_short_hex_string k))
            `Quick
            (fun () -> test_bytecode_pure ~input_stack:[] Program.(mload (Lit k)) ~output_stack:[Word.zero])
        in
        List.map test test_keys )
    ; ( "MLOAD after MSTORE" (* Check that mload sees stored values *)
      , let test_keys = Word.[~$0 * ~$32; ~$1 * ~$32; ~$2 * ~$32; ~$3 * ~$32] in
        let test k =
          test_case
            (Format.sprintf "Mload(0x%s)" (Word.to_short_hex_string k))
            `Quick
            (fun () -> test_bytecode_pure ~input_stack:[]
               Program.(
                 let stores = test_keys |> List.map (fun k -> mstore (Lit k) (Lit k)) |> Bytes.concat "" in
                 stores ^ mload (Lit k) )
               ~output_stack:[k] )
        in
        List.map test test_keys )
    ; ( "MLOAD near MSTORE" (* Check that storage is word-addressed *)
      , let write_keys = Word.[~$0 * ~$32; ~$1 * ~$32; ~$2 * ~$32; ~$3 * ~$32] in
        let write_word = Word.of_string "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffffffffffffffffff" in
        let test write_key =
          let read_key_before = Word.(write_key - one) in
          let read_word_before =
            Word.of_string "0x00aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffffffffffffffff"
          in
          let read_key_after = Word.(write_key + one) in
          let read_word_after =
            Word.of_string "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffffffffffffffffff00"
          in
          test_case
            (Format.sprintf "Mload(0x%s); Mload(0x%s); Mload(0x%s)" (Word.to_short_hex_string write_key)
               (Word.to_short_hex_string read_key_before)
               (Word.to_short_hex_string read_key_after) )
            `Quick
            (fun () -> test_bytecode_pure ~input_stack:[]
               Program.(
                 mstore (Lit write_key) (Lit write_word)
                 ^ mload (Lit read_key_before)
                 ^ mload (Lit write_key)
                 ^ mload (Lit read_key_after) )
               ~output_stack:[read_word_after; write_word; read_word_before] )
        in
        List.map test write_keys ) ]
