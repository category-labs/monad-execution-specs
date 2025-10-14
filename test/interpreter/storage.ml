open Test_utils
open Test_utils.Utils
open Alcotest

module Word = Monad_lib.Word

let () =
  run "Storage opcodes"
    [ ( "Unset values" (* Check that uninitialized keys contain zero *)
      , let test k =
          test_case
            (Format.sprintf "Sload(0x%s)" (Word.to_short_hex_string k))
            `Quick
            (test_program_pure ~push:[] Program.(sload (Lit k)) ~pop:[Word.zero])
        in
        let test_keys = Word.[~$0; ~$1; ~$2; ~$2 ** 128; max_unsigned_t] in
        List.map test test_keys )
    ; ( "SLOAD after SSTORE" (* Check that sload sees stored values *)
      , let test_keys = Word.[~$0; ~$1; ~$2; ~$2 ** 128; max_unsigned_t] in
        let test k =
          test_case
            (Format.sprintf "Sload(0x%s)" (Word.to_short_hex_string k))
            `Quick
            (test_program_pure ~push:[]
               Program.(
                 let stores = test_keys |> List.map (fun k -> sstore (Lit k) (Lit k)) |> List.concat in
                 stores @ sload (Lit k) )
               ~pop:[k] )
        in
        List.map test test_keys )
    ; ( "SLOAD near SSTORE" (* Check that storage is word-addressed *)
      , let write_keys = Word.[~$0; ~$2; ~$4; ~$6; ~$8] in
        let test write_key =
          let read_key_1 = Word.(write_key - one) in
          let read_key_2 = Word.(write_key + one) in
          test_case
            (Format.sprintf "Sload(0x%s); Sload(0x%s); Sload(0x%s)" (Word.to_short_hex_string write_key)
               (Word.to_short_hex_string read_key_1)
               (Word.to_short_hex_string read_key_2) )
            `Quick
            (test_program_pure ~push:[]
               Program.(
                 sstore (Lit write_key) (Lit Word.max_unsigned_t)
                 @ sload (Lit read_key_1)
                 @ sload (Lit write_key)
                 @ sload (Lit read_key_2) )
               ~pop:Word.[zero; max_unsigned_t; zero] )
        in
        List.map test write_keys ) ]
