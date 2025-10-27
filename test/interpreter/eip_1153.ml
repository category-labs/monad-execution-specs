open Test_utils
open Test_utils.Utils
open Alcotest

open Monad_lib
open Monad_lib.Numeric

let () =
  run "EIP-1153: Transient storage opcodes"
    [ ( "Unset values" (* Check that uninitialized keys contain zero *)
      , let test k =
          test_case
            (Format.sprintf "Tload(%s)" (U256.to_short_hex_string k))
            `Quick
            (fun () -> test_bytecode_pure ~input_stack:[] Program.(tload (Lit k)) ~output_stack:[U256.zero])
        in
        let test_keys = U256.[~$0; ~$1; ~$2; ~$2 ** 128; max_t] in
        List.map test test_keys )
    ; ( "TLOAD after TSTORE" (* Check that tload sees stored values *)
      , let test_keys = U256.[~$0; ~$1; ~$2; ~$2 ** 128; max_t] in
        let test k =
          test_case
            (Format.sprintf "Tload(%s)" (U256.to_short_hex_string k))
            `Quick
            (fun () ->
              test_bytecode_pure ~input_stack:[]
                Program.(
                  let stores = test_keys |> List.map (fun k -> tstore (Lit k) (Lit k)) |> Bytes.concat "" in
                  stores ^ tload (Lit k) )
                ~output_stack:[k] )
        in
        List.map test test_keys )
    ; ( "TLOAD after SSTORE" (* Check that transient storage is distinct from storage *)
      , let test_keys = U256.[~$0; ~$1; ~$2; ~$2 ** 128; max_t] in
        let test k =
          test_case
            (Format.sprintf "Tload(%s)" (U256.to_short_hex_string k))
            `Quick
            (fun () ->
              test_bytecode_pure ~input_stack:[]
                Program.(
                  let stores = test_keys |> List.map (fun k -> sstore (Lit k) (Lit k)) |> Bytes.concat "" in
                  stores ^ tload (Lit k) )
                ~output_stack:[U256.zero] )
        in
        List.map test test_keys )
    ; ( "TLOAD near TSTORE" (* Check that transient storage is word-addressed *)
      , let write_keys = U256.[~$0; ~$2; ~$4; ~$6; ~$8] in
        let test write_key =
          let read_key_1 = U256.(write_key - one) in
          let read_key_2 = U256.(write_key + one) in
          test_case
            (Format.sprintf "Tstore(%s); Tload(%s); Tload(%s)" (U256.to_short_hex_string write_key)
               (U256.to_short_hex_string read_key_1)
               (U256.to_short_hex_string read_key_2) )
            `Quick
            (fun () ->
              test_bytecode_pure ~input_stack:[]
                Program.(
                  tstore (Lit write_key) (Lit U256.max_t)
                  ^ tload (Lit read_key_1)
                  ^ tload (Lit write_key)
                  ^ tload (Lit read_key_2) )
                ~output_stack:U256.[zero; max_t; zero] )
        in
        List.map test write_keys ) ]
