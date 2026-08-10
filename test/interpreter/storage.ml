open Test_utils
open Test_utils.Utils
open Alcotest

open Monad_lib.Numeric
open Monad_lib.Byte_string

let () =
  run "Storage opcodes"
    [ ( "Unset values" (* Check that uninitialized keys contain zero *)
      , let test k =
          test_case
            (Format.sprintf "Sload(%s)" (U256.to_hex_string k))
            `Quick
            (fun () -> test_bytecode_pure ~input_stack:[] Program.(sload (Lit k)) ~output_stack:[U256.zero])
        in
        let test_keys = U256.[~$0; ~$1; ~$2; ~$2 ** 128; max_t] in
        List.map test test_keys )
    ; ( "SLOAD after SSTORE" (* Check that sload sees stored values *)
      , let test_keys = U256.[~$0; ~$1; ~$2; ~$2 ** 128; max_t] in
        let test k =
          test_case
            (Format.sprintf "Sload(%s)" (U256.to_hex_string k))
            `Quick
            (fun () ->
              test_bytecode_pure ~input_stack:[]
                Program.(
                  let stores = test_keys |> List.map (fun k -> sstore (Lit k) (Lit k)) |> Bytes.concat "" in
                  stores ^ sload (Lit k) )
                ~output_stack:[k] )
        in
        List.map test test_keys )
    ; ( "SLOAD near SSTORE" (* Check that storage is word-addressed *)
      , let write_keys = U256.[~$0; ~$2; ~$4; ~$6; ~$8] in
        let test write_key =
          let read_key_1 = U256.(write_key - one) in
          let read_key_2 = U256.(write_key + one) in
          test_case
            (Format.sprintf "Sload(%s); Sload(%s); Sload(%s)" (U256.to_hex_string write_key)
               (U256.to_hex_string read_key_1) (U256.to_hex_string read_key_2) )
            `Quick
            (fun () ->
              test_bytecode_pure ~input_stack:[]
                Program.(
                  sstore (Lit write_key) (Lit U256.max_t)
                  ^ sload (Lit read_key_1)
                  ^ sload (Lit write_key)
                  ^ sload (Lit read_key_2) )
                ~output_stack:U256.[zero; max_t; zero] )
        in
        List.map test write_keys )
    ; ( "SLOAD across transactions" (* Check that storage persists across transactions *)
      , [ (let addr = U256.of_int 0xdeadbeef in
           let value = U256.of_int 0x1234 in
           let bc_write = Program.(sstore (Lit addr) (Lit value)) in
           let bc_read = Program.(sload (Lit addr)) in
           test_case
             (Format.sprintf "Sload(%s)" U256.(to_hex_string zero))
             `Quick
             (fun () ->
               let _, state = test_message (bytecode_to_call_message bc_write) in
               ignore
                 (test_message ~initial_state:state ~expect_output_stack:[value]
                    (bytecode_to_call_message bc_read) ) ) ) ] ) ]
