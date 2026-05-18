open Monad_lib
open Test_utils.Utils
open Chain.Ethereum
open Byte_string

let blockchain_tests_folder = "fixtures" $/ "blockchain_tests"

let drop_test_folder_prefix =
  let prefix = blockchain_tests_folder ^ "/" in
  let prefix_len = String.length prefix in
  fun filename ->
    if String.starts_with ~prefix filename then
      String.sub filename prefix_len (String.length filename - prefix_len)
    else filename

let load_preconditions pre (state : Host.WorldState.t) =
  let open Host.WorldState in
  let accounts = Address.Map.add_seq (Address.Map.to_seq pre) state.accounts in
  {state with accounts}

let check_postconditions (post : Account.t Address.Map.t) (state : Host.WorldState.t) : unit =
  let check_account_existence_and_state addr =
    let actual = Address.Map.find_opt addr state.accounts in
    let expected = Address.Map.find_opt addr post in
    Alcotest.check (Alcotest.option account)
      (Format.sprintf "Account states for %s differ" (Address.to_hex_string addr))
      actual expected
  in
  let all_addresses = Address.(Set.union (Map.keys state.accounts) (Map.keys post)) in
  Address.Set.iter check_account_existence_and_state all_addresses

let load_genesis_block (genesis_block_header : Block.Header.t) (state : Host.WorldState.t) =
  { state with
    history = [Block.{header = genesis_block_header; transactions = []; ommers = []; withdrawals = []}] }

module Test_failure = struct
  type test_failure = Expected_ok of Execution.Error.t | Expected_error of string
  let to_string = function
    | Expected_ok err -> Format.sprintf "Expected ok, got %s" (Execution.Error.to_string err)
    | Expected_error err -> Format.sprintf "Expected error %s, got success" err
end

let run_blockchain_test ((_name : string), (fixtures : Fixtures.BlockchainTest.test_case)) =
  let module Execution = Execution.Make (struct
    let chain_id = fixtures.config.chain_id
    let trace = false
  end) in
  let check_block_fixture state Fixtures.BlockchainTest.{block; expect_exception} =
    let result = Execution.process_block ~verify:true state block in
    match (result, expect_exception) with
    | Ok state, None -> Ok state
    | Error _, Some _ ->
        (* TODO: standarize on error messages and check those. *)
        Ok state
    | Ok _, Some err -> Error (Test_failure.Expected_error err)
    | Error err, None -> Error (Test_failure.Expected_ok err)
  in
  Host.WorldState.empty
  |> load_genesis_block fixtures.genesis_block_header
  |> load_preconditions fixtures.pre
  |> fun s ->
  assert (B32.(Host.WorldState.state_root s = fixtures.genesis_block_header.state_root)) ;
  Result.List.fold_leftM ~f:check_block_fixture s fixtures.blocks
  |> Result.map_error Test_failure.to_string
  |> expect_ok
  |> check_postconditions fixtures.post

let is_substring needle haystack =
  (* Quadratic complexity, we don't really care. *)
  let rec match_at i j =
    if String.length needle <= j then true
    else if String.length haystack <= i then false
    else haystack.[i] = needle.[j] && match_at (i + 1) (j + 1)
  in
  let rec loop i = if i >= String.length haystack then false else match_at i 0 || loop (i + 1) in
  loop 0

let blockchain_tests =
  traverse_folder blockchain_tests_folder
  |> Seq.filter (fun (_path, filename) -> Filename.extension filename = ".json" && filename <> "index.json")
  |> Seq.group (fun (path_1, _) (path_2, _) -> path_1 = path_2)
  |> Seq.map (fun test_group ->
      let (path, filename), tl = Option.get (Seq.uncons test_group) in
      let group_name = drop_test_folder_prefix path in
      let tests =
        Seq.cons (path, filename) tl
        |> List.of_seq
        |> List.sort (fun (_, f1) (_, f2) -> compare f1 f2)
        |> List.map (fun (path, filename) ->
            let path = path $/ filename in
            Alcotest.test_case filename `Quick (fun subtest_filter ->
                let fixtures =
                  Result.get_ok'
                    (Fixtures.BlockchainTest.of_yojson ~skip_invalid:false (Yojson.Safe.from_file path))
                  |> List.filter (fun (_name, test) -> test.Fixtures.BlockchainTest.network = "MONAD_EIGHT")
                in
                let fixtures =
                  match subtest_filter with
                  | None -> fixtures
                  | Some filter -> List.filter (fun (name, _test) -> is_substring filter name) fixtures
                in
                List.iter run_blockchain_test fixtures ) )
      in
      (group_name, tests) )
  |> List.of_seq

(* Blockchain tests contain multiple subtests per json file. The --subtest_filter flag can be used to
   execute a specific such subtest. *)
let subtest_filter_flag =
  Cmdliner.Arg.(value & opt (some string) None & info ["subtest_filter"] ~doc:"Select a specific subtest")

module Test_entry = struct
  type t = string * int
  include Comparable.Make (struct
    type nonrec t = t
    let compare (name, index) (name', index') =
      let d = compare name name' in
      if d <> 0 then d else compare index index'
  end)
end

(* Suppressed tests. *)
let suppressed_tests =
  Test_entry.Set.of_list
    [ ("mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_map_fp2_to_g2", 0)
    ; ("mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_map_fp2_to_g2", 1)
    ; ("mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_map_fp2_to_g2", 2)
    ; ("mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_map_fp2_to_g2", 3)
    ; ("mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_pairing", 0)
    ; ("mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_pairing", 1)
    ; ("mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_pairing", 2)
    ; ("mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_pairing", 3)
    ; ("mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_pairing", 4)
    ; ("mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_pairing", 5)
    ; ("mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_map_fp_to_g1", 0)
    ; ("mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_map_fp_to_g1", 1)
    ; ("mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_map_fp_to_g1", 2)
    ; ("mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_map_fp_to_g1", 3)
    ; ("mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_map_fp_to_g1", 4)
    ; ("mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_variable_length_input_contracts", 0)
    ; ("mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_variable_length_input_contracts", 1)
    ; ("mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_variable_length_input_contracts", 2)
    ; ("mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_variable_length_input_contracts", 3)
    ; ("mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_variable_length_input_contracts", 4)
    ; ("mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_variable_length_input_contracts", 5)
    ; ("mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_variable_length_input_contracts", 6)
    ; ("mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_variable_length_input_contracts", 7)
    ; ("mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_variable_length_input_contracts", 8)
    ; ("mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_variable_length_input_contracts", 9)
    ; ("mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_variable_length_input_contracts", 10)
    ; ("mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_variable_length_input_contracts", 11)
    ; ("mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_variable_length_input_contracts", 12)
    ; ("mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_variable_length_input_contracts", 13)
    ; ("mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_variable_length_input_contracts", 14) ]

(* Filter failing tests. *)
let filter ~name ~index = if Test_entry.Set.mem (name, index) suppressed_tests then `Skip else `Run

let () = Alcotest.run_with_args "Blockchain tests" subtest_filter_flag blockchain_tests ~filter
