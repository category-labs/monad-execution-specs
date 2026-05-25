open Monad_lib
open Test_utils.Utils
open Chain.Ethereum
open Byte_string
open Numeric

let blockchain_tests_folder = "fixtures" $/ "blockchain_tests"

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
let enabled_revisions_for_test : Test_entry.t -> Chain.Monad.Revision.active list =
  (* Tests disabled at the folder level. None of the fixtures inside these folders will be executed. Note that
     only the test fixtures directly inside the folders will be disabled, fixtures in subfolders will be
     executed normally. *)
  let disabled_tests =
    String.Set.of_list
      [ (* alt_bn128 precompiles. *)
        "mf_tests/byzantium/eip197_ec_pairing/gas"
      ; "mf_tests/byzantium/eip196_ec_add_mul/gas"
      ; "mf_tests/byzantium/eip196_ec_add_mul/ecadd"

        (* blake2 precompile. *)
      ; "mf_tests/istanbul/eip152_blake2/blake2"
      ; "mf_tests/istanbul/eip152_blake2/blake2_delegatecall"

        (* modexp precompile. *)
      ; "mf_tests/byzantium/eip198_modexp_precompile/modexp"
      ; "mf_tests/osaka/eip7883_modexp_gas_increase/modexp_thresholds"

        (* p256verify precompile. *)
      ; "mf_tests/osaka/eip7951_p256verify_precompiles/p256verify"
      ; "mf_tests/osaka/eip7951_p256verify_precompiles/eip_mainnet"

        (* BLS precompiles. *)
      ; "mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_g1mul"
      ; "mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_g2msm"
      ; "mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_g2add"
      ; "mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_g1add"
      ; "mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_map_fp2_to_g2"
      ; "mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_g1msm"
      ; "mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_pairing"
      ; "mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_g2mul"
      ; "mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_map_fp_to_g1"
      ; "mf_tests/prague/eip2537_bls_12_381_precompiles/bls12_variable_length_input_contracts"

        (* Other precompiles. *)
      ; "mf_tests/byzantium/eip214_staticcall/staticcall"

        (* MIP-3. *)
      ; "mf_tests/monad_nine/mip3_linear_memory/oom_deep"
      ; "mf_tests/monad_nine/mip3_linear_memory/oom"
      ; "mf_tests/monad_nine/mip3_linear_memory/gas_cost"

        (* MIP-4. *)
      ; "mf_tests/monad_nine/mip4_checkreservebalance/fork_transition"
      ; "mf_tests/monad_nine/mip4_checkreservebalance/tx_revert"
      ; "mf_tests/monad_nine/mip4_checkreservebalance/transfers"
      ; "mf_tests/monad_nine/mip4_checkreservebalance/precompile_call"
      ; "mf_tests/monad_nine/mip4_checkreservebalance/multi_block"

        (* MIP-5. *)
      ; "mf_tests/osaka/eip7823_modexp_upper_bounds/modexp_upper_bounds"
      ; "mf_tests/osaka/eip7939_count_leading_zeros/count_leading_zeros"
      ] [@ocamlformat "disable"]
  in
  (* Tests disabled at the individual test fixture or revision level, specified as a mapping from the test
     folder plus fixture index to the list of revisions for which the tests are to be run (or an empty list
     to suppress the entire test fixture file). Alcotest's filter mechanism does not provide the actual
     filename, just the test family name and the test index. *)
  let enabled_revisions_map =
    Test_entry.Map.of_list
      [ (* modexp precompile. *)
        (("mf_tests/prague/eip7702_set_code_tx/set_code_txs_2", 1), [])
      ; (("mf_tests/prague/eip7702_set_code_tx/set_code_txs_2", 15), [])

        (* Other precompiles. *)
      ; (("mf_tests/shanghai/eip4895_withdrawals/withdrawals", 10), [])
      ; (("mf_tests/frontier/precompiles/precompiles", 0), [])

        (* MIP-3. *)
      ; (("mf_tests/cancun/eip5656_mcopy/mcopy_memory_expansion", 1), [`Eight])
      ; (("mf_tests/frontier/opcodes/call", 1), [`Eight])
      ; (("mf_tests/frontier/opcodes/call", 2), [`Eight])

        (* Misc. *)
      ; (("mf_tests/shanghai/eip3860_initcode/initcode", 1), [`Eight])
      ; (("mf_tests/shanghai/eip3860_initcode/initcode", 2), [`Eight])
      ; (("mf_tests/cancun/eip6780_selfdestruct/selfdestruct", 5), [`Eight])
      ; (("mf_tests/cancun/eip6780_selfdestruct/selfdestruct", 6), [`Eight])
      ; (("mf_tests/frontier/create/create_deposit_oog", 0), [`Eight])
      ; (("mf_tests/frontier/opcodes/all_opcodes", 0), [`Eight])
      ; (("mf_tests/frontier/opcodes/all_opcodes", 1), [`Eight])
      ; (("mf_tests/monad_eight/reserve_balance/transfers", 4), [`Eight])
      ; (("mf_tests/monad_eight/reserve_balance/transfers", 5), [`Eight])
      ; (("mf_tests/monad_eight/reserve_balance/transfers", 21), [`Eight])
      ; (("mf_tests/prague/eip7702_set_code_tx/set_code_txs", 40), [`Eight])
      ; (("mf_tests/prague/eip7702_set_code_tx/set_code_txs", 41), [`Eight])
      ; (("mf_tests/berlin/eip2929_gas_cost_increases/precompile_warming", 0), [`Eight])
      ] [@ocamlformat "disable"]
  in
  fun (name, idx) ->
    if String.Set.mem name disabled_tests then []
    else
      Test_entry.Map.find_opt (name, idx) enabled_revisions_map
      |> Option.value ~default:Chain.Monad.Revision.all_active_revisions

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

let process_block
    (config : Fixtures.BlockchainTest.config) ~(verify : bool) (state : Host.WorldState.t) (block : Block.t) =
  let module Execution = Execution.Make (struct
    let chain_id = config.chain_id
    let revision =
      let rev =
        match config.network with
        | Single rev -> rev
        | Transition {pre; post; timestamp} -> if U256.(block.header.timestamp < timestamp) then pre else post
        | Invalid -> assert false
      in
      rev |> Chain.Monad.Revision.is_active |> Option.get
    let trace = false
  end) in
  Execution.process_block ~verify state block

let run_blockchain_test ((_name : string), (fixtures : Fixtures.BlockchainTest.test_case)) =
  let check_block_fixture state Fixtures.BlockchainTest.{block; expect_exception} =
    let result = process_block fixtures.config ~verify:true state block in
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
        |> List.mapi (fun i (path, filename) ->
            let path = path $/ filename in
            Alcotest.test_case filename `Quick (fun subtest_filter ->
                let matches_subtest_filter : string -> bool =
                  match subtest_filter with
                  | None -> fun _ -> true
                  | Some filter -> fun s -> Option.is_some (String.find_substring ~substring:filter s)
                in
                let matches_rev_filter : Fixtures.BlockchainTest.revision -> bool =
                  let enabled_revisions =
                    (enabled_revisions_for_test (group_name, i) :> Chain.Monad.Revision.t list)
                  in
                  function
                  | Fixtures.BlockchainTest.Single rev -> List.mem rev enabled_revisions
                  | Transition {pre; post; _} ->
                      List.mem pre enabled_revisions && List.mem post enabled_revisions
                  | Invalid -> false
                in
                Fixtures.BlockchainTest.of_yojson ~skip_invalid:false (Yojson.Safe.from_file path)
                |> Result.get_ok'
                |> List.filter (fun (name, (test : Fixtures.BlockchainTest.test_case)) ->
                    matches_subtest_filter name && matches_rev_filter test.config.network )
                |> List.iter run_blockchain_test ) )
      in
      (group_name, tests) )
  |> List.of_seq

(* Blockchain tests contain multiple subtests per json file. The --subtest_filter flag can be used to
   execute a specific such subtest. *)
let subtest_filter_flag =
  Cmdliner.Arg.(value & opt (some string) None & info ["subtest_filter"] ~doc:"Select a specific subtest")

(* Filter failing tests. *)
let filter ~name ~index = if List.is_empty (enabled_revisions_for_test (name, index)) then `Skip else `Run

let () = Alcotest.run_with_args "Blockchain tests" subtest_filter_flag blockchain_tests ~filter
