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
      [ (* These tests check that an EIP-4844 blob transaction is rejected. Currently they fail because
           the spec does not have the ability to parse blob transactions at all. *)
        "mf_tests/for_monad_eight/monad_eight/typed_transactions/blob_transaction"
      ; "mf_tests/for_monad_nine/monad_eight/typed_transactions/blob_transaction"
      ; "mf_tests/for_monad_ten/monad_eight/typed_transactions/blob_transaction"
        (* All monad-ten tests suppressed as they fail pre-MIP-8 due to gas costs *)
      ; "mf_tests/for_monad_ninetomonad_tenattime15k/berlin/eip2929_gas_cost_increases/precompile_warming"
      ; "mf_tests/for_monad_ninetomonad_tenattime15k/monad_ten/mip8_pageified_storage/fork_transition"
      ; "mf_tests/for_monad_ten/amsterdam/eip8037_state_creation_gas_cost_increase/block_2d_gas_accounting"
      ; "mf_tests/for_monad_ten/berlin/eip2929_gas_cost_increases/call"
      ; "mf_tests/for_monad_ten/berlin/eip2929_gas_cost_increases/create"
      ; "mf_tests/for_monad_ten/berlin/eip2929_gas_cost_increases/warm_status_revert"
      ; "mf_tests/for_monad_ten/berlin/eip2930_access_list/acl"
      ; "mf_tests/for_monad_ten/berlin/eip2930_access_list/tx_intrinsic_gas"
      ; "mf_tests/for_monad_ten/berlin/eip2930_access_list/tx_type"
      ; "mf_tests/for_monad_ten/byzantium/eip196_ec_add_mul/ecadd"
      ; "mf_tests/for_monad_ten/byzantium/eip196_ec_add_mul/ecmul"
      ; "mf_tests/for_monad_ten/byzantium/eip196_ec_add_mul/gas"
      ; "mf_tests/for_monad_ten/byzantium/eip197_ec_pairing/ecpairing"
      ; "mf_tests/for_monad_ten/byzantium/eip197_ec_pairing/ecpairing_fuzzed"
      ; "mf_tests/for_monad_ten/byzantium/eip197_ec_pairing/gas"
      ; "mf_tests/for_monad_ten/byzantium/eip198_modexp_precompile/modexp"
      ; "mf_tests/for_monad_ten/byzantium/eip211_return_data/call"
      ; "mf_tests/for_monad_ten/byzantium/eip211_return_data/create"
      ; "mf_tests/for_monad_ten/byzantium/eip211_return_data/selfdestruct"
      ; "mf_tests/for_monad_ten/byzantium/eip214_staticcall/staticcall"
      ; "mf_tests/for_monad_ten/cancun/create/create_oog_from_eoa_refunds"
      ; "mf_tests/for_monad_ten/cancun/eip1153_tstore/basic_tload"
      ; "mf_tests/for_monad_ten/cancun/eip1153_tstore/tload_calls"
      ; "mf_tests/for_monad_ten/cancun/eip1153_tstore/tload_reentrancy"
      ; "mf_tests/for_monad_ten/cancun/eip1153_tstore/tstorage"
      ; "mf_tests/for_monad_ten/cancun/eip1153_tstore/tstorage_clear_after_tx"
      ; "mf_tests/for_monad_ten/cancun/eip1153_tstore/tstorage_create_contexts"
      ; "mf_tests/for_monad_ten/cancun/eip1153_tstore/tstorage_execution_contexts"
      ; "mf_tests/for_monad_ten/cancun/eip1153_tstore/tstorage_reentrancy_contexts"
      ; "mf_tests/for_monad_ten/cancun/eip1153_tstore/tstorage_selfdestruct"
      ; "mf_tests/for_monad_ten/cancun/eip1153_tstore/tstore_reentrancy"
      ; "mf_tests/for_monad_ten/cancun/eip5656_mcopy/mcopy"
      ; "mf_tests/for_monad_ten/cancun/eip5656_mcopy/mcopy_contexts"
      ; "mf_tests/for_monad_ten/cancun/eip5656_mcopy/mcopy_memory_expansion"
      ; "mf_tests/for_monad_ten/cancun/eip6780_selfdestruct/collision_selfdestruct"
      ; "mf_tests/for_monad_ten/cancun/eip6780_selfdestruct/dynamic_create2_selfdestruct_collision"
      ; "mf_tests/for_monad_ten/cancun/eip6780_selfdestruct/journal_revert"
      ; "mf_tests/for_monad_ten/cancun/eip6780_selfdestruct/reentrancy_selfdestruct_revert"
      ; "mf_tests/for_monad_ten/cancun/eip6780_selfdestruct/selfdestruct"
      ; "mf_tests/for_monad_ten/cancun/eip6780_selfdestruct/selfdestruct_finalization"
      ; "mf_tests/for_monad_ten/cancun/eip6780_selfdestruct/selfdestruct_revert"
      ; "mf_tests/for_monad_ten/cancun/eip7516_blobgasfee/blobgasfee_opcode"
      ; "mf_tests/for_monad_ten/constantinople/eip1014_create2/create_returndata"
      ; "mf_tests/for_monad_ten/constantinople/eip1014_create2/create2_revert"
      ; "mf_tests/for_monad_ten/constantinople/eip1014_create2/deterministic_deployment"
      ; "mf_tests/for_monad_ten/constantinople/eip1052_extcodehash/extcodehash"
      ; "mf_tests/for_monad_ten/constantinople/eip145_bitwise_shift/shift_combinations"
      ; "mf_tests/for_monad_ten/frontier/create/create_collision"
      ; "mf_tests/for_monad_ten/frontier/create/create_deposit_oog"
      ; "mf_tests/for_monad_ten/frontier/create/create_one_byte"
      ; "mf_tests/for_monad_ten/frontier/create/create_preimage_layout"
      ; "mf_tests/for_monad_ten/frontier/create/create_suicide_during_init"
      ; "mf_tests/for_monad_ten/frontier/create/create_suicide_store"
      ; "mf_tests/for_monad_ten/frontier/eip2681_limit_account_nonce/nonce_reaching_max"
      ; "mf_tests/for_monad_ten/frontier/examples/block_intermediate_state"
      ; "mf_tests/for_monad_ten/frontier/identity_precompile/identity"
      ; "mf_tests/for_monad_ten/frontier/identity_precompile/identity_returndatasize"
      ; "mf_tests/for_monad_ten/frontier/opcodes/all_opcodes"
      ; "mf_tests/for_monad_ten/frontier/opcodes/blockhash"
      ; "mf_tests/for_monad_ten/frontier/opcodes/call"
      ; "mf_tests/for_monad_ten/frontier/opcodes/call_and_callcode_gas_calculation"
      ; "mf_tests/for_monad_ten/frontier/opcodes/calldatacopy"
      ; "mf_tests/for_monad_ten/frontier/opcodes/calldataload"
      ; "mf_tests/for_monad_ten/frontier/opcodes/calldatasize"
      ; "mf_tests/for_monad_ten/frontier/opcodes/data_copy_oog"
      ; "mf_tests/for_monad_ten/frontier/opcodes/dup"
      ; "mf_tests/for_monad_ten/frontier/opcodes/dynamic_jump"
      ; "mf_tests/for_monad_ten/frontier/opcodes/exp"
      ; "mf_tests/for_monad_ten/frontier/opcodes/extcodecopy"
      ; "mf_tests/for_monad_ten/frontier/opcodes/log"
      ; "mf_tests/for_monad_ten/frontier/opcodes/push"
      ; "mf_tests/for_monad_ten/frontier/opcodes/swap"
      ; "mf_tests/for_monad_ten/frontier/precompiles/ecrecover"
      ; "mf_tests/for_monad_ten/frontier/precompiles/precompile_absence"
      ; "mf_tests/for_monad_ten/frontier/precompiles/precompiles"
      ; "mf_tests/for_monad_ten/frontier/precompiles/ripemd"
      ; "mf_tests/for_monad_ten/frontier/scenarios/scenarios"
      ; "mf_tests/for_monad_ten/frontier/validation/header"
      ; "mf_tests/for_monad_ten/frontier/validation/transaction"
      ; "mf_tests/for_monad_ten/homestead/coverage/coverage"
      ; "mf_tests/for_monad_ten/homestead/identity_precompile/identity"
      ; "mf_tests/for_monad_ten/istanbul/eip1344_chainid/chainid"
      ; "mf_tests/for_monad_ten/istanbul/eip152_blake2/blake2"
      ; "mf_tests/for_monad_ten/istanbul/eip152_blake2/blake2_delegatecall"
      ; "mf_tests/for_monad_ten/istanbul/eip2200_net_gas_metering/sstore_combinations"
      ; "mf_tests/for_monad_ten/london/eip1559_fee_market_change/tx_type"
      ; "mf_tests/for_monad_ten/monad_eight/reserve_balance/gas_fees_vs_reserve"
      ; "mf_tests/for_monad_ten/monad_eight/reserve_balance/multi_block"
      ; "mf_tests/for_monad_ten/monad_eight/reserve_balance/transfers"
      ; "mf_tests/for_monad_ten/monad_nine/mip3_linear_memory/gas_cost"
      ; "mf_tests/for_monad_ten/monad_nine/mip3_linear_memory/oom"
      ; "mf_tests/for_monad_ten/monad_nine/mip3_linear_memory/oom_deep"
      ; "mf_tests/for_monad_ten/monad_nine/mip4_checkreservebalance/multi_block"
      ; "mf_tests/for_monad_ten/monad_nine/mip4_checkreservebalance/precompile_call"
      ; "mf_tests/for_monad_ten/monad_nine/mip4_checkreservebalance/transfers"
      ; "mf_tests/for_monad_ten/monad_nine/mip4_checkreservebalance/tx_revert"
      ; "mf_tests/for_monad_ten/monad_ten/mip8_pageified_storage/cross_call"
      ; "mf_tests/for_monad_ten/monad_ten/mip8_pageified_storage/sload_gas"
      ; "mf_tests/for_monad_ten/monad_ten/mip8_pageified_storage/sstore_gas"
      ; "mf_tests/for_monad_ten/monad_ten/mip8_pageified_storage/sstore_refunds"
      ; "mf_tests/for_monad_ten/osaka/eip7823_modexp_upper_bounds/modexp_upper_bounds"
      ; "mf_tests/for_monad_ten/osaka/eip7825_transaction_gas_limit_cap/tx_gas_limit"
      ; "mf_tests/for_monad_ten/osaka/eip7883_modexp_gas_increase/modexp_thresholds"
      ; "mf_tests/for_monad_ten/osaka/eip7939_count_leading_zeros/count_leading_zeros"
      ; "mf_tests/for_monad_ten/osaka/eip7951_p256verify_precompiles/p256verify"
      ; "mf_tests/for_monad_ten/paris/security/selfdestruct_balance_bug"
      ; "mf_tests/for_monad_ten/prague/eip2537_bls_12_381_precompiles/bls12_g1add"
      ; "mf_tests/for_monad_ten/prague/eip2537_bls_12_381_precompiles/bls12_g1msm"
      ; "mf_tests/for_monad_ten/prague/eip2537_bls_12_381_precompiles/bls12_g1mul"
      ; "mf_tests/for_monad_ten/prague/eip2537_bls_12_381_precompiles/bls12_g2add"
      ; "mf_tests/for_monad_ten/prague/eip2537_bls_12_381_precompiles/bls12_g2msm"
      ; "mf_tests/for_monad_ten/prague/eip2537_bls_12_381_precompiles/bls12_g2mul"
      ; "mf_tests/for_monad_ten/prague/eip2537_bls_12_381_precompiles/bls12_map_fp_to_g1"
      ; "mf_tests/for_monad_ten/prague/eip2537_bls_12_381_precompiles/bls12_map_fp2_to_g2"
      ; "mf_tests/for_monad_ten/prague/eip2537_bls_12_381_precompiles/bls12_pairing"
      ; "mf_tests/for_monad_ten/prague/eip2537_bls_12_381_precompiles/bls12_variable_length_input_contracts"
      ; "mf_tests/for_monad_ten/prague/eip2935_historical_block_hashes_from_state/block_hashes"
      ; "mf_tests/for_monad_ten/prague/eip7623_increase_calldata_cost/execution_gas"
      ; "mf_tests/for_monad_ten/prague/eip7623_increase_calldata_cost/refunds"
      ; "mf_tests/for_monad_ten/prague/eip7623_increase_calldata_cost/transaction_validity"
      ; "mf_tests/for_monad_ten/prague/eip7702_set_code_tx/calls"
      ; "mf_tests/for_monad_ten/prague/eip7702_set_code_tx/gas"
      ; "mf_tests/for_monad_ten/prague/eip7702_set_code_tx/set_code_txs"
      ; "mf_tests/for_monad_ten/prague/eip7702_set_code_tx/set_code_txs_2"
      ; "mf_tests/for_monad_ten/shanghai/eip3651_warm_coinbase/warm_coinbase"
      ; "mf_tests/for_monad_ten/shanghai/eip3855_push0/push0"
      ; "mf_tests/for_monad_ten/shanghai/eip3860_initcode/initcode"
      ; "mf_tests/for_monad_ten/spurious_dragon/eip161_state_trie_clearing/touched_account_emptiness"
      ; "mf_tests/for_monad_ten/tangerine_whistle/eip150_operation_gas_costs/eip150_selfdestruct" ]
  in
  (* Tests disabled at the individual test fixture or revision level, specified as a mapping from the test
     folder plus fixture index to the list of revisions for which the tests are to be run (or an empty list
     to suppress the entire test fixture file). Alcotest's filter mechanism does not provide the actual
     filename, just the test family name and the (unsharded) test index. *)
  let enabled_revisions_map = Test_entry.Map.empty in
  fun (name, idx) ->
    if String.Set.mem name disabled_tests then []
    else
      Test_entry.Map.find_opt (name, idx) enabled_revisions_map
      |> Option.value ~default:Chain.Monad.Revision.all_active_revisions

let drop_test_folder_prefix =
  let prefix = blockchain_tests_folder ^ "/" in
  let prefix_len = String.length prefix in
  fun filename ->
    if String.starts_with ~prefix filename then String.drop_first prefix_len filename else filename

let load_preconditions pre (state : State.WorldState.t) =
  let open State.WorldState in
  let accounts = Address.Map.add_seq (Address.Map.to_seq pre) state.accounts in
  {state with accounts}

let check_postconditions (post : Account.t Address.Map.t) (state : State.WorldState.t) : unit =
  let check_account_existence_and_state addr =
    let actual = Address.Map.find_opt addr state.accounts in
    let expected = Address.Map.find_opt addr post in
    Alcotest.check (Alcotest.option account)
      (Format.sprintf "Account states for %s differ" (Address.to_hex_string addr))
      actual expected
  in
  let all_addresses = Address.(Set.union (Map.keys state.accounts) (Map.keys post)) in
  Address.Set.iter check_account_existence_and_state all_addresses

let load_genesis_block (genesis_block_header : Block.Header.t) (state : State.WorldState.t) =
  { state with
    history = [Block.{header = genesis_block_header; transactions = []; ommers = []; withdrawals = []}] }

module Test_failure = struct
  type test_failure = Expected_ok of Execution.Error.t | Expected_error of string
  let to_string = function
    | Expected_ok err -> Format.sprintf "Expected ok, got %s" (Execution.Error.to_string err)
    | Expected_error err -> Format.sprintf "Expected error %s, got success" err
end

let process_block
    (config : Fixtures.BlockchainTest.config) ~(verify : bool) (state : State.WorldState.t) (block : Block.t)
    =
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
  State.WorldState.empty
  |> load_genesis_block fixtures.genesis_block_header
  |> load_preconditions fixtures.pre
  |> fun s ->
  assert (B32.(State.WorldState.state_root s = fixtures.genesis_block_header.state_root)) ;
  Result.List.fold_leftM ~f:check_block_fixture s fixtures.blocks
  |> Result.map_error Test_failure.to_string
  |> expect_ok
  |> check_postconditions fixtures.post

(* Test files can be split into shards to be run in parallel (see dune file).
   Setting BLOCKCHAIN_TESTS_SHARD=k/n selects every n-th test file, starting from
   the k-th one (1-based). When not set, run everything. *)
let shard : (int * int) option =
  Sys.getenv_opt "BLOCKCHAIN_TESTS_SHARD"
  |> Option.map (fun s ->
      Scanf.sscanf s "%d/%d%!" (fun k n ->
          if not (1 <= k && k <= n) then invalid_arg "BLOCKCHAIN_TESTS_SHARD=k/n must satisfy 1 <= k <= n" ;
          (k, n) ) )

let in_shard = match shard with None -> fun _ -> true | Some (k, n) -> fun i -> i mod n = k - 1

let blockchain_test_case group_name i path filename =
  Alcotest.test_case filename `Quick (fun subtest_filter ->
      let enabled_revisions = (enabled_revisions_for_test (group_name, i) :> Chain.Monad.Revision.t list) in
      if List.is_empty enabled_revisions then Alcotest.skip () ;
      let matches_subtest_filter : string -> bool =
        match subtest_filter with
        | None -> fun _ -> true
        | Some filter -> fun s -> String.includes ~affix:filter s
      in
      let matches_rev_filter : Fixtures.BlockchainTest.revision -> bool = function
        | Fixtures.BlockchainTest.Single rev -> List.mem rev enabled_revisions
        | Transition {pre; post; _} -> List.mem pre enabled_revisions && List.mem post enabled_revisions
        | Invalid -> false
      in
      Fixtures.BlockchainTest.of_yojson ~skip_invalid:false (Yojson.Safe.from_file path)
      |> Result.get_ok'
      |> List.filter (fun (name, (test : Fixtures.BlockchainTest.test_case)) ->
          matches_subtest_filter name && matches_rev_filter test.config.network )
      |> List.iter run_blockchain_test )

let blockchain_tests =
  traverse_folder blockchain_tests_folder
  |> Seq.filter (fun (_path, filename) -> Filename.extension filename = ".json" && filename <> "index.json")
  |> Seq.group (fun (path_1, _) (path_2, _) -> path_1 = path_2)
  |> Seq.map (fun test_group ->
      let (path, _), _ = Option.get (Seq.uncons test_group) in
      let files = test_group |> List.of_seq |> List.sort (fun (_, f1) (_, f2) -> compare f1 f2) in
      (drop_test_folder_prefix path, files) )
  |> List.of_seq
  (* Number the test files consecutively. *)
  |> List.fold_left_map
       (fun offset (group_name, files) ->
         (offset + List.length files, (group_name, List.mapi (fun i file -> (offset + i, i, file)) files)) )
       0
  |> snd
  |> List.filter_map (fun (group_name, files) ->
      (* Test files are indexed in the unsharded folder. *)
      files
      |> List.filter_map (fun (global_index, i, (path, filename)) ->
          if in_shard global_index then Some (blockchain_test_case group_name i (path $/ filename) filename)
          else None )
      |> function [] -> None | tests -> Some (group_name, tests) )

(* Blockchain tests contain multiple subtests per json file. The --subtest_filter flag can be used to
   execute a specific such subtest. *)
let subtest_filter_flag =
  Cmdliner.Arg.(value & opt (some string) None & info ["subtest_filter"] ~doc:"Select a specific subtest")

let () =
  let suite_name =
    match shard with
    | None -> "Blockchain tests"
    | Some (k, n) -> Format.sprintf "Blockchain tests - shard %d of %d" k n
  in
  Alcotest.run_with_args suite_name subtest_filter_flag blockchain_tests
