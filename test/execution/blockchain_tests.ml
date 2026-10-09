open Monad_lib
open Test_utils.Utils
open Chain.Ethereum
open Byte_string

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
      ; "mf_tests/for_monad_ten/monad_eight/typed_transactions/blob_transaction" ]
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
    let revision = Fixtures.BlockchainTest.header_revision config block.header
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
  let genesis_revision =
    Fixtures.BlockchainTest.header_revision fixtures.config fixtures.genesis_block_header
  in
  assert (B32.(State.WorldState.state_root genesis_revision s = fixtures.genesis_block_header.state_root)) ;
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
