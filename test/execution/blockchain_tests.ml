open Monad_lib
open Test_utils.Utils
open Chain.Ethereum

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
  Result.List.fold_leftM ~f:check_block_fixture s fixtures.blocks
  |> Result.map_error Test_failure.to_string
  |> expect_ok
  |> check_postconditions fixtures.post

let blockchain_tests =
  traverse_folder blockchain_tests_folder
  |> Seq.filter (fun (_path, filename) -> Filename.extension filename = ".json")
  |> Seq.group (fun (path_1, _) (path_2, _) -> path_1 = path_2)
  |> Seq.map (fun test_group ->
      let (path, filename), tl = Option.get (Seq.uncons test_group) in
      let group_name = drop_test_folder_prefix path in
      let tests =
        Seq.cons (path, filename) tl
        |> Seq.map (fun (path, filename) ->
            let path = path $/ filename in
            Alcotest.test_case filename `Quick (fun () ->
                let fixtures =
                  Result.get_ok'
                    (Fixtures.BlockchainTest.of_yojson ~skip_invalid:false (Yojson.Safe.from_file path))
                  |> List.filter (fun (_name, test) -> test.Fixtures.BlockchainTest.network = "MONAD_EIGHT")
                in
                List.iter run_blockchain_test fixtures ) )
        |> List.of_seq
      in
      (group_name, tests) )
  |> List.of_seq

let () = Alcotest.run "Blockchain tests" blockchain_tests
