open Monad_lib
open Test_utils.Utils
open Chain.Ethereum

let fixtures_folder = Sys.getcwd () $/ "fixtures"

let valid_block_tests_folder = fixtures_folder $/ "blockchain_tests" $/ "valid_blocks"

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

let run_blockchain_test ((_name : string), (fixtures : Fixtures.BlockchainTest.test_case)) =
  Host.WorldState.make fixtures.config.chain_id
  |> load_genesis_block fixtures.genesis_block_header
  |> load_preconditions fixtures.pre
  |> fun s ->
  List.fold_left (Execution.process_block ~trace:false ~verify:true) s fixtures.blocks
  |> check_postconditions fixtures.post

let valid_block_tests =
  Sys.readdir valid_block_tests_folder
  |> Array.to_seq
  |> Seq.filter (fun filename -> Filename.extension filename = ".json")
  |> Seq.map (fun filename ->
      Alcotest.test_case filename `Quick (fun () ->
          let path = valid_block_tests_folder $/ filename in
          let fixtures =
            Result.get_ok (Fixtures.BlockchainTest.of_yojson ~skip_invalid:false (Yojson.Safe.from_file path))
          in
          List.iter run_blockchain_test fixtures ) )
  |> List.of_seq

let () = Alcotest.run "Blockchain tests" [("Valid block tests", valid_block_tests)]
