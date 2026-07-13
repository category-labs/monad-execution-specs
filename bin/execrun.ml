open Monad_lib
open Chain.Ethereum
open Numeric
open Byte_string

let fixtures_file = ref None
let test_kind = ref None
let select_fixtures kind =
  Arg.String
    (fun filename ->
      test_kind := Some kind ;
      fixtures_file := Some filename )

let execution_mode = ref `Verify
let set_execution_mode_update_fixture = Arg.String (fun filename -> execution_mode := `Update filename)

let usage_str =
  "Usage: execrun (--blockchain_test FILE | --state_test FILE) [--update_fixture FILE] [--trace]\n"

let trace = ref false

let () =
  Arg.(
    parse
      [ ("--blockchain_test", select_fixtures `Blockchain, "Blockchain test fixture file")
      ; ("--state_test", select_fixtures `State, "State test fixture file")
      ; ("--trace", Set trace, "Trace VM execution")
      ; ( "--update_fixture"
        , set_execution_mode_update_fixture
        , "Generate new fixtures from execution, do not verify provided roots" ) ]
      (fun extra_arg ->
        Format.printf "Unknown argument %s\n" extra_arg ;
        Format.printf "%s" usage_str ;
        exit (-1) )
      usage_str )

let trace = !trace
let execution_mode = !execution_mode

let fixtures_file =
  match !fixtures_file with Some filename -> filename | None -> Format.printf "%s" usage_str ; exit (-1)

let test_kind = match !test_kind with Some kind -> kind | None -> Format.printf "%s" usage_str ; exit (-1)

let check_account_state (address : Address.t) (actual : Account.t) (expected : Account.t) =
  if Account.(actual = expected) then (
    Format.printf "Account states for %s converge\n" (Address.to_hex_string address) ;
    true )
  else (
    Format.printf "Account states for %s diverge\n" (Address.to_hex_string address) ;
    if Bytes.(actual.code <> expected.code) then
      Format.printf "\tCode: %s\n\tExpected: %s\n" (Bytes.to_hex_string actual.code)
        (Bytes.to_hex_string expected.code) ;
    if U256.(actual.balance <> expected.balance) then
      Format.printf "\tBalance: %s\n\tExpected: %s\n" (U256.to_string actual.balance)
        (U256.to_string expected.balance) ;
    if U64.(actual.nonce <> expected.nonce) then
      Format.printf "\tNonce: %s\n\tExpected: %s\n" (U64.to_string actual.nonce)
        (U64.to_string expected.nonce) ;
    if not B32.Map.(equal B32.equal actual.storage expected.storage) then (
      Format.printf "\tStorage differs\n" ;
      let actual_keys = B32.Map.keys actual.storage in
      let expected_keys = B32.Map.keys expected.storage in
      B32.Set.(
        iter
          (fun key ->
            let key_s = B32.to_short_hex_string key in
            let v_actual = B32.Map.find_opt key actual.storage in
            let v_expected = B32.Map.find_opt key expected.storage in
            match (v_actual, v_expected) with
            | Some v_actual, Some v_expected when B32.(v_actual <> v_expected) ->
                Format.printf "\t\tactual(%s): %s\n" key_s (B32.to_hex_string v_actual) ;
                Format.printf "\t\texpected(%s): %s\n" key_s (B32.to_hex_string v_expected)
            | None, Some v_expected ->
                Format.printf "\t\tactual(%s): <EMPTY>\n" key_s ;
                Format.printf "\t\texpected(%s): %s\n" key_s (B32.to_hex_string v_expected)
            | Some v_actual, None ->
                Format.printf "\t\tactual(%s): %s\n" key_s (B32.to_hex_string v_actual) ;
                Format.printf "\t\texpected(%s): <EMPTY>\n" key_s
            | _, _ -> () )
          (union actual_keys expected_keys) ) ) ;
    false )

let check_postconditions (state : Host.WorldState.t) (post : Account.t Address.Map.t) : bool =
  let check_account_existence_and_state addr =
    let actual = Address.Map.find_opt addr state.accounts in
    let expected = Address.Map.find_opt addr post in
    match (actual, expected) with
    | Some actual, Some expected -> check_account_state addr actual expected
    | Some _, None ->
        Format.printf "Account %s should not exist\n" (Address.to_hex_string addr) ;
        false
    | None, Some _ ->
        Format.printf "Account %s fails to exist\n" (Address.to_hex_string addr) ;
        false
    | None, None -> assert false
  in
  let all_addresses = Address.(Set.union (Map.keys state.accounts) (Map.keys post)) in
  Address.Set.fold
    (fun addr acc ->
      let ok = check_account_existence_and_state addr in
      ok && acc )
    all_addresses true

let load_preconditions pre (state : Host.WorldState.t) =
  let open Host.WorldState in
  let accounts = Address.Map.add_seq (Address.Map.to_seq pre) state.accounts in
  {state with accounts}

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
    let trace = trace
  end) in
  Execution.process_block ~verify state block

let run_blockchain_test (fixtures : Fixtures.BlockchainTest.test_case) =
  let check_block_fixture state Fixtures.BlockchainTest.{block; expect_exception} =
    let result = process_block fixtures.config ~verify:(execution_mode = `Verify) state block in
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
  |> Result.get_ok

let check_test_result (name, fixtures, post_state) =
  let success = check_postconditions post_state fixtures.Fixtures.BlockchainTest.post in
  Format.printf "Test %s: %s\n" name (if success then "PASS" else "FAIL") ;
  success

let check_test_results results = List.for_all check_test_result results

let update_fixtures (fixtures : Fixtures.BlockchainTest.test_case) (post_state : Host.WorldState.t) =
  let post = post_state.accounts in
  (* TODO: allow for blocks that expect a failure. *)
  let blocks =
    List.map
      (fun block -> Fixtures.BlockchainTest.{block; expect_exception = None})
      List.(tl (rev post_state.history))
  in
  let info =
    Fixtures.BlockchainTest.
      { fixtures.info with
        filling_rpc_server = Some (Format.sprintf "execrun %s" Version.hash)
      ; fixture_format = "blockchain_test" }
  in
  let genesis_rlp = Rlp.encode (Block.Header.to_rlp fixtures.genesis_block_header) in
  let last_blockhash = U256.of_repr (Block.hash (List.hd post_state.history)) in
  {fixtures with post; blocks; info; genesis_rlp; last_blockhash}

let test_case_to_yojson (fixture : Fixtures.BlockchainTest.test_case) =
  let open Yojson.Safe.Util in
  let open Fixtures in
  (* TODO: this is a hack to add necessary extra fields *)
  let fixture_json = failwith ""(*Fixtures.BlockchainTest.test_case_to_yojson fixture*) in
  let fixture_json =
    (* Add its own RLP encoding and hash to each block. *)
    let blocks =
      to_list fixture_json.$("blocks")
      |> List.map (fun (b : Yojson.Safe.t) ->
          let block = match  failwith "" (*Block.of_yojson b*) with Ok b -> b | Error err -> failwith err in
          let b = b.$("rlp") <- Bytes.to_yojson (Rlp.encode (Block.to_rlp block)) in
          let header_with_hash = b.$("blockHeader").$("hash") <- B32.to_yojson (Block.hash block) in
          b.$("blockHeader") <- header_with_hash )
    in
    let genesis_block =
      Block.{header = fixture.genesis_block_header; transactions = []; ommers = []; withdrawals = []}
    in
    let genesis_block_header =
      fixture_json.$("genesisBlockHeader").$("hash") <- B32.to_yojson (Block.hash genesis_block)
    in
    fixture_json
    |> (fun f -> f.$("blocks") <- `List blocks)
    |> fun f -> f.$("genesisBlockHeader") <- genesis_block_header
  in
  fixture_json

let run_blockchain_tests (tests : (string * Fixtures.BlockchainTest.test_case) list) =
  let test_results : (string * Fixtures.BlockchainTest.test_case * Host.WorldState.t) list =
    List.map (fun (test_name, fixtures) -> (test_name, fixtures, run_blockchain_test fixtures)) tests
  in
  match execution_mode with
  | `Verify -> check_test_results test_results
  | `Update output_file ->
      let updated_fixtures_json =
        List.map
          (fun (name, fixtures, post_state) ->
            let fixtures = update_fixtures fixtures post_state in
            (name, test_case_to_yojson fixtures) )
          test_results
      in
      Out_channel.with_open_text output_file (fun out_channel ->
          Yojson.Safe.pretty_to_channel out_channel (`Assoc updated_fixtures_json) ) ;
      true

let () =
  match test_kind with
  | `Blockchain ->
      let blockchain_tests =
        match Fixtures.BlockchainTest.of_yojson ~skip_invalid:false (Yojson.Safe.from_file fixtures_file) with
        | Error place -> failwith (Format.sprintf "Error when decoding %s" place)
        | Ok tests ->
            List.filter (fun (_name, test_case) -> Fixtures.BlockchainTest.is_active_revision test_case) tests
      in
      if List.is_empty blockchain_tests then Format.printf "No valid tests found in %s!\n" fixtures_file ;
      if not (run_blockchain_tests blockchain_tests) then (Format.printf "Some tests failed\n" ; exit (-1))
  | `State -> failwith "TODO"
