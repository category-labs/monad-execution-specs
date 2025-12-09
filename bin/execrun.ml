open Monad_lib
open Chain.Ethereum
open Numeric
open Byte_string

let tests_kind = ref None
let set_tests_kind kind = Arg.String (fun filename -> tests_kind := Some (kind, filename))

let execution_mode = ref `Verify
let set_execution_mode_update_fixture = Arg.String (fun filename -> execution_mode := `Update filename)

let usage_str = "Usage: execrun (--blockchain_test FILE | --state_test FILE) [--update_fixture <file>]\n"

let () =
  Arg.(
    parse
      [ ("--blockchain_test", set_tests_kind `Blockchain, "Blockchain test fixture file")
      ; ("--state_test", set_tests_kind `State, "State test fixture file")
      ; ( "--update_fixture"
        , set_execution_mode_update_fixture
        , "Generate new fixtures from execution, do not verify provided roots" ) ]
      (fun extra_arg ->
        Format.printf "Unknown argument %s\n" extra_arg ;
        exit (-1) )
      usage_str )

let check_account_state (address : Address.t) (actual : Account.t) (expected : Account.t) =
  if actual = expected then (
    Format.eprintf "Account states for %s converge\n" (Address.to_hex_string address) ;
    true )
  else (
    Format.eprintf "Account states for %s diverge\n" (Address.to_hex_string address) ;
    if actual.code <> expected.code then
      Format.eprintf "\tCode: %s\n\tExpected: %s\n" (Bytes.to_hex_string actual.code)
        (Bytes.to_hex_string expected.code) ;
    if actual.balance <> expected.balance then
      Format.eprintf "\tBalance: %s\n\tExpected: %s\n" (U256.to_string actual.balance)
        (U256.to_string expected.balance) ;
    if actual.nonce <> expected.nonce then
      Format.eprintf "\tNonce: %s\n\tExpected: %s\n" (U256.to_string actual.nonce)
        (U256.to_string expected.nonce) ;
    if actual.storage <> expected.storage then (
      Format.eprintf "\tStorage differs\n" ;
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
                Format.eprintf "\t\tactual(%s): %s\n" key_s (B32.to_hex_string v_actual) ;
                Format.eprintf "\t\texpected(%s): %s\n" key_s (B32.to_hex_string v_expected)
            | None, Some v_expected ->
                Format.eprintf "\t\tactual(%s): <EMPTY>\n" key_s ;
                Format.eprintf "\t\texpected(%s): %s\n" key_s (B32.to_hex_string v_expected)
            | Some v_actual, None ->
                Format.eprintf "\t\tactual(%s): %s\n" key_s (B32.to_hex_string v_actual) ;
                Format.eprintf "\t\texpected(%s): <EMPTY>\n" key_s
            | _, _ -> () )
          (union actual_keys expected_keys) ) ) ;
    false )

let check_postconditions (state : State.WorldState.t) (post : Account.t Address.Map.t) : bool =
  let check_account_existence_and_state addr =
    let actual = Address.Map.find_opt addr state.accounts in
    let expected = Address.Map.find_opt addr post in
    match (actual, expected) with
    | Some actual, Some expected -> check_account_state addr actual expected
    | Some _, None ->
        Format.eprintf "Account %s should not exist\n" (Address.to_hex_string addr) ;
        false
    | None, Some _ ->
        Format.eprintf "Account %s fails to exist\n" (Address.to_hex_string addr) ;
        false
    | None, None -> assert false
  in
  let all_addresses = Address.(Set.union (Map.keys state.accounts) (Map.keys post)) in
  Address.Set.for_all check_account_existence_and_state all_addresses

let load_preconditions pre (state : State.WorldState.t) =
  let open State.WorldState in
  let accounts = Address.Map.add_seq (Address.Map.to_seq pre) state.accounts in
  {state with accounts}

let run_blockchain_test (fixtures : Fixtures.BlockchainTest.test_case) =
  State.WorldState.make fixtures.config.chain_id
  |> load_preconditions fixtures.pre
  |> fun s -> List.fold_left (State.process_block ~verify:false) s fixtures.blocks

let check_test_result (name, fixtures, post_state) =
  let success = check_postconditions post_state fixtures.Fixtures.BlockchainTest.post in
  Format.eprintf "Test %s: %s" name (if success then "PASS" else "FAIL") ;
  success

let check_test_results results = List.for_all check_test_result results

let update_fixtures (fixtures : Fixtures.BlockchainTest.test_case) (post_state : State.WorldState.t) =
  assert (List.length post_state.history = List.length fixtures.blocks) ;
  {fixtures with post = post_state.accounts; blocks = List.rev post_state.history}

let test_case_to_yojson fixture =
  let open Yojson.Safe.Util in
  let ( .$() ) obj k = member k obj in
  let ( .$()<- ) obj k v = to_assoc obj |> List.remove_assoc k |> fun l -> (k, v) :: l |> fun l -> `Assoc l in
  (* TODO: this is a hack to add necessary extra fields *)
  let fixture_json = Fixtures.BlockchainTest.test_case_to_yojson fixture in
  let fixture_json =
    (* Add its own RLP encoding to each block. *)
    let blocks =
      to_list fixture_json.$("blocks")
      |> List.map (fun b ->
          let block = match Block.of_yojson b with Ok b -> b | Error err -> failwith err in
          let rlp = Rlp.encode (Block.to_rlp block) in
          b.$("rlp") <- Bytes.to_yojson rlp )
      |> fun bs -> `List bs
    in
    fixture_json.$("blocks") <- blocks
  in
  (* TODO: don't hard-code this. *)
  let fixture_json = fixture_json.$("network") <- `String "MONAD_EIGHT" in
  fixture_json

let run_blockchain_tests (tests : (string * Fixtures.BlockchainTest.test_case) list) =
  let test_results : (string * Fixtures.BlockchainTest.test_case * State.WorldState.t) list =
    List.map (fun (test_name, fixtures) -> (test_name, fixtures, run_blockchain_test fixtures)) tests
  in
  match !execution_mode with
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
  match !tests_kind with
  | Some (`Blockchain, blockchain_fixtures) ->
      let blockchain_tests =
        match
          Fixtures.BlockchainTest.of_yojson ~skip_invalid:false (Yojson.Safe.from_file blockchain_fixtures)
        with
        | Ok fix -> fix
        | Error place -> failwith (Format.sprintf "Error when decoding %s" place)
      in
      if List.is_empty blockchain_tests then Format.eprintf "No valid tests found!\n" ;
      if not (run_blockchain_tests blockchain_tests) then (Format.eprintf "Some tests failed\n" ; exit (-1))
  | Some (`State, _state_fixtures) -> failwith "TODO"
  | None ->
      Format.printf "No fixture selected\n%s" usage_str ;
      exit (-1)
