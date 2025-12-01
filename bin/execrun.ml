open Monad_lib
open Chain.Ethereum
open Monad_lib.Numeric

let execution = ref None
let set_execution kind = Arg.String (fun filename -> execution := Some (kind, filename))

let usage_str = "Usage: execrun (--blockchain_test FILE | --state_test FILE)"

let () =
  Arg.(
    parse
      [ ("--blockchain_test", set_execution `Blockchain, "Blockchain test fixture file")
      ; ("--state_test", set_execution `State, "State test fixture file") ]
      (fun extra_arg ->
        Format.printf "Unknown argument %s\n" extra_arg ;
        exit (-1) )
      usage_str )

let load_preconditions (state : State.WorldState.t) pre =
  let open State.WorldState in
  let accounts = Address.Map.add_seq (Address.Map.to_seq pre) state.accounts in
  {state with accounts}

let account_expected (address : Address.t) (actual : Account.t) (expected : Account.t) =
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
      let actual_keys = U256.Map.keys actual.storage in
      let expected_keys = U256.Map.keys expected.storage in
      U256.Set.(
        iter
          (fun key ->
            let key_s = U256.to_short_hex_string key in
            let v_actual = U256.Map.find_opt key actual.storage in
            let v_expected = U256.Map.find_opt key expected.storage in
            match (v_actual, v_expected) with
            | Some v_actual, Some v_expected when U256.(v_actual <> v_expected) ->
                Format.eprintf "\t\tactual(%s): %s\n" key_s (U256.to_hex_string v_actual) ;
                Format.eprintf "\t\texpected(%s): %s\n" key_s (U256.to_hex_string v_expected)
            | None, Some v_expected ->
                Format.eprintf "\t\tactual(%s): <EMPTY>\n" key_s ;
                Format.eprintf "\t\texpected(%s): %s\n" key_s (U256.to_hex_string v_expected)
            | Some v_actual, None ->
                Format.eprintf "\t\tactual(%s): %s\n" key_s (U256.to_hex_string v_actual) ;
                Format.eprintf "\t\texpected(%s): <EMPTY>\n" key_s
            | _, _ -> () )
          (union actual_keys expected_keys) ) ) ;
    false )

let assert_postconditions (state : State.WorldState.t) (post : Account.t Address.Map.t) =
  let assert_account_state_expected addr expected =
    match Address.Map.find_opt addr state.accounts with
    | None -> Format.eprintf "Account %s fails to exist\n" (Address.to_string addr)
    | Some actual -> ignore (account_expected addr actual expected)
  in
  Address.Map.iter assert_account_state_expected post

let run_blockchain_test ((name : string), (fixtures : Fixtures.BlockchainTest.test_case)) =
  Format.printf "Running blockchain test %s\n" name ;
  let state = State.WorldState.make fixtures.config.chain_id in

  let state = load_preconditions state fixtures.pre in
    let state = List.fold_left (State.process_block ~verify:false) state fixtures.blocks in
  assert_postconditions state fixtures.post ;
  ignore state ;
  ()

let () =
  match !execution with
  | Some (`Blockchain, blockchain_fixtures) ->
      let blockchain_fixtures =
        match
          Fixtures.BlockchainTest.of_yojson ~skip_invalid:true (Yojson.Safe.from_file blockchain_fixtures)
        with
        | Ok fix -> fix
        | Error place -> failwith (Format.sprintf "Error when decoding %s" place)
      in
      List.iter run_blockchain_test blockchain_fixtures
  | Some (`State, _state_fixtures) -> failwith "TODO"
  | None ->
      Format.printf "No fixture selected\n%s" usage_str ;
      exit (-1)
