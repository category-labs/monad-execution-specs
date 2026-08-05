open Alcotest
open Monad_lib
open Test_utils
open Test_utils.Utils
open Numeric
open Byte_string
open Chain.Ethereum
open State
open Lens.Infix

open Staking
module Function = Staking.Function

let address = Address.of_hex_string
let assert' msg property = check bool msg true property

let staking_error = Alcotest.testable (Fmt.of_to_string Staking.Error.encode_error) Stdlib.( = )
let validator_id =
  Alcotest.testable (Fmt.of_to_string (fun (Val_id.Val_id i) -> U64.to_string i)) Val_id.( = )
let epoch = Alcotest.testable (Fmt.of_to_string (fun (Epoch.Epoch i) -> U64.to_string i)) Epoch.( = )

let expect_ok v = expect_ok ~err_kind:staking_error v
let expect_error v = expect_error staking_error v

(* Decoding error messages from the staking contract's output string. It's important to check this as
   error messages are observable. *)
let error_of_output_string : string -> Staking.Error.t = function
  | "internal error" -> Internal_error
  | "method not supported" -> Method_not_supported
  | "invalid input" -> Invalid_input
  | "validator exists" -> Validator_exists
  | "unknown validator" -> Unknown_validator
  | "unknown delegator" -> Unknown_delegator
  | "withdrawal id exists" -> Withdrawal_id_exists
  | "unknown withdrawal id" -> Unknown_withdrawal_id
  | "withdrawal not ready" -> Withdrawal_not_ready
  | "insufficient stake" -> Insufficient_stake
  | "invalid secp pubkey" -> Invalid_secp_pubkey
  | "invalid bls pubkey" -> Invalid_bls_pubkey
  | "invalid secp signature" -> Invalid_secp_signature
  | "invalid bls signature" -> Invalid_bls_signature
  | "secp signature verification failed" -> Secp_signature_verification_failed
  | "bls signature verification failed" -> Bls_signature_verification_failed
  | "not in validator set" -> Not_in_validator_set
  | "solvency error" -> Solvency_error
  | "called snapshot while in boundary" -> Snapshot_in_boundary
  | "invalid epoch change" -> Invalid_epoch_change
  | "requires auth address" -> Requires_auth_address
  | "commission too high" -> Commission_too_high
  | "delegation is too small" -> Delegation_too_small
  | "external reward too small" -> External_reward_too_small
  | "external reward too large" -> External_reward_too_large
  | "length mismatch" -> Length_mismatch
  | "overflow" -> Arithmetic_error Overflow
  | "underflow" -> Arithmetic_error Underflow
  | "division by zero" -> Arithmetic_error Division_by_zero
  | "value is nonzero" -> Value_non_zero
  | "input too short" -> Input_too_short
  | _ -> assert false

module M = Contract.Storage.M

(* Call a contract function via a message pass (avoiding dispatch, but performing ABI encoding/decoding). This
   is not strictly necessary; the staking contract functions can be called directly, but then the ABI parameter
   encoding would go untested.
   Note that call does not check gas costs.
 *)
(* TODO: we would like to move the encoding/decoding testing to its own module. Round-tripping for every
   function call is expensive. *)
let call
    (type i o)
    (fn : (i, o) Function.impl)
    ~sender
    ?(endpoint = staking_contract)
    ?(on_error = `Rollback)
    ?(value = U256.zero)
    (input : i) : (o, 'e) result M.t =
  let msg =
    Abi.Signature.input_to_message ~prepend_selector:true ~value ~sender ~recipient:staking_address
      ~gas:100_000_000L
      ~memory_capacity:(Uint.to_uint32 Evm.Vm.Memory.max_memory_usage)
      fn.signature input
  in
  fun state ->
    (* Keep track of the state explicitly so state updates can be unrolled in case of error. *)
    let result, state' = endpoint msg state in
    match result.status_code with
    | Success ->
        (* Output decoding should not fail under any circumstances. *)
        let outputs = Result.get_ok Type.(dec_bytes fn.signature.output result.output_data) in
        (Ok outputs, state')
    | _ -> (
        let error = error_of_output_string result.output_data in
        (Error error, match on_error with `Rollback -> state | `Keep -> state') )

let syscall (fn : ('i, 'o) Function.impl) ?(value = U256.zero) (input : 'i) : ('o, 'e) result M.t =
  call fn ~endpoint:staking_syscalls ~sender:Chain.Monad.system_sender ~value input

let initial_state : TransactionState.t =
  let state = TransactionState.empty in
  (* Set staking CA nonce to 1. *)
  let state = state.^(TransactionState.account Staking.staking_address |-- Account.nonce) <- U64.one in
  (* Initially, epoch=1 and in_epoch_delay_period=false. *)
  let result, state =
    Staking.M.(
      let$ () = Staking.Variables.epoch $= Epoch.one in
      Staking.Variables.in_epoch_delay_period $= false )
      state
  in
  let () = Result.get_ok result in
  state

let check_post_state (test_name : string) (post_state : TransactionState.t) =
  let open Chain.Ethereum in
  let filename = Format.sprintf "staking_tests/%s.json" test_name in
  let expected_storage = Result.get_ok' (Storage.of_yojson (Yojson.Safe.from_file filename)) in
  let actual_storage = TransactionState.(post_state.^(account staking_address).storage) in
  let keys = B32.Set.(union (Storage.keys expected_storage) (Storage.keys actual_storage)) in
  B32.Set.to_list keys
  |> List.sort B32.compare
  |> List.iteri (fun i k ->
      let expected_val = Storage.find k expected_storage in
      let actual_val = Storage.find k actual_storage in
      if B32.(expected_val <> actual_val) then
        fail
          (Format.sprintf "Error on %d'th key %s\n\tExpected: %s\n\tActual:   %s\n" i (B32.to_hex_string k)
             (B32.to_hex_string expected_val) (B32.to_hex_string actual_val) ) )

let run_from_initial_state ?(compare_with : string option) (action : 'a M.t) : 'a =
  let result, post_state = action initial_state in
  Option.iter (fun test_name -> check_post_state test_name post_state) compare_with ;
  result

(**** Wrappers over contract functions. ****)
(* Create and add a validator. *)
type add_validator_result = {val_id : Val_id.t; sign_address : Address.t}
let craft_add_validator_input ~auth_address ~stake ~commission ~secret =
  let (secp_pk, secp_sk), (bls_pk, bls_sk) =
    let secp_pk, secp_sk = Crypto.Secp.gen_keypair secret in
    let bls_pk, bls_sk = Crypto.Bls.gen_keypair secret in
    ((secp_pk, secp_sk), (bls_pk, bls_sk))
  in
  let message =
    Bytes.(
      concat empty
        [ B33.to_bytes (Crypto.Secp.pk_to_bytes secp_pk)
        ; B48.to_bytes (Crypto.Bls.pk_to_bytes bls_pk)
        ; Address.to_bytes auth_address
        ; U256.to_repr_bytes stake
        ; U256.to_repr_bytes commission ] )
  in
  assert (Bytes.length message = 165) ;
  let secp_sig = Crypto.Secp.(signature_to_bytes (sign secp_sk message)) in
  let bls_sig = Crypto.Bls.(signature_to_bytes (sign bls_sk message)) in
  (Type.Tuple.[message; secp_sig; bls_sig], Crypto.Secp.address_of_pubkey secp_pk)

let add_validator_wrapper
    ?(commission = U256.zero) ?(secret = B32.of_hex_string "0x1000") ~auth_address ~stake () :
    (add_validator_result, Staking.Error.t) result M.t =
  let inputs, sign_address = craft_add_validator_input ~auth_address ~stake ~commission ~secret in
  M.(
    let$ result = call add_validator_function ~value:stake ~sender:auth_address inputs in
    match result with
    | Ok val_id ->
        let$ () = update_field (staking_account |-- Account.balance) (fun bal -> U256.(bal + stake)) in
        return (Ok {val_id; sign_address})
    | Error err -> return (Error err) )

(* Never expected to fail. *)
let snapshot =
  M.(
    let$ () = expect_ok <$> syscall syscall_snapshot_function [] in
    return () )

(* Never expected to fail. *)
let inc_epoch =
  M.(
    let$ epoch = !$Variables.epoch in
    let$ () = expect_ok <$> syscall syscall_on_epoch_change_function [Result.get_ok Epoch.(epoch + 1)] in
    return () )

(* Never expected to fail. *)
let skip_to_next_epoch =
  M.(
    let$ () = snapshot in
    let$ () = inc_epoch in
    return () )

let pull_delegator_up_to_date val_id address =
  M.(
    let$ _ = expect_ok <$> call get_delegator_function ~sender:Address.zero [val_id; address] in
    return () )

let reward = U256.(~$1 * mon)

(* Delegate and, if successful, also credit the staking contract balance. *)
let delegate_and_credit val_id ~sender ~value =
  M.(
    let$ result = call delegate_function ~sender ~value [val_id] in
    let$ () =
      when_ (Result.is_ok result)
        (update_field (staking_account |-- Account.balance) (fun b -> U256.(b + value)))
    in
    return result )

(* Reward and also credit the staking contract balance. The call to external_reward_function is expected to
   succeed. *)
let external_reward_and_credit val_id ~sender ~value =
  M.(
    let$ _ = expect_ok <$> call external_reward_function ~sender ~value [val_id] in
    update_field (staking_account |-- Account.balance) (fun b -> U256.(b + value)) )

let check_validator_flags name expected_flags val_id =
  M.(
    let$ ve = !$(Variables.val_execution val_id) in
    let actual = ve.address_flags.flags in
    assert' name (actual = expected_flags) ;
    return () )

let check_validator_stake name expected val_id =
  M.(
    let$ ve = !$(Variables.val_execution val_id) in
    check u256 name expected ve.stake ; return () )

let check_delegator_state ~val_id ~delegator ~expected_stake ~expected_rewards =
  M.(
    let$ () = pull_delegator_up_to_date val_id delegator in
    let$ del = !$(Variables.delegator (val_id, delegator)) in
    check u256 "stake" expected_stake del.stake ;
    check u256 "rewards" expected_rewards del.rewards ;
    return () )

(**** Uncategorized tests. ****)

let test_invoke_fallback () =
  let sender = address "0xdeadbeef" in
  let value = min_auth_address_stake in

  let signature_bytes = "\xff\xff\xff\xff" in
  let msg =
    Evmc.Message.
      { kind = Call
      ; depth = 0l
      ; gas = 0L
      ; sender
      ; value
      ; recipient = staking_address
      ; input_data = signature_bytes
      ; delegated = false
      ; static = false
      ; create2_salt = B32.zeros
      ; code = Bytes.empty
      ; code_address = Address.zero
      ; memory_capacity = Uint.to_uint32 Evm.Vm.Memory.max_memory_usage }
  in
  let () =
    let msg = Evmc.Message.{msg with gas = 40_000L} in
    let result, post_state = staking_contract msg initial_state in
    check status_code "result.status_code" Revert result.status_code ;
    check_post_state "invoke_fallback" post_state
  in

  let () =
    let msg = Evmc.Message.{msg with gas = 39_999L} in
    let result, post_state = staking_contract msg initial_state in
    check status_code "result.status_code" Out_of_gas result.status_code ;
    check_post_state "invoke_fallback" post_state
  in
  ()

let test_accumulator_is_monotonic_again () =
  run_from_initial_state ~compare_with:"accumulator_is_monotonic_again"
    M.(
      let$ {val_id; sign_address} =
        expect_ok
        <$> add_validator_wrapper ~auth_address:(address "0xdeadbeef") ~stake:active_validator_stake ()
      in
      let$ _ = expect_some ~msg:"validator_exists" <$> !$(Variables.val_execution_opt val_id) in
      let validator1_loc = Variables.val_execution val_id in

      let$ () = skip_to_next_epoch in

      let$ () =
        let rec loop i previous_accumulator =
          when_ (i > 0)
            (let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
             let$ validator = !$validator1_loc in
             let current_accumulator = validator.rewards_per_token in
             (* Check that accumulator is monotonically increasing. *)
             assert' "current_accumulator > previous_accumulator"
               U256.(current_accumulator > previous_accumulator) ;
             (* Update for next iteration. *)
             loop (i - 1) current_accumulator )
        in
        loop 10 U256.zero
      in

      let$ () = skip_to_next_epoch in

      let$ _ = expect_some ~msg:"validator exists" <$> !$(Variables.val_execution_opt val_id) in
      return () )

(**** Commission tests. ****)

let test_revert_if_commission_too_high () =
  run_from_initial_state ~compare_with:"revert_if_commission_too_high"
    M.(
      let auth_address = address "0xababab" in
      let bad_commission = U256.(~@"2000000000000000000") in
      (* Commission too high. *)
      let$ () =
        expect_error Commission_too_high
        <$> add_validator_wrapper ~auth_address ~stake:min_auth_address_stake ~commission:bad_commission ()
      in

      (* Add a validator with no commission to set a bad commission. *)
      let$ {val_id; _} =
        expect_ok
        <$> add_validator_wrapper ~auth_address ~stake:min_auth_address_stake ~commission:U256.zero ()
      in
      let$ () =
        expect_error Commission_too_high
        <$> call change_commission_function ~sender:auth_address [val_id; bad_commission]
      in
      return () )

let test_non_auth_attempts_to_change_commission () =
  run_from_initial_state ~compare_with:"non_auth_attempts_to_change_commission"
    M.(
      let auth_address = address "0x600d" in
      let bad_sender = address "0xbadd" in

      let$ {val_id; _} = expect_ok <$> add_validator_wrapper ~auth_address ~stake:min_auth_address_stake () in
      let$ () =
        expect_error Requires_auth_address
        <$> call change_commission_function ~sender:bad_sender [val_id; max_commission]
      in
      return () )

let test_validator_has_commission (commission_percent : int) (reward : U256.t) =
  let fixture_name =
    Format.sprintf "validator_has_commission_%d_%s" commission_percent U256.(to_string reward)
  in
  run_from_initial_state ~compare_with:fixture_name
    M.(
      let commission = U256.(mon * ~$commission_percent / ~$100) in
      let auth_address = address "0xababab" in

      let$ {val_id; sign_address} =
        expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ~commission ()
      in
      let$ () = skip_to_next_epoch in

      let del_address = address "0xaaaabbbb" in
      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:del_address ~value:active_validator_stake in
      let$ () = skip_to_next_epoch in

      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = pull_delegator_up_to_date val_id auth_address in
      let$ () = pull_delegator_up_to_date val_id del_address in

      let expected_commission = U256.(reward * ~$commission_percent / ~$100) in
      let expected_delegator_reward = U256.((reward - expected_commission) / ~$2) in

      let$ delegator = !$(Variables.delegator (val_id, del_address)) in
      check u256 "delegator rewards" expected_delegator_reward delegator.rewards ;
      let$ validator = !$(Variables.delegator (val_id, auth_address)) in
      check u256 "validator rewards" U256.(expected_commission + expected_delegator_reward) validator.rewards ;

      return () )

let test_validator_has_commission () =
  let commission_values = [1; 5; 10; 25; 50; 66; 75; 90] in
  let reward_values =
    U256.[zero; mon / ~$25; mon / ~$50; ~$2 * mon; ~$10 * mon; ~$25 * mon; ~$300 * mon; ~$1000 * mon]
  in
  List.iter
    (fun commission_percent ->
      List.iter (fun reward -> test_validator_has_commission commission_percent reward) reward_values )
    commission_values

let test_validator_changes_commission () =
  run_from_initial_state ~compare_with:"validator_changes_commission"
    M.(
      (* 5% commission. *)
      let starting_commission = U256.(mon / ~$20) in
      let auth_address = address "0xdeadbeef" in
      let delegator = address "0xde1e" in

      let$ {val_id; sign_address} =
        expect_ok
        <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ~commission:starting_commission
              ()
      in

      (* Create another delegator with 90% of this stake for the validator pool.
         Otherwise, the auth delegator gets all the commission and this doesn't
         test anything. *)
      let$ _ =
        expect_ok <$> delegate_and_credit val_id ~sender:delegator ~value:U256.(~$9 * active_validator_stake)
      in
      let$ () = skip_to_next_epoch in

      (* Change validator's commission to 20%; this won't go live until the next epoch. *)
      let new_commission = U256.(mon / ~$5) in
      let$ _ = expect_ok <$> call change_commission_function ~sender:auth_address [val_id; new_commission] in

      (* Reward this epoch, before and after the boundary, to verify both consensus and snapshot views use
         the starting commission. *)
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = snapshot in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      (* Auth address has 5% commission and 10% of stake pool. Note that stake pool rewards are applied
         after the commission, so he gets two rewards at 14.5% each. If the auth has stake `S` and commission
         `C`, both expressed as percents, the reward including commission is: C+S(1-C) *)
      let total_rewards = U256.(~$2 * reward) in
      let auth_running_rewards = U256.(reward * ~$29 / ~$100) in
      let$ () = pull_delegator_up_to_date val_id auth_address in
      let$ () = pull_delegator_up_to_date val_id delegator in
      let$ () =
        let$ validator = !$(Variables.delegator (val_id, auth_address)) in
        check u256 "validator rewards" auth_running_rewards validator.rewards ;
        let$ delegator = !$(Variables.delegator (val_id, delegator)) in
        check u256 "delegator rewards" U256.(total_rewards - auth_running_rewards) delegator.rewards ;
        return ()
      in

      (* Next epoch, new commission is live. *)
      let$ () = inc_epoch in

      (* Reward before and after the boundary again, uses the new commission. *)
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = snapshot in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      let total_rewards = U256.(total_rewards + (~$2 * reward)) in
      let auth_running_rewards = U256.(auth_running_rewards + (reward * ~$56 / ~$100)) in
      let$ () = pull_delegator_up_to_date val_id auth_address in
      let$ () = pull_delegator_up_to_date val_id delegator in
      let$ () =
        let$ validator = !$(Variables.delegator (val_id, auth_address)) in
        check u256 "validator rewards" auth_running_rewards validator.rewards ;
        let$ delegator = !$(Variables.delegator (val_id, delegator)) in
        check u256 "delegator rewards" U256.(total_rewards - auth_running_rewards) delegator.rewards ;
        return ()
      in

      return () )

(**** Input validation tests. ****)

let test_add_validator_revert_invalid_input_size () =
  let sender = address "0xdeadbeef" in
  let value = min_auth_address_stake in

  let inputs, _ =
    craft_add_validator_input ~auth_address:sender ~stake:value ~commission:U256.zero
      ~secret:B32.(of_hex_string "0x1000")
  in
  let msg =
    Abi.Signature.input_to_message ~prepend_selector:false ~gas:1_000_000L ~sender:Address.zero
      ~value:U256.zero add_validator_function.signature ~recipient:staking_address
      ~memory_capacity:(Uint.to_uint32 Evm.Vm.Memory.max_memory_usage)
      inputs
  in
  let () =
    let msg_too_short = {msg with input_data = Bytes.(sub msg.input_data 0 (length msg.input_data - 1))} in
    let result, _ = Function.send_message (Pack add_validator_function) msg_too_short initial_state in
    check status_code "status_code" Revert result.status_code ;
    check staking_error "staking_error" Input_too_short (error_of_output_string result.output_data)
  in
  let () =
    let msg_too_long = {msg with input_data = msg.input_data ^ "\xff"} in
    let result, _ = Function.send_message (Pack add_validator_function) msg_too_long initial_state in
    check status_code "status_code" Revert result.status_code ;
    check staking_error "staking_error" Invalid_input (error_of_output_string result.output_data)
  in
  ()

let test_add_validator_revert_bad_signature () =
  let auth_address = address "0xababab" in
  let [message; good_secp_sig; good_bls_sig], _ =
    craft_add_validator_input ~auth_address ~stake:min_auth_address_stake ~commission:U256.zero
      ~secret:B32.(of_hex_string "0x1000")
  in

  (* Bad SECP signature. *)
  let _bad_secp_pk, bad_secp_sk = Crypto.Secp.gen_keypair B32.(of_hex_string "0x2000") in
  let bad_secp_sig = Crypto.Secp.(signature_to_bytes (sign bad_secp_sk message)) in

  run_from_initial_state ~compare_with:"add_validator_revert_bad_signature"
    M.(
      expect_error Secp_signature_verification_failed
      <$> call add_validator_function ~sender:auth_address ~value:min_auth_address_stake
            [message; bad_secp_sig; good_bls_sig] ) ;

  (* Bad BLS signature. *)
  let _bad_bls_pk, bad_bls_sk = Crypto.Bls.gen_keypair B32.(of_hex_string "0x2000") in
  let bad_bls_sig = Crypto.Bls.(signature_to_bytes (sign bad_bls_sk message)) in
  run_from_initial_state ~compare_with:"add_validator_revert_bad_signature"
    M.(
      expect_error Bls_signature_verification_failed
      <$> call add_validator_function ~sender:auth_address ~value:min_auth_address_stake
            [message; good_secp_sig; bad_bls_sig] )

let test_add_validator_revert_msg_value_not_signed () =
  run_from_initial_state ~compare_with:"add_validator_revert_msg_value_not_signed"
    M.(
      let auth_address = address "0xababab" in
      let value = min_auth_address_stake in
      let input, _ =
        craft_add_validator_input ~auth_address ~stake:U256.zero ~commission:U256.zero
          ~secret:B32.(of_hex_string "0x1000")
      in
      expect_error Invalid_input <$> call add_validator_function ~sender:auth_address ~value input )

let test_add_validator_revert_already_exists () =
  run_from_initial_state ~compare_with:"add_validator_revert_already_exists"
    M.(
      let auth_address = address "0xababab" in
      let value = min_auth_address_stake in
      let input, _ =
        craft_add_validator_input ~auth_address ~stake:value ~commission:U256.zero
          ~secret:B32.(of_hex_string "0x1000")
      in
      let$ _ = expect_ok <$> call add_validator_function ~sender:auth_address ~value input in
      expect_error Validator_exists <$> call add_validator_function ~sender:auth_address ~value input )

let test_add_validator_revert_minimum_stake_not_met () =
  run_from_initial_state ~compare_with:"add_validator_revert_minimum_stake_not_met"
    M.(
      let value = U256.one in
      let auth_address = address "0xababab" in
      let input, _ =
        craft_add_validator_input ~auth_address ~stake:value ~commission:U256.zero
          ~secret:B32.(of_hex_string "0x1000")
      in
      expect_error Insufficient_stake
      <$> call add_validator_function ~sender:auth_address ~value:U256.one input )

let test_nonpayable_functions_revert () =
  run_from_initial_state ~compare_with:"nonpayable_functions_revert"
    M.(
      let value = U256.(~$5 * mon) in
      let check_nonpayable (type i o) ?(endpoint = staking_contract) (fn : (i, o) Function.impl) (input : i) :
          unit t =
        expect_error Value_non_zero <$> call ~endpoint ~value ~sender:Address.zero fn input
      in

      let$ () = check_nonpayable ~endpoint:staking_syscalls syscall_snapshot_function [] in
      let$ () = check_nonpayable ~endpoint:staking_syscalls syscall_on_epoch_change_function [Epoch.zero] in

      let$ () = check_nonpayable undelegate_function [Val_id.zero; U256.zero; U8.zero] in
      let$ () = check_nonpayable compound_function [Val_id.zero] in
      let$ () = check_nonpayable withdraw_function [Val_id.zero; U8.zero] in
      let$ () = check_nonpayable claim_rewards_function [Val_id.zero] in
      let$ () = check_nonpayable change_commission_function [Val_id.zero; U256.zero] in
      let$ () = check_nonpayable get_validator_function [Val_id.zero] in
      let$ () = check_nonpayable get_delegator_function [Val_id.zero; Address.zero] in
      let$ () = check_nonpayable get_withdrawal_request_function [Val_id.zero; Address.zero; U8.zero] in
      let$ () = check_nonpayable get_execution_validator_set_function [U32.zero] in
      let$ () = check_nonpayable get_snapshot_validator_set_function [U32.zero] in
      let$ () = check_nonpayable get_consensus_validator_set_function [U32.zero] in
      let$ () = check_nonpayable get_delegations_function [Address.zero; Val_id.zero] in
      let$ () = check_nonpayable get_delegators_function [Val_id.zero; Address.zero] in
      let$ () = check_nonpayable get_epoch_function [] in
      let$ () = check_nonpayable get_proposer_val_id_function [] in

      return () )

let test_auth_address_conflicts_with_linked_list () =
  run_from_initial_state ~compare_with:"auth_address_conflicts_with_linked_list"
    M.(
      (* Empty address. *)
      let$ () =
        expect_error Invalid_input
        <$> add_validator_wrapper ~auth_address:Address.zero ~stake:active_validator_stake ()
      in
      (* Sentinel address. *)
      let$ () =
        expect_error Invalid_input
        <$> add_validator_wrapper ~auth_address:Address.(make '\xff') ~stake:active_validator_stake ()
      in
      return () )

let test_linked_list_removal_state_override () =
  run_from_initial_state ~compare_with:"linked_list_removal_state_override"
    M.(
      (* Even though the empty address and the sentinel address are banned during delegate, a user could
       state override and trigger unreachable code during live execution via eth call. *)
      let$ () = Variables.epoch $= Epoch.of_int 10 in

      let sentinel = Address.make '\xff' in
      let stake = U256.(~$500 * mon) in

      (* State override invalid validator. *)
      let val_id = Val_id.one in
      let$ () =
        update_field
          (Storage.Loc.lens (Variables.val_execution val_id))
          (fun v -> {v with address_flags = Address_flags.{auth_address = sentinel; flags = ok}; stake})
      in

      (* State override that the contract can process this withdrawal. *)
      let$ () = update_field (TransactionState.balance staking_address) (fun bal -> U256.(bal + stake)) in

      (* State override the delegator. *)
      let$ () =
        update_field (Storage.Loc.lens (Variables.delegator (val_id, sentinel))) (fun d -> {d with stake})
      in

      let$ () =
        (* Here the C++ equivalent test throws an exception inside `undelegate`, and the state is not
           rolled back, so we use the same behavior, as that is what the fixture expects. *)
        expect_error Internal_error
        <$> call undelegate_function ~sender:sentinel ~on_error:`Keep [val_id; stake; U8.one]
      in

      return () )

(**** Add validator tests. ****)

let test_simple_add_validator () =
  let auth_address = address "0xdeadbeef" in
  (* Canonical calldata for a valid addValidator call, used as the base for byte surgery below. Post-selector
     layout: [ 3 offset words | len=165 | 192-byte padded message | len=64 | secp sig | len=96 | bls sig ],
     544 bytes in total. The message payload occupies [128..293), its zero padding [293..320), the secp and
     bls length words sit at offsets 320 and 416. *)
  let inputs, _ =
    craft_add_validator_input ~auth_address ~stake:active_validator_stake ~commission:U256.zero
      ~secret:B32.(of_hex_string "0x1000")
  in
  let msg =
    Abi.Signature.input_to_message ~prepend_selector:false ~gas:1_000_000L ~sender:auth_address
      ~value:active_validator_stake add_validator_function.signature ~recipient:staking_address
      ~memory_capacity:(Uint.to_uint32 Evm.Vm.Memory.max_memory_usage)
      inputs
  in
  let canonical = msg.input_data in
  let () = check int "canonical calldata length" 544 (Bytes.length canonical) in
  (* Overwrite the 32-byte word at [at..at+32) with the big-endian representation of [v]. *)
  let set_word (data : Bytes.t) ~(at : int) (v : U256.t) : Bytes.t =
    Bytes.(sub data 0 at ^ U256.to_repr_bytes v ^ sub data (at + 32) (length data - at - 32))
  in
  (* Send corrupted calldata from the initial state and discard the post-state: decode failures must not
     leak state, and the fixture comparison below only covers the successful call. *)
  let expect_decode_error name err (input_data : Bytes.t) =
    let result, _ = Function.send_message (Pack add_validator_function) {msg with input_data} initial_state in
    check status_code (name ^ ": status_code") Revert result.status_code ;
    check staking_error name err (error_of_output_string result.output_data)
  in

  (* Malformed inputs, stress-testing the raw decoder: tuple offset words are ignored, each length prefix
     must match the expected size exactly (compared as a full u256, and checked *before* the payload is
     read), payloads are consumed padded to 32 bytes, and leftover bytes are rejected. *)
  (* Head truncated mid-offsets: the first length word is out of bounds. *)
  let () = expect_decode_error "truncated head" Input_too_short Bytes.(sub canonical 0 64) in
  (* Offsets present but the message length word is missing. *)
  let () = expect_decode_error "missing length word" Input_too_short Bytes.(sub canonical 0 96) in
  (* Message length prefix off by one, payload intact. *)
  let () =
    expect_decode_error "message prefix 164" Length_mismatch (set_word canonical ~at:96 U256.(~$164))
  in
  (* Correct message prefix but the payload is cut short of its padded length. *)
  let () = expect_decode_error "message payload truncated" Input_too_short Bytes.(sub canonical 0 228) in
  (* Wrong prefix AND truncated payload: the prefix check must win (C++ checks it before the payload). *)
  let () =
    expect_decode_error "wrong prefix and truncated payload" Length_mismatch
      (set_word Bytes.(sub canonical 0 228) ~at:96 U256.(~$200))
  in
  (* A length prefix that does not fit in an int must still be a mismatch, not "input too short". *)
  let () =
    expect_decode_error "huge message prefix" Length_mismatch
      (set_word canonical ~at:96 U256.(shift_left one 100))
  in
  (* Wrong secp and bls signature length prefixes, everything else canonical. *)
  let () = expect_decode_error "secp prefix 63" Length_mismatch (set_word canonical ~at:320 U256.(~$63)) in
  let () = expect_decode_error "bls prefix 95" Length_mismatch (set_word canonical ~at:416 U256.(~$95)) in
  (* Unconsumed input: sub-word and word-aligned trailing bytes are both rejected. *)
  let () = expect_decode_error "one trailing byte" Invalid_input (canonical ^ "\xff") in
  let () = expect_decode_error "one trailing word" Invalid_input (canonical ^ B32.to_bytes B32.zeros) in

  (* First run: the canonical call, compared against the fixture. *)
  let () =
    run_from_initial_state ~compare_with:"simple_add_validator"
      M.(
        let$ {val_id; _} =
          expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ()
        in
        let$ _ = expect_some ~msg:"validator_exists" <$> !$(Variables.val_execution_opt val_id) in
        return () )
  in

  (* Second run: the same call made with garbage tuple offsets and non-zero message padding bytes. The
     decoder must ignore both, exactly as the C++ does; comparing against the same fixture proves the
     lenient decode is byte-for-byte equivalent to the canonical one. *)
  run_from_initial_state ~compare_with:"simple_add_validator"
    M.(
      let lenient =
        let garbage_offsets = Bytes.init 96 (fun _ -> '\xff') in
        let garbage_padding = Bytes.init 27 (fun _ -> '\xff') in
        Bytes.(
          garbage_offsets
          ^ sub canonical 96 (293 - 96)
          ^ garbage_padding
          ^ sub canonical 320 (length canonical - 320) )
      in
      let$ result = Function.send_message (Pack add_validator_function) {msg with input_data = lenient} in
      check status_code "lenient accept: status_code" Success result.status_code ;
      let val_id = Result.get_ok (Type.dec_bytes Val_id.t result.output_data) in
      (* Mirror add_validator_wrapper: credit the staked value to the contract. *)
      let$ () =
        update_field (staking_account |-- Account.balance) (fun bal -> U256.(bal + active_validator_stake))
      in
      let$ _ = expect_some ~msg:"validator_exists" <$> !$(Variables.val_execution_opt val_id) in
      return () )

let test_add_validator_sufficient_balance () =
  run_from_initial_state ~compare_with:"add_validator_sufficient_balance"
    M.(
      let auth_address = address "0xdeadbeef" in
      let other_address = address "0xdeaddead" in

      let$ {val_id = val1_id; sign_address = val1_sign} =
        expect_ok
        <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake
              ~secret:(B32.of_hex_string "0x1000") ()
      in

      let$ () = snapshot in

      let$ {val_id = val2_id; sign_address = val2_sign} =
        expect_ok
        <$> add_validator_wrapper ~auth_address:other_address ~stake:active_validator_stake
              ~secret:(B32.of_hex_string "0x1001") ()
      in

      let$ () = inc_epoch in

      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [val1_sign] in
      let$ () =
        let$ epoch_valset = expect_ok <$> get_this_epoch_valset in
        return (check int "List.length this_epoch_valset = 1" 1 (List.length epoch_valset))
      in
      let$ () = check_validator_flags "val_1.flags = Ok" Address_flags.ok val1_id in
      let$ () = check_validator_flags "val_2.flags = Ok" Address_flags.ok val2_id in

      let$ () = skip_to_next_epoch in

      let$ () =
        let$ epoch_valset = expect_ok <$> get_this_epoch_valset in
        return (check int "List.length this_epoch_valset = 2" 2 (List.length epoch_valset))
      in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [val2_sign] in
      let$ () = check_validator_flags "val_1.flags = ok" Address_flags.ok val1_id in
      let$ () = check_validator_flags "val_2.flags = ok" Address_flags.ok val2_id in

      let$ cv1 = expect_ok <$> get_this_epoch_view val1_id in
      check u256 "this_epoch_view(val_1).stake" active_validator_stake cv1.stake ;
      let$ cv2 = expect_ok <$> get_this_epoch_view val2_id in
      check u256 "this_epoch_view(val_2).stake" active_validator_stake cv2.stake ;

      let$ ve1 = !$(Variables.val_execution val1_id) in
      check u256 "val_1.stake" active_validator_stake ve1.stake ;
      let$ ve2 = !$(Variables.val_execution val2_id) in
      check u256 "val_2.stake" active_validator_stake ve2.stake ;
      check u256 "val_1.commission" U256.zero ve1.Val_execution.commission ;
      check u256 "val_2.commission" U256.zero ve2.Val_execution.commission ;

      return () )

let test_add_validator_insufficient_balance () =
  run_from_initial_state ~compare_with:"add_validator_insufficient_balance"
    M.(
      let auth_address = address "0xdeadbeef" in

      let$ {val_id = val1_id; sign_address = val1_sign} =
        expect_ok
        <$> add_validator_wrapper ~auth_address ~stake:min_auth_address_stake ~commission:U256.one
              ~secret:B32.(of_hex_string "0x1000")
              ()
      in

      let$ () = snapshot in
      let$ {val_id = val2_id; sign_address = val2_sign} =
        expect_ok
        <$> add_validator_wrapper ~auth_address
              ~stake:U256.(active_validator_stake - one)
              ~commission:U256.(~$2)
              ~secret:B32.(of_hex_string "0x1001")
              ()
      in

      let$ () = inc_epoch in

      let$ () = expect_error Not_in_validator_set <$> syscall syscall_reward_function [val1_sign] in

      let$ () =
        check int "List.length this_epoch_valset = 0" 0
        <$> (List.length <$> (expect_ok <$> get_this_epoch_valset))
      in
      let$ () = check_validator_flags "val_1.flags = stake_too_low" Address_flags.stake_too_low val1_id in
      let$ () = check_validator_flags "val_2.flags = stake_too_low" Address_flags.stake_too_low val2_id in

      let$ () = skip_to_next_epoch in

      let$ () = expect_error Not_in_validator_set <$> syscall syscall_reward_function [val2_sign] in

      let$ () =
        check int "List.length this_epoch_valset = 0" 0
        <$> (List.length <$> (expect_ok <$> get_this_epoch_valset))
      in
      let$ () = check_validator_flags "val_1.flags = stake_too_low" Address_flags.stake_too_low val1_id in
      let$ () = check_validator_flags "val_2.flags = stake_too_low" Address_flags.stake_too_low val2_id in
      let$ () =
        let$ {stake; commission; _} = !$(Variables.val_execution val1_id) in
        check u256 "val1_stake" min_auth_address_stake stake ;
        check u256 "val1_commission" U256.one commission ;
        return ()
      in
      let$ () =
        let$ {stake; commission; _} = !$(Variables.val_execution val2_id) in
        check u256 "val2_stake" U256.(active_validator_stake - one) stake ;
        check u256 "val2_commission" U256.(~$2) commission ;
        return ()
      in

      return () )

let test_add_validator_active_stake_fork () =
  run_from_initial_state ~compare_with:"add_validator_active_stake_fork"
    M.(
      let$ {val_id; _} =
        expect_ok
        <$> add_validator_wrapper ~auth_address:(address "0xdeadbeef") ~stake:U256.(~$15_000_000 * mon) ()
      in
      let$ () = skip_to_next_epoch in

      (* The spec does not implement old forks so only the >= MONAD_FIVE branch is tested here. *)
      let$ () =
        let vs = Storage.Array.read_to_list Variables.valset_execution in
        check int "valset_execution length" 1 <$> (List.length <$> vs)
      in
      let$ () =
        check int "this_epoch_valset length" 1 <$> (List.length <$> (expect_ok <$> get_this_epoch_valset))
      in
      let$ () = check_validator_flags "val_execution(val_id).flags = Ok" Address_flags.ok val_id in

      return () )

(**** Validator tests. ****)

let test_validator_delegate_before_active () =
  run_from_initial_state ~compare_with:"validator_delegate_before_active"
    M.(
      let auth_address = address "0xdeadbeef" in
      let other_address = address "0xdeaddead" in

      let$ {val_id = val1_id; _} =
        expect_ok
        <$> add_validator_wrapper ~auth_address ~stake:min_auth_address_stake ~commission:U256.zero
              ~secret:(B32.of_hex_string "0x1000") ()
      in

      let$ _ = expect_ok <$> delegate_and_credit val1_id ~sender:auth_address ~value:active_validator_stake in

      let$ () = snapshot in

      let$ {val_id = val2_id; _} =
        expect_ok
        <$> add_validator_wrapper ~auth_address:other_address ~stake:min_auth_address_stake
              ~commission:U256.zero ~secret:(B32.of_hex_string "0x1001") ()
      in
      let$ _ = expect_ok <$> delegate_and_credit val2_id ~sender:auth_address ~value:active_validator_stake in

      let$ () = inc_epoch in
      let$ () = skip_to_next_epoch in

      (* Check val info. *)
      let$ () = check_validator_flags "val1.flags" Address_flags.ok val1_id in
      let$ () =
        check_validator_stake "val1.stake" U256.(active_validator_stake + min_auth_address_stake) val1_id
      in
      let$ () = check_validator_flags "val2.flags" Address_flags.ok val2_id in
      let$ () =
        check_validator_stake "val2.stake" U256.(active_validator_stake + min_auth_address_stake) val2_id
      in

      (* Check delegator. *)
      let$ () =
        check_delegator_state ~val_id:val1_id ~delegator:auth_address
          ~expected_stake:U256.(active_validator_stake + min_auth_address_stake)
          ~expected_rewards:U256.zero
      in
      let$ () =
        check_delegator_state ~val_id:val2_id ~delegator:auth_address ~expected_stake:active_validator_stake
          ~expected_rewards:U256.zero
      in
      let$ () =
        check_delegator_state ~val_id:val2_id ~delegator:other_address ~expected_stake:min_auth_address_stake
          ~expected_rewards:U256.zero
      in
      return () )

let test_validator_multiple_delegations () =
  run_from_initial_state ~compare_with:"validator_multiple_delegations"
    M.(
      (* Epoch 1. *)
      let auth_address = address "0xdeadbeef" in
      let$ {val_id; sign_address} =
        expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ()
      in

      (* Epoch 2. *)
      let$ () = skip_to_next_epoch in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      let$ () =
        check_delegator_state ~val_id ~delegator:auth_address ~expected_stake:active_validator_stake
          ~expected_rewards:reward
      in

      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:auth_address ~value:min_auth_address_stake in

      let$ () = snapshot in

      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () =
        check_delegator_state ~val_id ~delegator:auth_address ~expected_stake:active_validator_stake
          ~expected_rewards:U256.(~$2 * reward)
      in
      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:auth_address ~value:min_auth_address_stake in

      (* Epoch 3. *)
      let$ () = inc_epoch in

      let$ () =
        check_delegator_state ~val_id ~delegator:auth_address
          ~expected_stake:U256.(active_validator_stake + min_auth_address_stake)
          ~expected_rewards:U256.(~$2 * reward)
      in
      (* Epoch 4. *)
      let$ () = skip_to_next_epoch in
      let$ () =
        check_delegator_state ~val_id ~delegator:auth_address
          ~expected_stake:U256.(active_validator_stake + (~$2 * min_auth_address_stake))
          ~expected_rewards:U256.(~$2 * reward)
      in
      return () )

let test_validator_compound () =
  run_from_initial_state ~compare_with:"validator_compound"
    M.(
      (* Epoch 1. *)
      let auth_address = address "0xdeadbeef" in
      let$ {val_id; sign_address} =
        expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ()
      in

      (* Epoch 2. *)
      let$ () = skip_to_next_epoch in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      let$ () =
        check_delegator_state ~val_id ~delegator:auth_address ~expected_stake:active_validator_stake
          ~expected_rewards:reward
      in

      let$ _ = expect_ok <$> call compound_function ~sender:auth_address [val_id] in

      let$ () = snapshot in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      let$ () =
        check_delegator_state ~val_id ~delegator:auth_address ~expected_stake:active_validator_stake
          ~expected_rewards:reward
      in

      let$ _ = expect_ok <$> call compound_function ~sender:auth_address [val_id] in

      (* Epoch 3. *)
      let$ () = inc_epoch in

      let$ () =
        check_delegator_state ~val_id ~delegator:auth_address
          ~expected_stake:U256.(active_validator_stake + reward)
          ~expected_rewards:U256.zero
      in
      (* Epoch 4. *)
      let$ () = skip_to_next_epoch in
      let$ () =
        check_delegator_state ~val_id ~delegator:auth_address
          ~expected_stake:U256.(active_validator_stake + (~$2 * reward))
          ~expected_rewards:U256.zero
      in
      return () )

let test_validator_undelegate () =
  run_from_initial_state ~compare_with:"validator_undelegate"
    M.(
      (* Epoch 1. *)
      let auth_address = address "0xdeadbeef" in
      let other_address = address "0xdeaddead" in
      let withdrawal_id = U8.one in

      let$ {val_id = val1_id; _} =
        expect_ok
        <$> add_validator_wrapper ~auth_address ~stake:min_auth_address_stake ~commission:U256.zero
              ~secret:(B32.of_hex_string "0x1000") ()
      in

      let$ _ = expect_ok <$> delegate_and_credit val1_id ~sender:auth_address ~value:min_auth_address_stake in

      let$ () = snapshot in

      let$ {val_id = val2_id; _} =
        expect_ok
        <$> add_validator_wrapper ~auth_address:other_address ~stake:min_auth_address_stake
              ~commission:U256.zero ~secret:(B32.of_hex_string "0x1001") ()
      in

      let$ _ = expect_ok <$> delegate_and_credit val2_id ~sender:auth_address ~value:active_validator_stake in

      let$ () = inc_epoch in
      let$ () = skip_to_next_epoch in
      let$ () = skip_to_next_epoch in

      let$ _ =
        expect_ok <$> call undelegate_function ~sender:auth_address [val1_id; min_auth_address_stake; U8.one]
      in
      let$ _ =
        expect_ok <$> call undelegate_function ~sender:auth_address [val1_id; min_auth_address_stake; U8.(~$2)]
      in
      let$ _ =
        expect_ok
        <$> call undelegate_function ~sender:auth_address
              [val2_id; U256.(active_validator_stake / ~$2); U8.one]
      in
      let$ _ =
        expect_ok
        <$> call undelegate_function ~sender:auth_address
              [val2_id; U256.(active_validator_stake / ~$2); U8.(~$2)]
      in
      let$ () =
        check_validator_flags "val1.flags = Withdrawn | StakeTooLow"
          Address_flags.(U64.logor stake_too_low withdrawn)
          val1_id
      in

      let$ () = skip_to_next_epoch in
      let$ () = skip_to_next_epoch in

      let$ _ = expect_ok <$> call withdraw_function ~sender:auth_address [val1_id; withdrawal_id] in
      let$ _ = expect_ok <$> call withdraw_function ~sender:auth_address [val2_id; withdrawal_id] in

      (* Check val info. *)
      let$ () =
        check_validator_flags "val1.flags = Withdrawn | StakeTooLow"
          Address_flags.(U64.logor stake_too_low withdrawn)
          val1_id
      in
      let$ () = check_validator_stake "val1.stake = 0" U256.zero val1_id in
      let$ () = check_validator_flags "val2.flags = StakeTooLow" Address_flags.stake_too_low val2_id in
      let$ () = check_validator_stake "val2.stake = min_validate_stake" min_auth_address_stake val2_id in

      let$ () =
        check_delegator_state ~val_id:val1_id ~delegator:auth_address ~expected_stake:U256.zero
          ~expected_rewards:U256.zero
      in
      let$ () =
        check_delegator_state ~val_id:val2_id ~delegator:auth_address ~expected_stake:U256.zero
          ~expected_rewards:U256.zero
      in
      let$ () =
        check_delegator_state ~val_id:val2_id ~delegator:other_address ~expected_stake:min_auth_address_stake
          ~expected_rewards:U256.zero
      in

      return () )

let test_validator_exit_via_validator () =
  run_from_initial_state ~compare_with:"validator_exit_via_validator"
    M.(
      let auth_address = address "0xdeadbeef" in
      let other_address = address "0xdeaddead" in
      let withdrawal_id = U8.one in

      let$ {val_id = val1_id; _} =
        expect_ok
        <$> add_validator_wrapper ~auth_address ~stake:min_auth_address_stake ~commission:U256.zero
              ~secret:(B32.of_hex_string "0x1000") ()
      in

      let$ _ = expect_ok <$> delegate_and_credit val1_id ~sender:auth_address ~value:active_validator_stake in

      let$ () = snapshot in

      let$ {val_id = val2_id; _} =
        expect_ok
        <$> add_validator_wrapper ~auth_address:other_address ~stake:min_auth_address_stake
              ~commission:U256.zero ~secret:(B32.of_hex_string "0x1001") ()
      in

      let$ _ = expect_ok <$> delegate_and_credit val2_id ~sender:auth_address ~value:active_validator_stake in

      let$ () = inc_epoch in
      let$ () = skip_to_next_epoch in
      let$ () = skip_to_next_epoch in

      let$ _ =
        expect_ok
        <$> call undelegate_function ~sender:auth_address
              [val1_id; U256.(active_validator_stake + min_auth_address_stake - one); withdrawal_id]
      in
      let$ _ =
        expect_ok
        <$> call undelegate_function ~sender:other_address [val2_id; min_auth_address_stake; withdrawal_id]
      in

      let$ _ =
        expect_ok
        <$> delegate_and_credit val1_id ~sender:auth_address
              ~value:U256.(active_validator_stake + min_auth_address_stake - one)
      in

      let$ () = skip_to_next_epoch in

      let$ () =
        check int "this_epoch_valset length" 1 <$> (List.length <$> (expect_ok <$> get_this_epoch_valset))
      in

      let$ _ =
        expect_ok <$> delegate_and_credit val2_id ~sender:other_address ~value:min_auth_address_stake
      in

      let$ () = skip_to_next_epoch in

      let$ () =
        check int "this_epoch_valset length" 2 <$> (List.length <$> (expect_ok <$> get_this_epoch_valset))
      in
      let$ () = skip_to_next_epoch in

      let$ _ = expect_ok <$> call withdraw_function ~sender:auth_address [val1_id; withdrawal_id] in
      let$ _ = expect_ok <$> call withdraw_function ~sender:other_address [val2_id; withdrawal_id] in
      return () )

let test_validator_exit_via_delegator () =
  run_from_initial_state ~compare_with:"validator_exit_via_delegator"
    M.(
      let auth_address = address "0xdeadbeef" in
      let other_address = address "0xdeaddead" in
      let withdrawal_id = U8.one in

      let$ {val_id = val1_id; _} =
        expect_ok
        <$> add_validator_wrapper ~auth_address ~stake:min_auth_address_stake ~commission:U256.zero
              ~secret:(B32.of_hex_string "0x1000") ()
      in

      let$ _ = expect_ok <$> delegate_and_credit val1_id ~sender:auth_address ~value:active_validator_stake in

      let$ () = snapshot in

      let$ {val_id = val2_id; _} =
        expect_ok
        <$> add_validator_wrapper ~auth_address:other_address ~stake:min_auth_address_stake
              ~commission:U256.zero ~secret:(B32.of_hex_string "0x1001") ()
      in

      let$ _ = expect_ok <$> delegate_and_credit val2_id ~sender:auth_address ~value:active_validator_stake in

      let$ () = inc_epoch in
      let$ () = skip_to_next_epoch in
      let$ () = skip_to_next_epoch in

      let$ _ =
        expect_ok
        <$> call undelegate_function ~sender:auth_address [val1_id; active_validator_stake; withdrawal_id]
      in
      let$ _ =
        expect_ok
        <$> call undelegate_function ~sender:auth_address [val2_id; active_validator_stake; withdrawal_id]
      in

      let$ _ = expect_ok <$> delegate_and_credit val1_id ~sender:auth_address ~value:active_validator_stake in

      let$ () = skip_to_next_epoch in

      let$ () =
        check int "this_epoch_valset length" 1 <$> (List.length <$> (expect_ok <$> get_this_epoch_valset))
      in

      let$ _ = expect_ok <$> delegate_and_credit val2_id ~sender:auth_address ~value:active_validator_stake in

      let$ () = skip_to_next_epoch in

      let$ () =
        check int "this_epoch_valset length" 2 <$> (List.length <$> (expect_ok <$> get_this_epoch_valset))
      in
      let$ () = skip_to_next_epoch in

      let$ _ = expect_ok <$> call withdraw_function ~sender:auth_address [val1_id; withdrawal_id] in
      let$ _ = expect_ok <$> call withdraw_function ~sender:auth_address [val2_id; withdrawal_id] in
      return () )

(* The equivalent C++ test runs on the MONAD_FOUR fork (active stake 25M MON). This version was constructed
   by retargeting the C++ to MONAD_EIGHT. *)
let test_validator_exit_multiple_delegations () =
  run_from_initial_state ~compare_with:"validator_exit_multiple_delegations"
    M.(
      let auth_address = address "0xdeadbeef" in
      let other_address = address "0xdeaddead" in
      let withdrawal_id = U8.one in
      let half_stake = U256.(active_validator_stake / ~$2) in

      let$ () = check u256 "auth balance" U256.zero <$> !(TransactionState.balance auth_address) in

      let$ {val_id = val1_id; sign_address = val1_sign} =
        expect_ok
        <$> add_validator_wrapper ~auth_address ~stake:min_auth_address_stake ~commission:U256.zero
              ~secret:(B32.of_hex_string "0x1000") ()
      in

      let$ _ = expect_ok <$> delegate_and_credit val1_id ~sender:auth_address ~value:half_stake in
      let$ _ = expect_ok <$> delegate_and_credit val1_id ~sender:auth_address ~value:half_stake in

      let$ () = snapshot in

      let$ {val_id = val2_id; sign_address = val2_sign} =
        expect_ok
        <$> add_validator_wrapper ~auth_address:other_address ~stake:min_auth_address_stake
              ~commission:U256.zero ~secret:(B32.of_hex_string "0x1001") ()
      in

      let$ _ = expect_ok <$> delegate_and_credit val2_id ~sender:auth_address ~value:half_stake in
      let$ _ = expect_ok <$> delegate_and_credit val2_id ~sender:auth_address ~value:half_stake in

      let$ () = inc_epoch in
      let$ () = skip_to_next_epoch in

      let$ () =
        check int "this_epoch_valset length" 2 <$> (List.length <$> (expect_ok <$> get_this_epoch_valset))
      in

      (* Undelegate the delegated stake from both validators before the rewards land: the rewards accrue to
         the withdrawal requests (and to the auth delegators' remaining live stake), not to the undelegated
         positions. *)
      let$ _ =
        expect_ok
        <$> call undelegate_function ~sender:auth_address [val1_id; active_validator_stake; withdrawal_id]
      in
      let$ _ =
        expect_ok
        <$> call undelegate_function ~sender:auth_address [val2_id; active_validator_stake; withdrawal_id]
      in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [val1_sign] in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [val2_sign] in

      (* Re-delegate to exactly one wei below the active threshold: neither validator may re-enter the
         valset. *)
      let one_wei_below = U256.(active_validator_stake - min_auth_address_stake - ~$1) in
      let$ _ = expect_ok <$> delegate_and_credit val1_id ~sender:auth_address ~value:one_wei_below in

      let$ () = snapshot in

      let$ _ = expect_ok <$> delegate_and_credit val2_id ~sender:auth_address ~value:one_wei_below in

      let$ () = inc_epoch in
      let$ () = skip_to_next_epoch in

      let$ () =
        check int "this_epoch_valset length" 0 <$> (List.length <$> (expect_ok <$> get_this_epoch_valset))
      in

      let$ () = check u256 "auth balance" U256.zero <$> !(TransactionState.balance auth_address) in
      (* Auth had no live stake in val2 at reward time, so there is nothing to claim... *)
      let$ _ = expect_ok <$> call claim_rewards_function ~sender:auth_address [val2_id] in
      let$ () =
        check u256 "auth balance after claim val2" U256.zero <$> !(TransactionState.balance auth_address)
      in
      (* ...but the withdrawal request accrued rewards until its withdrawal epoch. *)
      let$ _ = expect_ok <$> call withdraw_function ~sender:auth_address [val2_id; withdrawal_id] in
      let$ () =
        check u256 "auth balance after withdraw val2" U256.(active_validator_stake + ~@"990099009900990099")
        <$> !(TransactionState.balance auth_address)
      in

      let$ _ = expect_ok <$> call claim_rewards_function ~sender:other_address [val2_id] in
      let$ () =
        check u256 "other balance after claim val2" U256.(~@"9900990099009900")
        <$> !(TransactionState.balance other_address)
      in

      (* Auth is val1's auth delegator, so it owns both the live 100k position (paid by claim_rewards) and
         the 10M withdrawal (paid by withdraw): together they receive the full reward minus 1 wei of
         flooring dust. *)
      let$ _ = expect_ok <$> call claim_rewards_function ~sender:auth_address [val1_id] in
      let$ _ = expect_ok <$> call withdraw_function ~sender:auth_address [val1_id; withdrawal_id] in
      let$ () =
        check u256 "auth balance after exiting val1"
          U256.(active_validator_stake + (reward - ~$1) + active_validator_stake + ~@"990099009900990099")
        <$> !(TransactionState.balance auth_address)
      in
      return () )

(* Like validator_exit_multiple_delegations, ported from the MONAD_FOUR C++ test by retargetting the C++
   to MONAD_EIGHT. *)
let test_validator_exit_multiple_delegations_full_withdrawal () =
  run_from_initial_state ~compare_with:"validator_exit_multiple_delegations_full_withdrawal"
    M.(
      let smaller_stake = U256.(~$1_000_000 * mon) in
      let auth_address = address "0xdeadbeef" in
      let other_address = address "0xdeaddead" in
      let withdrawal_id = U8.one in
      let half_stake = U256.(active_validator_stake / ~$2) in

      let$ () = check u256 "auth balance" U256.zero <$> !(TransactionState.balance auth_address) in

      let$ {val_id = val1_id; sign_address = val1_sign} =
        expect_ok
        <$> add_validator_wrapper ~auth_address ~stake:smaller_stake ~commission:U256.zero
              ~secret:(B32.of_hex_string "0x1000") ()
      in

      let$ _ = expect_ok <$> delegate_and_credit val1_id ~sender:auth_address ~value:half_stake in
      let$ _ = expect_ok <$> delegate_and_credit val1_id ~sender:auth_address ~value:half_stake in

      let$ () = snapshot in

      let$ {val_id = val2_id; sign_address = val2_sign} =
        expect_ok
        <$> add_validator_wrapper ~auth_address:other_address ~stake:smaller_stake ~commission:U256.zero
              ~secret:(B32.of_hex_string "0x1001") ()
      in

      let$ _ = expect_ok <$> delegate_and_credit val2_id ~sender:auth_address ~value:half_stake in
      let$ _ = expect_ok <$> delegate_and_credit val2_id ~sender:auth_address ~value:half_stake in

      let$ () = inc_epoch in
      let$ () = skip_to_next_epoch in

      let$ () =
        check int "this_epoch_valset length" 2 <$> (List.length <$> (expect_ok <$> get_this_epoch_valset))
      in

      (* val1 is undelegated before its reward; val2 is rewarded before its undelegation. *)
      let$ _ =
        expect_ok
        <$> call undelegate_function ~sender:auth_address [val1_id; active_validator_stake; withdrawal_id]
      in

      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [val1_sign] in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [val2_sign] in

      let$ _ =
        expect_ok
        <$> call undelegate_function ~sender:auth_address [val2_id; active_validator_stake; withdrawal_id]
      in

      (* Re-delegate to exactly one wei below the active threshold: neither validator may re-enter the
         valset. *)
      let one_wei_below = U256.(active_validator_stake - smaller_stake - ~$1) in
      let$ _ = expect_ok <$> delegate_and_credit val1_id ~sender:auth_address ~value:one_wei_below in

      let$ () = snapshot in

      let$ _ = expect_ok <$> delegate_and_credit val2_id ~sender:auth_address ~value:one_wei_below in

      let$ () = inc_epoch in
      let$ () = skip_to_next_epoch in

      let$ () =
        check int "this_epoch_valset length" 0 <$> (List.length <$> (expect_ok <$> get_this_epoch_valset))
      in

      let$ () = check u256 "auth balance" U256.zero <$> !(TransactionState.balance auth_address) in
      (* val2: the claim pays the live position's reward share; the withdrawal pays back exactly the
         undelegated principal (its request accrued nothing, having been created after the reward). *)
      let$ _ = expect_ok <$> call claim_rewards_function ~sender:auth_address [val2_id] in
      let$ _ = expect_ok <$> call withdraw_function ~sender:auth_address [val2_id; withdrawal_id] in
      let$ () =
        check u256 "auth balance after exiting val2" U256.(active_validator_stake + ~@"909090909090909090")
        <$> !(TransactionState.balance auth_address)
      in

      let$ _ = expect_ok <$> call claim_rewards_function ~sender:other_address [val2_id] in
      let$ () =
        check u256 "other balance after claim val2" U256.(~@"90909090909090909")
        <$> !(TransactionState.balance other_address)
      in

      (* val1: the claim pays the live 1M position's share, the withdrawal pays the principal plus the
         request's share; together the full reward minus 1 wei of flooring dust. *)
      let$ _ = expect_ok <$> call claim_rewards_function ~sender:auth_address [val1_id] in
      let$ _ = expect_ok <$> call withdraw_function ~sender:auth_address [val1_id; withdrawal_id] in
      let$ () =
        check u256 "auth balance after exiting val1"
          U256.(active_validator_stake + (reward - ~$1) + active_validator_stake + ~@"909090909090909090")
        <$> !(TransactionState.balance auth_address)
      in

      (* check_delegator_state pulls the delegator up to date (a getDelegator call) and therefore mutates
         storage, exactly like the C++ check_delegator_c_state helper — keep these at the same point in the
         sequence. *)
      let$ () =
        check_delegator_state ~val_id:val1_id ~delegator:auth_address
          ~expected_stake:U256.(active_validator_stake - ~$1)
          ~expected_rewards:U256.zero
      in
      let$ () =
        check_delegator_state ~val_id:val2_id ~delegator:auth_address
          ~expected_stake:U256.(active_validator_stake - smaller_stake - ~$1)
          ~expected_rewards:U256.zero
      in
      let$ () =
        check_delegator_state ~val_id:val2_id ~delegator:other_address ~expected_stake:smaller_stake
          ~expected_rewards:U256.zero
      in

      (* Full withdrawal: undelegate the entire remaining positions, re-using withdrawal id 1 (the first
         requests were withdrawn and cleared above). *)
      let$ _ =
        expect_ok
        <$> call undelegate_function ~sender:auth_address
              [val1_id; U256.(active_validator_stake - ~$1); withdrawal_id]
      in
      let$ _ =
        expect_ok
        <$> call undelegate_function ~sender:auth_address
              [val2_id; U256.(active_validator_stake - smaller_stake - ~$1); withdrawal_id]
      in

      let$ () = skip_to_next_epoch in
      let$ () = skip_to_next_epoch in
      let$ () = skip_to_next_epoch in
      let$ () = skip_to_next_epoch in

      (* No rewards landed since the last claims: the final claims pay nothing and the withdrawals return
         exactly the undelegated principals. *)
      let$ _ = expect_ok <$> call claim_rewards_function ~sender:auth_address [val2_id] in
      let$ _ = expect_ok <$> call withdraw_function ~sender:auth_address [val2_id; withdrawal_id] in

      let$ _ = expect_ok <$> call claim_rewards_function ~sender:other_address [val2_id] in
      let$ () =
        check u256 "other balance unchanged" U256.(~@"90909090909090909")
        <$> !(TransactionState.balance other_address)
      in

      let$ _ = expect_ok <$> call claim_rewards_function ~sender:auth_address [val1_id] in
      let$ _ = expect_ok <$> call withdraw_function ~sender:auth_address [val1_id; withdrawal_id] in
      let$ () =
        check u256 "auth balance after full withdrawal"
          U256.(
            active_validator_stake
            + (reward - ~$1)
            + active_validator_stake
            + ~@"909090909090909090"
            + (active_validator_stake - ~$1)
            + (active_validator_stake - smaller_stake - ~$1) )
        <$> !(TransactionState.balance auth_address)
      in
      return () )

let test_validator_exit_claim_rewards () =
  run_from_initial_state ~compare_with:"validator_exit_claim_rewards"
    M.(
      let auth_address = address "0xdeadbeef" in
      let other_address = address "0xdeaddead" in

      let smaller_stake = U256.(~$1_000_000 * mon) in
      let larger_stake = U256.(~$50_000_000 * mon) in
      let$ {val_id = val1_id; sign_address = val1_sign} =
        expect_ok
        <$> add_validator_wrapper ~auth_address ~stake:smaller_stake ~commission:U256.zero
              ~secret:(B32.of_hex_string "0x1000") ()
      in

      let$ _ = expect_ok <$> delegate_and_credit val1_id ~sender:auth_address ~value:larger_stake in

      let$ () = snapshot in

      let$ {val_id = val2_id; sign_address = val2_sign} =
        expect_ok
        <$> add_validator_wrapper ~auth_address:other_address ~stake:smaller_stake ~commission:U256.zero
              ~secret:(B32.of_hex_string "0x1001") ()
      in

      let$ _ = expect_ok <$> delegate_and_credit val2_id ~sender:auth_address ~value:larger_stake in

      let$ () = inc_epoch in
      let$ () = skip_to_next_epoch in
      let$ () = skip_to_next_epoch in

      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [val1_sign] in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [val2_sign] in

      let$ _ = expect_ok <$> call undelegate_function ~sender:auth_address [val1_id; larger_stake; U8.one] in
      let$ _ = expect_ok <$> call undelegate_function ~sender:auth_address [val2_id; larger_stake; U8.one] in

      let$ () = skip_to_next_epoch in

      let$ () =
        check int "this_epoch_valset length" 0 <$> (List.length <$> (expect_ok <$> get_this_epoch_valset))
      in

      let$ () = check u256 "auth balance" U256.zero <$> !(TransactionState.balance auth_address) in
      let$ _ = expect_ok <$> call claim_rewards_function ~sender:auth_address [val1_id] in
      let$ () =
        check u256 "auth balance after claim val1" U256.(reward - ~$1)
        <$> !(TransactionState.balance auth_address)
      in
      let$ _ = expect_ok <$> call claim_rewards_function ~sender:auth_address [val2_id] in
      let$ () =
        check u256 "auth balance after claim val2" U256.(~@"980392156862745098" + (reward - ~$1))
        <$> !(TransactionState.balance auth_address)
      in

      let$ () = check u256 "other balance" U256.zero <$> !(TransactionState.balance other_address) in
      let$ _ = expect_ok <$> call claim_rewards_function ~sender:other_address [val2_id] in
      let$ () =
        check u256 "other balance after claim val2" U256.(~@"19607843137254901")
        <$> !(TransactionState.balance other_address)
      in
      return () )

let test_validator_exit_compound () =
  run_from_initial_state ~compare_with:"validator_exit_compound"
    M.(
      let smaller_stake = U256.(~$1_000_000 * mon) in
      let larger_stake = U256.(~$50_000_000 * mon) in
      let auth_address = address "0xdeadbeef" in
      let other_address = address "0xdeaddead" in
      let reward = U256.(~$60 * mon) in

      let$ {val_id = val1_id; sign_address = val1_sign} =
        expect_ok
        <$> add_validator_wrapper ~auth_address ~stake:smaller_stake ~commission:U256.zero
              ~secret:(B32.of_hex_string "0x1000") ()
      in

      let$ _ = expect_ok <$> delegate_and_credit val1_id ~sender:auth_address ~value:larger_stake in

      let$ () = snapshot in

      let$ {val_id = val2_id; sign_address = val2_sign} =
        expect_ok
        <$> add_validator_wrapper ~auth_address:other_address ~stake:smaller_stake ~commission:U256.zero
              ~secret:(B32.of_hex_string "0x1001") ()
      in

      let$ _ = expect_ok <$> delegate_and_credit val2_id ~sender:auth_address ~value:larger_stake in

      let$ () = inc_epoch in
      let$ () = skip_to_next_epoch in
      let$ () = skip_to_next_epoch in

      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [val1_sign] in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [val2_sign] in

      let$ _ = expect_ok <$> call compound_function ~sender:auth_address [val1_id] in
      let$ _ = expect_ok <$> call compound_function ~sender:auth_address [val2_id] in
      let$ _ = expect_ok <$> call compound_function ~sender:other_address [val2_id] in

      let$ _ = expect_ok <$> call undelegate_function ~sender:auth_address [val1_id; larger_stake; U8.one] in
      let$ _ = expect_ok <$> call undelegate_function ~sender:auth_address [val2_id; larger_stake; U8.one] in

      let$ () = skip_to_next_epoch in

      let$ () =
        check int "this_epoch_valset length" 0 <$> (List.length <$> (expect_ok <$> get_this_epoch_valset))
      in
      let$ _ = expect_ok <$> call claim_rewards_function ~sender:auth_address [val1_id] in
      let$ _ = expect_ok <$> call claim_rewards_function ~sender:auth_address [val2_id] in
      let$ _ = expect_ok <$> call claim_rewards_function ~sender:other_address [val2_id] in

      let$ () = check u256 "auth balance" U256.zero <$> !(TransactionState.balance auth_address) in
      let$ () = check u256 "other balance" U256.zero <$> !(TransactionState.balance other_address) in

      let expected_reward1 = U256.(~@"1176470588235294117") in
      let expected_reward2 = U256.(~@"58823529411764705882") in
      assert' "expected_reward1 + expected_reward2 <= reward"
        U256.(expected_reward1 + expected_reward2 <= reward) ;
      let$ () =
        check_delegator_state ~val_id:val2_id ~delegator:other_address
          ~expected_stake:U256.(smaller_stake + expected_reward1)
          ~expected_rewards:U256.zero
      in

      let$ () =
        check_delegator_state ~val_id:val2_id ~delegator:auth_address ~expected_stake:expected_reward2
          ~expected_rewards:U256.zero
      in

      let$ () =
        check_delegator_state ~val_id:val1_id ~delegator:auth_address
          ~expected_stake:U256.(smaller_stake + reward - ~$1)
          ~expected_rewards:U256.zero
      in
      return () )

let test_validator_activation_via_delegate () =
  run_from_initial_state ~compare_with:"validator_activation_via_delegate"
    M.(
      let auth_address = address "0xdeadbeef" in

      (* Create, minimum amount of stake to be a validator, but less than the
         amount required to be put in the valset. *)
      let$ {val_id; _} = expect_ok <$> add_validator_wrapper ~auth_address ~stake:min_auth_address_stake () in
      let$ () = check_validator_flags "val.flags" Address_flags.stake_too_low val_id in
      let$ () = skip_to_next_epoch in
      let$ () =
        check int "this_epoch_valset empty" 0 <$> (List.length <$> (expect_ok <$> get_this_epoch_valset))
      in

      (* A delegator stakes enough to activate the validator. *)
      let$ _ =
        expect_ok <$> delegate_and_credit val_id ~sender:(address "0xabab") ~value:active_validator_stake
      in
      let$ () = check_validator_flags "val.flags" Address_flags.ok val_id in
      let$ () = skip_to_next_epoch in
      let$ () =
        check int "this_epoch_valset length" 1 <$> (List.length <$> (expect_ok <$> get_this_epoch_valset))
      in

      (* Undelegate, once again deactivating this validator. *)
      let$ _ =
        expect_ok
        <$> call undelegate_function ~sender:(address "0xabab") [val_id; active_validator_stake; U8.one]
      in
      let$ () = check_validator_flags "val.flags" Address_flags.stake_too_low val_id in
      let$ () = skip_to_next_epoch in
      let$ () =
        check int "this_epoch_valset empty" 0 <$> (List.length <$> (expect_ok <$> get_this_epoch_valset))
      in
      return () )

let test_validator_undelegates_and_redelegates_in_epoch_delay_period () =
  run_from_initial_state ~compare_with:"validator_undelegates_and_redelegates_in_epoch_delay_period"
    M.(
      let auth_address = address "0xdeadbeef" in
      let$ {val_id; _} = expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake () in

      (* Activate validator. *)
      let$ () = skip_to_next_epoch in

      (* Undelegate everything, deactivating him. *)
      let$ _ =
        expect_ok <$> call undelegate_function ~sender:auth_address [val_id; active_validator_stake; U8.one]
      in
      let$ () = pull_delegator_up_to_date val_id auth_address in
      let$ () =
        check_validator_flags "val.flags"
          U64.(logor Address_flags.withdrawn Address_flags.stake_too_low)
          val_id
      in
      let$ () = snapshot in

      let$ vs = Storage.Array.read_to_list Variables.valset_consensus in
      check int "valset_consensus length" 0 (List.length vs) ;

      (* Redelegate during boundary. *)
      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:auth_address ~value:active_validator_stake in
      let$ () = inc_epoch in

      (* Next epoch, this validator should be reactivated. *)
      let$ () = skip_to_next_epoch in
      let$ vs = Storage.Array.read_to_list Variables.valset_consensus in
      check int "valset_consensus length" 1 (List.length vs) ;
      check validator_id "valset_consensus[0]" val_id (List.nth vs 0) ;
      return () )

let test_validator_joins_in_epoch_delay_period () =
  run_from_initial_state ~compare_with:"validator_joins_in_epoch_delay_period"
    M.(
      let auth_address = address "0xdeadbeef" in
      let$ () = snapshot in
      let$ {val_id; _} = expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake () in
      let$ () = inc_epoch in

      (* Validator should be active. *)
      let$ () = skip_to_next_epoch in
      let$ vs = Storage.Array.read_to_list Variables.valset_consensus in
      check int "valset_consensus length" 1 (List.length vs) ;
      check validator_id "valset_consensus[0]" val_id (List.nth vs 0) ;
      return () )

let test_validator_compound_before_active () =
  run_from_initial_state ~compare_with:"validator_compound_before_active"
    M.(
      let auth_address = address "0xdeadbeef" in
      let other_address = address "0xdeaddead" in

      let$ {val_id = val1_id; _} =
        expect_ok
        <$> add_validator_wrapper ~auth_address ~stake:min_auth_address_stake ~commission:U256.zero
              ~secret:(B32.of_hex_string "0x1000") ()
      in

      let$ _ = expect_ok <$> delegate_and_credit val1_id ~sender:auth_address ~value:min_auth_address_stake in
      let$ _ = expect_ok <$> call compound_function ~sender:auth_address [val1_id] in

      let$ () = snapshot in

      let$ {val_id = val2_id; _} =
        expect_ok
        <$> add_validator_wrapper ~auth_address:other_address ~stake:min_auth_address_stake
              ~commission:U256.zero ~secret:(B32.of_hex_string "0x1001") ()
      in

      let$ _ = expect_ok <$> delegate_and_credit val2_id ~sender:auth_address ~value:active_validator_stake in
      let$ _ = expect_ok <$> call compound_function ~sender:auth_address [val2_id] in

      let$ () = inc_epoch in

      let$ () = skip_to_next_epoch in
      let$ () = skip_to_next_epoch in

      let$ () = check_validator_flags "val1.flags" Address_flags.stake_too_low val1_id in
      let$ () =
        check_validator_stake "val1.stake" U256.(min_auth_address_stake + min_auth_address_stake) val1_id
      in
      let$ () = check_validator_flags "val2.flags" Address_flags.ok val2_id in
      let$ () =
        check_validator_stake "val2.stake" U256.(active_validator_stake + min_auth_address_stake) val2_id
      in

      let$ () =
        check_delegator_state ~val_id:val1_id ~delegator:auth_address
          ~expected_stake:U256.(min_auth_address_stake + min_auth_address_stake)
          ~expected_rewards:U256.zero
      in
      let$ () =
        check_delegator_state ~val_id:val2_id ~delegator:auth_address ~expected_stake:active_validator_stake
          ~expected_rewards:U256.zero
      in
      let$ () =
        check_delegator_state ~val_id:val2_id ~delegator:other_address ~expected_stake:min_auth_address_stake
          ~expected_rewards:U256.zero
      in
      return () )

let test_validator_withdrawal_before_active () =
  run_from_initial_state ~compare_with:"validator_withdrawal_before_active"
    M.(
      let auth_address = address "0xdeadbeef" in
      let other_address = address "0xdeaddead" in
      let withdrawal_id = U8.one in

      let$ {val_id = val1_id; _} =
        expect_ok
        <$> add_validator_wrapper ~auth_address ~stake:min_auth_address_stake ~commission:U256.zero
              ~secret:(B32.of_hex_string "0x1000") ()
      in

      let$ _ = expect_ok <$> delegate_and_credit val1_id ~sender:auth_address ~value:min_auth_address_stake in
      let$ () =
        expect_error Unknown_withdrawal_id
        <$> call withdraw_function ~sender:auth_address [val1_id; withdrawal_id]
      in

      let$ () = snapshot in

      let$ {val_id = val2_id; _} =
        expect_ok
        <$> add_validator_wrapper ~auth_address:other_address ~stake:min_auth_address_stake
              ~commission:U256.zero ~secret:(B32.of_hex_string "0x1001") ()
      in

      let$ _ = expect_ok <$> delegate_and_credit val2_id ~sender:auth_address ~value:active_validator_stake in
      let$ () =
        expect_error Unknown_withdrawal_id
        <$> call withdraw_function ~sender:auth_address [val2_id; withdrawal_id]
      in

      let$ () = inc_epoch in
      let$ () = skip_to_next_epoch in

      (* Check validator info. *)
      (* Check delegator info. *)
      let$ () =
        expect_error Unknown_withdrawal_id
        <$> call withdraw_function ~sender:auth_address [val1_id; withdrawal_id]
      in
      let$ () =
        expect_error Unknown_withdrawal_id
        <$> call withdraw_function ~sender:auth_address [val2_id; withdrawal_id]
      in
      return () )

let test_validator_undelegate_before_delegator_active () =
  run_from_initial_state ~compare_with:"validator_undelegate_before_delegator_active"
    M.(
      let auth_address = address "0xdeadbeef" in
      let other_address = address "0xdeaddead" in

      let$ {val_id = val1_id; _} =
        expect_ok
        <$> add_validator_wrapper ~auth_address ~stake:min_auth_address_stake ~commission:U256.zero
              ~secret:(B32.of_hex_string "0x1000") ()
      in
      let$ _ = expect_ok <$> delegate_and_credit val1_id ~sender:auth_address ~value:min_auth_address_stake in
      let$ () =
        expect_error Insufficient_stake
        <$> call undelegate_function ~sender:auth_address [val1_id; U256.(~$50); U8.one]
      in

      let$ () = snapshot in
      let$ {val_id = val2_id; _} =
        expect_ok
        <$> add_validator_wrapper ~auth_address:other_address ~stake:min_auth_address_stake
              ~commission:U256.zero ~secret:(B32.of_hex_string "0x1001") ()
      in
      let$ _ = expect_ok <$> delegate_and_credit val2_id ~sender:auth_address ~value:active_validator_stake in
      let$ () =
        expect_error Insufficient_stake
        <$> call undelegate_function ~sender:auth_address [val2_id; U256.(~$50); U8.one]
      in

      let$ () = inc_epoch in
      let$ () = skip_to_next_epoch in
      let$ () = skip_to_next_epoch in

      let$ _ = expect_ok <$> call undelegate_function ~sender:auth_address [val1_id; U256.(~$50); U8.one] in
      let$ _ = expect_ok <$> call undelegate_function ~sender:auth_address [val2_id; U256.(~$50); U8.one] in
      return () )

let test_validator_removes_self () =
  run_from_initial_state ~compare_with:"validator_removes_self"
    M.(
      let auth_address = address "0xdeadbeef" in
      let$ {val_id; sign_address} =
        expect_ok <$> add_validator_wrapper ~auth_address ~stake:min_auth_address_stake ()
      in
      let$ _ =
        expect_ok <$> delegate_and_credit val_id ~sender:(address "0xabab") ~value:active_validator_stake
      in
      let$ () = skip_to_next_epoch in

      let withdrawal_id = U8.one in
      let$ _ =
        expect_ok
        <$> call undelegate_function ~sender:auth_address [val_id; min_auth_address_stake; withdrawal_id]
      in

      (* Check execution state. *)
      let$ ve = !$(Variables.val_execution val_id) in
      check u256 "val_execution.stake" active_validator_stake ve.stake ;
      (* Despite having enough stake to be active, the primary validator has withdrawn, rendering the
         validator inactive. *)
      assert' "val_execution.flags & Withdrawn"
        U64.(logand ve.Val_execution.address_flags.Address_flags.flags Address_flags.withdrawn <> zero) ;

      (* Validator can still be rewarded this epoch because he's active. *)
      let$ _ = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      (* Take snapshot. *)
      let$ () = snapshot in

      (* Execution view and consensus view should both show validator removed. *)
      let$ () =
        let vc = Storage.Array.read_to_list Variables.valset_consensus in
        check int "valset_consensus.length" 0 <$> (List.length <$> vc)
      in
      (* Validate snapshot view since the current epoch is ongoing. *)
      let$ () =
        let vs = Storage.Array.read_to_list Variables.valset_snapshot in
        check int "valset_snapshot.length" 1 <$> (List.length <$> vs)
      in
      let$ sv = !$(Variables.snapshot_view val_id) in
      check u256 "snapshot_view.stake"
        U256.(active_validator_stake + min_auth_address_stake)
        sv.Snapshot_view.stake ;

      (* Rewards now reference the snapshot set and should continue to work for this validator. *)
      let$ _ = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      let$ () = inc_epoch in

      (* Consensus view doesn't include this validator, and reward fails. *)
      let$ () =
        expect_error Not_in_validator_set <$> syscall syscall_reward_function ~value:reward [sign_address]
      in

      return () )

let test_two_validators_remove_self () =
  let compare_sets name vs_loc expected =
    M.(
      let$ actual = Storage.Array.read_to_list vs_loc in
      check int (name ^ ".length") (List.length expected) (List.length actual) ;
      List.iter (fun id -> assert' (name ^ " contains id") (List.exists (Val_id.equal id) expected)) actual ;
      return () )
  in
  run_from_initial_state ~compare_with:"two_validators_remove_self"
    M.(
      let auth_address = address "0xdeadbeef" in

      let$ expected_full_valset =
        List.fold_leftM
          ~f:(fun acc i ->
            let$ {val_id; _} =
              expect_ok
              <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ~commission:U256.zero
                    ~secret:(B32.of_hex_string (Format.sprintf "0x%02x" (i + 1)))
                    ()
            in
            return (acc @ [val_id]) )
          [] (List.init 13 Fun.id)
      in

      let$ () = compare_sets "valset_execution" Variables.valset_execution expected_full_valset in
      let$ () = skip_to_next_epoch in
      let$ () = compare_sets "valset_consensus" Variables.valset_consensus expected_full_valset in

      (* Remove validator 9 and validator 4. *)
      let expected_valset_with_undelegations =
        List.filteri (fun i _ -> i <> 9 && i <> 4) expected_full_valset
      in
      let$ _ =
        expect_ok
        <$> call undelegate_function ~sender:auth_address
              [List.nth expected_full_valset 9; active_validator_stake; U8.one]
      in
      let$ _ =
        expect_ok
        <$> call undelegate_function ~sender:auth_address
              [List.nth expected_full_valset 4; active_validator_stake; U8.one]
      in

      let$ () = skip_to_next_epoch in
      let$ () =
        compare_sets "valset_execution" Variables.valset_execution expected_valset_with_undelegations
      in
      let$ () =
        compare_sets "valset_consensus" Variables.valset_consensus expected_valset_with_undelegations
      in

      let$ _ =
        delegate_and_credit (List.nth expected_full_valset 4) ~sender:auth_address
          ~value:active_validator_stake
      in
      let$ _ =
        delegate_and_credit (List.nth expected_full_valset 9) ~sender:auth_address
          ~value:active_validator_stake
      in
      let$ () = compare_sets "valset_execution" Variables.valset_execution expected_full_valset in
      let$ () = skip_to_next_epoch in
      let$ () = compare_sets "valset_consensus" Variables.valset_consensus expected_full_valset in

      return () )

let test_validator_constant_validator_set () =
  run_from_initial_state ~compare_with:"validator_constant_validator_set"
    M.(
      let auth_address = address "0xdeadbeef" in
      let other_address = address "0xdeaddead" in

      let$ {val_id = val1_id; _} =
        expect_ok
        <$> add_validator_wrapper ~auth_address ~stake:min_auth_address_stake ~commission:U256.zero
              ~secret:(B32.of_hex_string "0x1000") ()
      in

      let$ _ = expect_ok <$> delegate_and_credit val1_id ~sender:auth_address ~value:active_validator_stake in

      let$ () = snapshot in

      let$ {val_id = val2_id; _} =
        expect_ok
        <$> add_validator_wrapper ~auth_address:other_address ~stake:min_auth_address_stake
              ~commission:U256.zero ~secret:(B32.of_hex_string "0x1001") ()
      in

      let$ _ = expect_ok <$> delegate_and_credit val2_id ~sender:auth_address ~value:active_validator_stake in

      let$ () = inc_epoch in
      let$ () = skip_to_next_epoch in
      let$ () = skip_to_next_epoch in

      let$ () =
        List.iterM
          ~f:(fun i ->
            let withdrawal_id = U8.of_int (i + 1) in
            let$ _ =
              expect_ok
              <$> call undelegate_function ~sender:auth_address
                    [val1_id; U256.(min_auth_address_stake + one); withdrawal_id]
            in
            let$ _ =
              expect_ok
              <$> call undelegate_function ~sender:auth_address
                    [val2_id; U256.(min_auth_address_stake + one); withdrawal_id]
            in
            let$ _ =
              delegate_and_credit val1_id ~sender:auth_address ~value:U256.(min_auth_address_stake + one)
            in
            let$ _ =
              delegate_and_credit val2_id ~sender:auth_address ~value:U256.(min_auth_address_stake + one)
            in
            return () )
          (List.init 10 Fun.id)
      in

      let$ () =
        check int "this_epoch_valset length" 2 <$> (List.length <$> (expect_ok <$> get_this_epoch_valset))
      in

      let$ () = skip_to_next_epoch in

      let$ () =
        check int "this_epoch_valset length" 2 <$> (List.length <$> (expect_ok <$> get_this_epoch_valset))
      in

      let$ () = skip_to_next_epoch in

      let$ () =
        check int "this_epoch_valset length" 2 <$> (List.length <$> (expect_ok <$> get_this_epoch_valset))
      in

      return () )

let test_validator_joining_boundary_rewards () =
  run_from_initial_state ~compare_with:"validator_joining_boundary_rewards"
    M.(
      let auth_address = address "0xdeadbeef" in
      let$ {val_id = _; sign_address = val1_sign_address} =
        expect_ok
        <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ~commission:U256.zero
              ~secret:(B32.of_hex_string "0x1000") ()
      in

      (* Add a new validator before adding the snapshot. Simulate the case when a malicous consensus client
         rewards themselves early.
         All other nodes will not reward him, indicated by the BLOCK_AUTHOR_NOT_IN_SET error code, producing a
         state root mismatch on that block. *)
      let$ () = snapshot in
      let delay_window = 6000 in
      let$ () =
        List.iterM
          ~f:(fun _ ->
            expect_error Not_in_validator_set
            <$> syscall syscall_reward_function ~value:reward [val1_sign_address] )
          (List.init (delay_window - 100 + 1) Fun.id)
      in
      let$ {val_id = _; sign_address = val2_sign_address} =
        expect_ok
        <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ~commission:U256.zero
              ~secret:(B32.of_hex_string "0x1001") ()
      in
      let$ () =
        List.iterM
          ~f:(fun _ ->
            expect_error Not_in_validator_set
            <$> syscall syscall_reward_function ~value:reward [val1_sign_address] )
          (List.init 99 Fun.id)
      in

      (* Joined after the boundary, not active. *)
      let$ () =
        expect_error Not_in_validator_set <$> syscall syscall_reward_function ~value:reward [val2_sign_address]
      in
      let$ () = inc_epoch in

      (* Joined before the boundary, now active. *)
      let$ _ = expect_ok <$> syscall syscall_reward_function ~value:reward [val1_sign_address] in

      return () )

let test_validator_miss_snapshot_miss_activation () =
  run_from_initial_state ~compare_with:"validator_miss_snapshot_miss_activation"
    M.(
      let auth_address = address "0xdeadbeef" in
      let$ {val_id; _} =
        expect_ok
        <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ~commission:U256.zero
              ~secret:(B32.of_hex_string "0x1000") ()
      in

      let$ () = inc_epoch in

      let$ () =
        check int "this_epoch_valset().length()" 0 <$> (List.length <$> (expect_ok <$> get_this_epoch_valset))
      in
      let$ () = check_validator_flags "val_execution(1).get_flags()" Address_flags.ok val_id in

      let$ () = check_validator_stake "val_execution(1).stake()" active_validator_stake val_id in
      let$ ve = !$(Variables.val_execution val_id) in
      check u256 "val_execution(1).commission()" U256.zero ve.Val_execution.commission ;

      return () )

let test_validator_miss_snapshot_miss_deactivation () =
  run_from_initial_state ~compare_with:"validator_miss_snapshot_miss_deactivation"
    M.(
      let auth_address = address "0xdeadbeef" in
      let$ {val_id; _} = expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake () in
      let$ () = skip_to_next_epoch in

      let$ _ =
        expect_ok <$> call undelegate_function ~sender:auth_address [val_id; active_validator_stake; U8.one]
      in

      let$ () = inc_epoch in

      let$ () =
        check int "this_epoch_valset().length()" 1 <$> (List.length <$> (expect_ok <$> get_this_epoch_valset))
      in
      let withdrawn_and_stake_too_low = U64.(logor Address_flags.withdrawn Address_flags.stake_too_low) in
      let$ () = check_validator_flags "val_execution(1).get_flags()" withdrawn_and_stake_too_low val_id in

      let$ cv = expect_ok <$> get_this_epoch_view val_id in
      check u256 "this_epoch_view(1).stake()" active_validator_stake cv.Consensus_view.stake ;
      let$ () = check_validator_stake "val_execution(1).stake()" U256.zero val_id in

      return () )

let test_validator_external_rewards_failure_conditions () =
  run_from_initial_state ~compare_with:"validator_external_rewards_failure_conditions"
    M.(
      let auth_address = address "0xdeadbeef" in
      let$ {val_id; _} = expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake () in

      let$ () =
        expect_error Not_in_validator_set
        <$> call external_reward_function ~sender:auth_address ~value:U256.(~$20 * mon) [val_id]
      in
      let$ () = skip_to_next_epoch in
      (* Validator in set. *)

      let$ () =
        expect_error Unknown_validator
        <$> call external_reward_function ~sender:auth_address ~value:U256.(~$20 * mon) [Val_id.of_int 20]
      in

      let$ () =
        expect_error External_reward_too_small
        <$> call external_reward_function ~sender:auth_address ~value:U256.(~$5) [val_id]
      in
      let$ () =
        expect_error External_reward_too_small
        <$> call external_reward_function ~sender:auth_address ~value:U256.(min_external_reward - one) [val_id]
      in

      let$ () =
        expect_error External_reward_too_large
        <$> call external_reward_function ~sender:auth_address ~value:U256.(max_external_reward + one) [val_id]
      in

      let$ () = external_reward_and_credit val_id ~sender:auth_address ~value:U256.(~$20 * mon) in

      return () )

let test_validator_external_rewards_uniform_reward_pool () =
  run_from_initial_state ~compare_with:"validator_external_rewards_uniform_reward_pool"
    M.(
      let auth_address = address "0xdeadbeef" in
      let$ {val_id; _} = expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake () in

      let delegators =
        [auth_address; address "0xaaaa"; address "0xbbbb"; address "0xcccc"; address "0xdddd"]
      in
      let$ () =
        List.iterM
          ~f:(fun d ->
            if Address.(d = auth_address) then return ()
            else
              let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:d ~value:active_validator_stake in
              return () )
          delegators
      in
      let$ () = skip_to_next_epoch in

      let$ () = external_reward_and_credit val_id ~sender:auth_address ~value:U256.(~$20 * mon) in
      let$ () =
        List.iterM
          ~f:(fun d ->
            let$ () = pull_delegator_up_to_date val_id d in
            let$ del = !$(Variables.delegator (val_id, d)) in
            check u256 "delegator rewards" U256.(~$4 * mon) del.rewards ;
            return () )
          delegators
      in

      return () )

(**** Delegate tests. ****)

let test_delegate_init () =
  run_from_initial_state ~compare_with:"delegate_init"
    M.(
      let auth_address = address "0xdeadbeef" in
      let$ {val_id; sign_address} =
        expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ()
      in
      let$ () =
        let$ validator = !$(Variables.val_execution val_id) in
        return (check u256 "Correct stake" active_validator_stake validator.stake)
      in

      let d0 = address "0xaaaabbbb" in
      let d1 = address "0xbbbbaaaa" in

      let$ _ = expect_ok <$> delegate_and_credit ~sender:d0 ~value:active_validator_stake val_id in
      let$ () = snapshot in
      let$ _ = expect_ok <$> delegate_and_credit ~sender:d1 ~value:active_validator_stake val_id in
      let$ () = inc_epoch in

      let$ () = skip_to_next_epoch in

      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = pull_delegator_up_to_date val_id auth_address in
      let$ () = pull_delegator_up_to_date val_id d0 in
      let$ () = pull_delegator_up_to_date val_id d1 in

      let$ del_auth_address = !$(Variables.delegator (val_id, auth_address)) in
      check u256 "del_auth_address.rewards" U256.(reward / ~$3) del_auth_address.rewards ;
      let$ del_d0 = !$(Variables.delegator (val_id, d0)) in
      check u256 "del_d0.rewards" U256.(reward / ~$3) del_d0.rewards ;
      let$ del_d1 = !$(Variables.delegator (val_id, d1)) in
      check u256 "del_d1.rewards" U256.(reward / ~$3) del_d1.rewards ;

      let () =
        check u256 "del_d0.stake" active_validator_stake del_d0.stake ;
        check u256 "del_d0.delta_stake" U256.zero del_d0.delta_stake ;
        check u256 "del_d0.next_delta_stake" U256.zero del_d0.next_delta_stake ;
        check epoch "del_d0.epochs.delta_epoch" Epoch.zero del_d0.epochs.delta_epoch ;
        check epoch "del_d0.epochs.next_delta_epoch" Epoch.zero del_d0.epochs.next_delta_epoch
      in

      let () =
        check u256 "del_d1.stake" active_validator_stake del_d1.stake ;
        check u256 "del_d1.delta_stake" U256.zero del_d1.delta_stake ;
        check u256 "del_d1.next_delta_stake" U256.zero del_d1.next_delta_stake ;
        check epoch "del_d1.epochs.delta_epoch" Epoch.zero del_d1.epochs.delta_epoch ;
        check epoch "del_d1.epochs.next_delta_epoch" Epoch.zero del_d1.epochs.next_delta_epoch
      in

      return () )

let check_delegator_zero val_id delegator_addr =
  M.(
    let$ () = pull_delegator_up_to_date val_id delegator_addr in
    let$ del = !$(Variables.delegator (val_id, delegator_addr)) in
    check u256 "del.stake" U256.zero del.stake ;
    check u256 "del.rewards_per_token" U256.zero del.rewards_per_token ;
    check u256 "del.rewards" U256.zero del.rewards ;
    check u256 "del.delta_stake" U256.zero del.delta_stake ;
    check u256 "del.next_delta_stake" U256.zero del.next_delta_stake ;
    check epoch "del.epochs.delta_epoch" Epoch.zero del.epochs.delta_epoch ;
    check epoch "del.epochs.next_delta_epoch" Epoch.zero del.epochs.next_delta_epoch ;
    return () )

let test_delegator_none_init () =
  run_from_initial_state ~compare_with:"delegator_none_init"
    M.(
      let auth_address = address "0xdeadbeef" in
      let delegator = address "0x1337" in

      let$ {val_id; sign_address = _} =
        expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ()
      in

      (* 1. Call get_delegator_info(). *)
      let$ () = check_delegator_zero val_id delegator in

      (* 2. Undelegate. *)
      let$ () =
        expect_error Insufficient_stake
        <$> call undelegate_function ~sender:delegator [val_id; U256.(~$100); U8.one]
      in
      let$ () = check_delegator_zero val_id delegator in

      let$ _ = expect_ok <$> call undelegate_function ~sender:delegator [val_id; U256.zero; U8.one] in
      let$ () = check_delegator_zero val_id delegator in

      (* 3. Withdraw. *)
      let$ () =
        expect_error Unknown_withdrawal_id <$> call withdraw_function ~sender:delegator [val_id; U8.one]
      in
      let$ () = check_delegator_zero val_id delegator in

      (* 4. Compound. *)
      let$ _ = expect_ok <$> call compound_function ~sender:delegator [val_id] in
      let$ () = check_delegator_zero val_id delegator in

      (* 5. Claim. *)
      let$ _ = expect_ok <$> call claim_rewards_function ~sender:delegator [val_id] in
      let$ () = check_delegator_zero val_id delegator in
      let$ () = check u256 "balance" U256.zero <$> !(TransactionState.balance delegator) in

      return () )

let test_random_delegator_not_allocated_state () =
  run_from_initial_state ~compare_with:"random_delegator_not_allocated_state"
    M.(
      let auth_address = address "0xdeadbeef" in

      let$ {val_id; sign_address} =
        expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ()
      in

      let$ () = skip_to_next_epoch in

      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      (* State should not be allocated. *)
      let$ () = check_delegator_zero val_id (address "0xaaaabbbb") in

      return () )

let test_delegator_state_cleared_after_withdraw () =
  run_from_initial_state ~compare_with:"delegator_state_cleared_after_withdraw"
    M.(
      let auth_address = address "0xdeadbeef" in
      let delegator = address "0x1337" in

      let$ {val_id; sign_address} =
        expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ()
      in
      let$ _ = expect_ok <$> delegate_and_credit ~sender:delegator ~value:active_validator_stake val_id in

      let$ () = skip_to_next_epoch in

      (* This causes del.acc to be nonzero. *)
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      let$ () = skip_to_next_epoch in

      (* Clear rewards slot. *)
      let$ _ = expect_ok <$> call claim_rewards_function ~sender:delegator [val_id] in
      (* Remove stake, setting del.acc to zero. *)
      let$ _ =
        expect_ok <$> call undelegate_function ~sender:delegator [val_id; active_validator_stake; U8.one]
      in

      (* State should be deallocated. *)
      let$ () = check_delegator_zero val_id delegator in

      (* Just to be sure, let's redelegate again. *)
      let$ _ = expect_ok <$> delegate_and_credit ~sender:delegator ~value:active_validator_stake val_id in
      let$ () = skip_to_next_epoch in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = pull_delegator_up_to_date val_id delegator in
      let$ () = pull_delegator_up_to_date val_id auth_address in

      (* Check stake and rewards make sense. *)
      let$ del = !$(Variables.delegator (val_id, delegator)) in
      check u256 "del.stake" active_validator_stake del.stake ;
      assert' "del.rewards > 0" U256.(del.rewards > zero) ;
      let$ del_auth = !$(Variables.delegator (val_id, auth_address)) in
      assert' "auth.rewards > del.rewards" U256.(del_auth.rewards > del.rewards) ;

      return () )

let test_delegate_noop_add_zero_stake () =
  run_from_initial_state ~compare_with:"delegate_noop_add_zero_stake"
    M.(
      let auth_address = address "0xdeadbeef" in
      let$ {val_id; sign_address} =
        expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ()
      in
      let$ () =
        let$ ve = !$(Variables.val_execution val_id) in
        return (check u256 "val.stake" active_validator_stake ve.stake)
      in
      let$ () = skip_to_next_epoch in

      let d0 = address "0xaaaabbbb" in
      let$ _ = delegate_and_credit ~sender:d0 ~value:U256.zero val_id in

      let$ () = skip_to_next_epoch in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      let$ () = pull_delegator_up_to_date val_id auth_address in
      let$ () = pull_delegator_up_to_date val_id d0 in

      let$ del_auth = !$(Variables.delegator (val_id, auth_address)) in
      check u256 "del_auth.rewards" reward del_auth.rewards ;

      return () )

let test_delegate_noop_subsequent_zero_stake () =
  run_from_initial_state ~compare_with:"delegate_noop_subsequent_zero_stake"
    M.(
      let auth_address = address "0xdeadbeef" in
      let d0 = address "0xaaaabbbb" in

      let$ {val_id; sign_address} =
        expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ()
      in
      let$ _ = expect_ok <$> delegate_and_credit ~sender:d0 ~value:active_validator_stake val_id in
      let$ () =
        let$ ve = !$(Variables.val_execution val_id) in
        return (check u256 "val.stake" U256.(~$2 * active_validator_stake) ve.stake)
      in

      let$ () = skip_to_next_epoch in

      (* Reward the validator. *)
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      (* Validator should receive all the reward being the only active delegator. *)
      let$ () = pull_delegator_up_to_date val_id auth_address in
      let$ () = pull_delegator_up_to_date val_id d0 in

      let$ del_auth = !$(Variables.delegator (val_id, auth_address)) in
      check u256 "del_auth.rewards" U256.(reward + (reward / ~$2)) del_auth.rewards ;
      let$ del_d0 = !$(Variables.delegator (val_id, d0)) in
      check u256 "del_d0.rewards" U256.(reward + (reward / ~$2)) del_d0.rewards ;

      let$ _ = expect_ok <$> delegate_and_credit ~sender:d0 ~value:U256.zero val_id in

      let$ () = snapshot in

      let$ _ = expect_ok <$> delegate_and_credit ~sender:d0 ~value:U256.zero val_id in

      let$ del_d0 = !$(Variables.delegator (val_id, d0)) in
      check u256 "del_d0.rewards" U256.(reward + (reward / ~$2)) del_d0.rewards ;
      check u256 "del_d0.stake" active_validator_stake del_d0.stake ;
      check u256 "del_d0.delta_stake" U256.zero del_d0.delta_stake ;
      check u256 "del_d0.next_delta_stake" U256.zero del_d0.next_delta_stake ;
      check epoch "del_d0.epochs.delta_epoch" Epoch.zero del_d0.epochs.delta_epoch ;
      check epoch "del_d0.epochs.next_delta_epoch" Epoch.zero del_d0.epochs.next_delta_epoch ;

      return () )

let test_delegate_revert_unknown_validator () =
  run_from_initial_state ~compare_with:"delegate_revert_unknown_validator"
    M.(
      let d0 = address "0xaaaabbbb" in
      let$ () =
        expect_error Unknown_validator
        <$> delegate_and_credit ~sender:d0 ~value:active_validator_stake Val_id.(of_int 3)
      in
      return () )

let test_delegate_redelegate_before_activation () =
  run_from_initial_state ~compare_with:"delegate_redelegate_before_activation"
    M.(
      let auth_address = address "0xdeadbeef" in
      let other_address = address "0xdeaddead" in

      let$ {val_id; sign_address} =
        expect_ok
        <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ~commission:U256.zero
              ~secret:B32.(of_hex_string "0x1000")
              ()
      in

      let check_refcount ~epoch ~count =
        let$ acc = !$(Variables.accumulated_reward_per_token (Epoch.of_int epoch, val_id)) in
        return
          (check u256 "accumulated_reward_per_token epoch val_id = count" U256.(of_int count) acc.refcount)
      in

      let$ () = check_refcount ~epoch:2 ~count:1 in

      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:other_address ~value:active_validator_stake in
      let$ () = check_refcount ~epoch:2 ~count:2 in

      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:other_address ~value:active_validator_stake in
      let$ () = check_refcount ~epoch:2 ~count:2 in

      let$ () = snapshot in

      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:other_address ~value:active_validator_stake in
      let$ () = check_refcount ~epoch:3 ~count:1 in

      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:other_address ~value:active_validator_stake in
      let$ () = check_refcount ~epoch:3 ~count:1 in

      let$ () = inc_epoch in

      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      let$ () = pull_delegator_up_to_date val_id auth_address in
      let$ () = check_refcount ~epoch:2 ~count:1 in

      let$ () = pull_delegator_up_to_date val_id other_address in
      let$ () = check_refcount ~epoch:2 ~count:0 in

      let check_rewards ~address ~rewards =
        let$ del = !$(Variables.delegator (val_id, address)) in
        return (check u256 "delegator(val_id, address).rewards" rewards del.rewards)
      in
      let$ () = check_rewards ~address:auth_address ~rewards:U256.(reward / ~$3) in
      let$ () = check_rewards ~address:other_address ~rewards:U256.(~$2 * reward / ~$3) in
      let$ () = check_refcount ~epoch:2 ~count:0 in

      let$ () = skip_to_next_epoch in

      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = pull_delegator_up_to_date val_id auth_address in
      let$ () = pull_delegator_up_to_date val_id other_address in

      let$ () = check_rewards ~address:auth_address ~rewards:U256.((reward / ~$3) + (reward / ~$5)) in
      let$ () =
        check_rewards ~address:other_address ~rewards:U256.((~$2 * reward / ~$3) + (~$4 * reward / ~$5))
      in

      let$ () =
        expect_none ~msg:"accumulated_reward_per_token (val_id, 2)"
        <$> !$(Variables.accumulated_reward_per_token_opt (Epoch.of_int 2, val_id))
      in
      let$ () =
        expect_none ~msg:"accumulated_reward_per_token (val_id, 3)"
        <$> !$(Variables.accumulated_reward_per_token_opt (Epoch.of_int 3, val_id))
      in

      return () )

let test_delegate_redelegate_after_activation () =
  run_from_initial_state ~compare_with:"delegate_redelegate_after_activation"
    M.(
      let auth_address = address "0xdeadbeef" in
      let$ {val_id; sign_address} =
        expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ()
      in
      let$ ve = !$(Variables.val_execution val_id) in
      check u256 "val.stake" active_validator_stake ve.stake ;

      let$ () = skip_to_next_epoch in

      let d0 = address "0xaaaabbbb" in
      let d1 = address "0xbbbbaaaa" in
      let$ _ =
        expect_ok <$> delegate_and_credit val_id ~sender:d0 ~value:U256.(active_validator_stake / ~$2)
      in
      let$ _ =
        expect_ok <$> delegate_and_credit val_id ~sender:d0 ~value:U256.(active_validator_stake / ~$2)
      in

      let$ () = snapshot in

      let$ _ =
        expect_ok <$> delegate_and_credit val_id ~sender:d1 ~value:U256.(active_validator_stake / ~$2)
      in
      let$ _ =
        expect_ok <$> delegate_and_credit val_id ~sender:d1 ~value:U256.(active_validator_stake / ~$2)
      in

      let$ ve = !$(Variables.val_execution val_id) in
      check u256 "val.stake" U256.(~$3 * active_validator_stake) ve.stake ;

      (* Reward the validator. *)
      let$ del_auth = !$(Variables.delegator (val_id, auth_address)) in
      check u256 "del_auth.rewards" U256.zero del_auth.rewards ;
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      let$ acc = !$(Variables.accumulated_reward_per_token (Epoch.of_int 3, val_id)) in
      check u256 "acc.value" U256.zero acc.value ;
      check u256 "acc.refcount" U256.one acc.refcount ;

      let$ acc_boundary = !$(Variables.accumulated_reward_per_token (Epoch.of_int 4, val_id)) in
      check u256 "acc_boundary.value" U256.zero acc_boundary.value ;
      check u256 "acc_boundary.refcount" U256.one acc_boundary.refcount ;

      let$ () = inc_epoch in

      (* Validator should receive all the reward being the only active delegator. *)
      let$ () = pull_delegator_up_to_date val_id auth_address in
      let$ del_auth = !$(Variables.delegator (val_id, auth_address)) in
      check u256 "del_auth.rewards" U256.(~$3 * reward) del_auth.rewards ;

      (* Calling touch again should be a no-op. *)
      let$ () = pull_delegator_up_to_date val_id auth_address in
      let$ del_auth = !$(Variables.delegator (val_id, auth_address)) in
      check u256 "del_auth.rewards (no-op)" U256.(~$3 * reward) del_auth.rewards ;

      (* Secondary delegators were not active and should receive nothing. *)
      let$ del_d0 = !$(Variables.delegator (val_id, d0)) in
      check u256 "del_d0.rewards" U256.zero del_d0.rewards ;
      let$ del_d1 = !$(Variables.delegator (val_id, d1)) in
      check u256 "del_d1.rewards" U256.zero del_d1.rewards ;

      (* Reward again with only 1 active delegator. *)
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      let$ () = pull_delegator_up_to_date val_id auth_address in
      let$ () = pull_delegator_up_to_date val_id d0 in
      let$ () = pull_delegator_up_to_date val_id d1 in

      let$ del_auth = !$(Variables.delegator (val_id, auth_address)) in
      check u256 "del_auth.rewards" U256.((~$3 * reward) + (reward / ~$2)) del_auth.rewards ;

      let$ del_d0 = !$(Variables.delegator (val_id, d0)) in
      check u256 "del_d0.rewards" U256.(reward / ~$2) del_d0.rewards ;
      let$ del_d1 = !$(Variables.delegator (val_id, d1)) in
      check u256 "del_d1.rewards" U256.zero del_d1.rewards ;

      let$ () = skip_to_next_epoch in

      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = pull_delegator_up_to_date val_id auth_address in
      let$ () = pull_delegator_up_to_date val_id d0 in
      let$ () = pull_delegator_up_to_date val_id d1 in

      let$ del_auth = !$(Variables.delegator (val_id, auth_address)) in
      check u256 "del_auth.rewards" U256.((~$3 * reward) + (reward / ~$2) + (reward / ~$3)) del_auth.rewards ;
      let$ del_d0 = !$(Variables.delegator (val_id, d0)) in
      check u256 "del_d0.rewards" U256.((reward / ~$2) + (reward / ~$3)) del_d0.rewards ;
      let$ del_d1 = !$(Variables.delegator (val_id, d1)) in
      check u256 "del_d1.rewards" U256.(reward / ~$3) del_d1.rewards ;

      let$ acc = !$(Variables.accumulated_reward_per_token (Epoch.of_int 3, val_id)) in
      check u256 "acc.value" U256.zero acc.value ;
      check u256 "acc.refcount" U256.zero acc.refcount ;

      let$ acc_boundary = !$(Variables.accumulated_reward_per_token (Epoch.of_int 4, val_id)) in
      check u256 "acc_boundary.value" U256.zero acc_boundary.value ;
      check u256 "acc_boundary.refcount" U256.zero acc_boundary.refcount ;

      let () =
        check u256 "del_d0.stake" active_validator_stake del_d0.stake ;
        check u256 "del_d0.delta_stake" U256.zero del_d0.delta_stake ;
        check u256 "del_d0.next_delta_stake" U256.zero del_d0.next_delta_stake ;
        check epoch "del_d0.epochs.delta_epoch" Epoch.zero del_d0.epochs.delta_epoch ;
        check epoch "del_d0.epochs.next_delta_epoch" Epoch.zero del_d0.epochs.next_delta_epoch
      in

      let () =
        check u256 "del_d1.stake" active_validator_stake del_d1.stake ;
        check u256 "del_d1.delta_stake" U256.zero del_d1.delta_stake ;
        check u256 "del_d1.next_delta_stake" U256.zero del_d1.next_delta_stake ;
        check epoch "del_d1.epochs.delta_epoch" Epoch.zero del_d1.epochs.delta_epoch ;
        check epoch "del_d1.epochs.next_delta_epoch" Epoch.zero del_d1.epochs.next_delta_epoch
      in

      return () )

let test_delegate_undelegate_withdraw_redelegate () =
  run_from_initial_state ~compare_with:"delegate_undelegate_withdraw_redelegate"
    M.(
      let auth_address = address "0xdeadbeef" in
      let$ {val_id; sign_address} =
        expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ()
      in
      let$ ve = !$(Variables.val_execution val_id) in
      check u256 "val.stake" active_validator_stake ve.stake ;

      let$ () = skip_to_next_epoch in

      let d0 = address "0xaaaabbbb" in
      let d1 = address "0xbbbbaaaa" in
      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:d0 ~value:active_validator_stake in

      let$ () = snapshot in

      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:d1 ~value:active_validator_stake in

      (* Reward the validator. *)
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      let$ () = inc_epoch in

      (* Reward again with only 1 active delegator. *)
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      let$ () = skip_to_next_epoch in

      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = pull_delegator_up_to_date val_id auth_address in
      let$ () = pull_delegator_up_to_date val_id d0 in
      let$ () = pull_delegator_up_to_date val_id d1 in

      let$ del_auth = !$(Variables.delegator (val_id, auth_address)) in
      check u256 "del_auth.rewards" U256.((~$3 * reward) + (reward / ~$2) + (reward / ~$3)) del_auth.rewards ;
      let$ del_d0 = !$(Variables.delegator (val_id, d0)) in
      check u256 "del_d0.rewards" U256.((reward / ~$2) + (reward / ~$3)) del_d0.rewards ;
      let$ del_d1 = !$(Variables.delegator (val_id, d1)) in
      check u256 "del_d1.rewards" U256.(reward / ~$3) del_d1.rewards ;

      let$ acc = !$(Variables.accumulated_reward_per_token (Epoch.of_int 3, val_id)) in
      check u256 "acc.value" U256.zero acc.value ;
      check u256 "acc.refcount" U256.zero acc.refcount ;

      let$ acc_boundary = !$(Variables.accumulated_reward_per_token (Epoch.of_int 4, val_id)) in
      check u256 "acc_boundary.value" U256.zero acc_boundary.value ;
      check u256 "acc_boundary.refcount" U256.zero acc_boundary.refcount ;

      let withdrawal_id = U8.one in
      let$ _ =
        expect_ok <$> call undelegate_function ~sender:d0 [val_id; active_validator_stake; withdrawal_id]
      in
      let$ () = snapshot in
      let$ _ =
        expect_ok <$> call undelegate_function ~sender:d1 [val_id; active_validator_stake; withdrawal_id]
      in

      let$ () = inc_epoch in
      let$ () = skip_to_next_epoch in
      let$ () = skip_to_next_epoch in

      let$ _ = expect_ok <$> call withdraw_function ~sender:d0 [val_id; withdrawal_id] in
      let$ _ = expect_ok <$> call withdraw_function ~sender:d1 [val_id; withdrawal_id] in

      let$ del_d0 = !$(Variables.delegator (val_id, d0)) in
      let () =
        check u256 "del_d0.stake" U256.zero del_d0.stake ;
        check u256 "del_d0.delta_stake" U256.zero del_d0.delta_stake ;
        check u256 "del_d0.next_delta_stake" U256.zero del_d0.next_delta_stake ;
        check epoch "del_d0.epochs.delta_epoch" Epoch.zero del_d0.epochs.delta_epoch ;
        check epoch "del_d0.epochs.next_delta_epoch" Epoch.zero del_d0.epochs.next_delta_epoch
      in

      let$ del_d1 = !$(Variables.delegator (val_id, d1)) in
      let () =
        check u256 "del_d1.stake" U256.zero del_d1.stake ;
        check u256 "del_d1.delta_stake" U256.zero del_d1.delta_stake ;
        check u256 "del_d1.next_delta_stake" U256.zero del_d1.next_delta_stake ;
        check epoch "del_d1.epochs.delta_epoch" Epoch.zero del_d1.epochs.delta_epoch ;
        check epoch "del_d1.epochs.next_delta_epoch" Epoch.zero del_d1.epochs.next_delta_epoch
      in

      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:d0 ~value:active_validator_stake in

      let$ () = snapshot in

      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:d1 ~value:active_validator_stake in

      let$ del_d0 = !$(Variables.delegator (val_id, d0)) in
      let () =
        check u256 "del_d0.stake" U256.zero del_d0.stake ;
        check u256 "del_d0.delta_stake" active_validator_stake del_d0.delta_stake ;
        check u256 "del_d0.next_delta_stake" U256.zero del_d0.next_delta_stake ;
        check epoch "del_d0.epochs.delta_epoch" Epoch.(of_int 8) del_d0.epochs.delta_epoch ;
        check epoch "del_d0.epochs.next_delta_epoch" Epoch.zero del_d0.epochs.next_delta_epoch
      in

      let$ del_d1 = !$(Variables.delegator (val_id, d1)) in
      let () =
        check u256 "del_d1.stake" U256.zero del_d1.stake ;
        check u256 "del_d1.delta_stake" U256.zero del_d1.delta_stake ;
        check u256 "del_d1.next_delta_stake" active_validator_stake del_d1.next_delta_stake ;
        check epoch "del_d1.epochs.delta_epoch" Epoch.zero del_d1.epochs.delta_epoch ;
        check epoch "del_d1.epochs.next_delta_epoch" Epoch.(of_int 9) del_d1.epochs.next_delta_epoch
      in

      return () )

let test_delegator_delegates_in_epoch_delay_period () =
  run_from_initial_state ~compare_with:"delegator_delegates_in_epoch_delay_period"
    M.(
      let auth_address = address "0xdeadbeef" in
      let$ {val_id; sign_address} =
        expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ()
      in
      let$ () = skip_to_next_epoch in

      let del_address = address "0xaaaabbbb" in
      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:del_address ~value:active_validator_stake in

      (* Take snapshot and reward during the window. delegator *should not* receive rewards. *)
      let$ () = snapshot in
      let delay_window = 6000 in
      let$ () =
        List.iterM
          ~f:(fun _ ->
            let$ cv = expect_ok <$> get_this_epoch_view val_id in
            check u256 "this_epoch_view(val_id).stake" active_validator_stake cv.stake ;
            let$ ve = !$(Variables.val_execution val_id) in
            check u256 "val_execution(val_id).stake" U256.(active_validator_stake * ~$2) ve.stake ;
            expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] )
          (List.init delay_window Fun.id)
      in

      let$ () = pull_delegator_up_to_date val_id auth_address in
      let$ () = pull_delegator_up_to_date val_id del_address in

      (* Validator should get all the rewards since the secondary delegator does not become active in the
         consensus view until after the window expires. *)
      let$ del_auth = !$(Variables.delegator (val_id, auth_address)) in
      check u256 "del_auth.rewards" U256.(reward * ~$delay_window) del_auth.rewards ;
      let$ del_delegator = !$(Variables.delegator (val_id, del_address)) in
      check u256 "del_delegator.rewards" U256.zero del_delegator.rewards ;

      return () )

let test_delegate_redelegation_refcount_before_activation () =
  run_from_initial_state ~compare_with:"delegate_redelegation_refcount_before_activation"
    M.(
      let auth_address = address "0xdeadbeef" in
      let$ {val_id; sign_address = _} =
        expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ()
      in

      let check_refcount ~epoch ~count =
        let$ acc = !$(Variables.accumulated_reward_per_token (Epoch.of_int epoch, val_id)) in
        return
          (check u256 "accumulated_reward_per_token epoch val_id = count" U256.(of_int count) acc.refcount)
      in

      (* Do a bunch of redelegations before snapshot. *)
      let$ () =
        List.iterM
          ~f:(fun _ -> ignore <$> delegate_and_credit val_id ~sender:auth_address ~value:mon)
          (List.init 20 Fun.id)
      in

      let$ () = snapshot in

      (* And some more in the snapshot. *)
      let$ () =
        List.iterM
          ~f:(fun _ -> ignore <$> delegate_and_credit val_id ~sender:auth_address ~value:mon)
          (List.init 20 Fun.id)
      in
      let$ () = inc_epoch in

      let$ () = check_refcount ~epoch:2 ~count:1 in
      let$ () = check_refcount ~epoch:3 ~count:1 in

      let$ () = pull_delegator_up_to_date val_id auth_address in

      let$ () = check_refcount ~epoch:2 ~count:0 in
      let$ () = check_refcount ~epoch:3 ~count:1 in

      let$ () = snapshot in
      let$ () = inc_epoch in

      let$ () = pull_delegator_up_to_date val_id auth_address in

      let$ () = check_refcount ~epoch:2 ~count:0 in
      let$ () = check_refcount ~epoch:3 ~count:0 in

      return () )

let test_delegate_redelegation_refcount_after_activation () =
  run_from_initial_state ~compare_with:"delegate_redelegation_refcount_after_activation"
    M.(
      let auth_address = address "0xdeadbeef" in
      let$ {val_id; sign_address = _} =
        expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ()
      in

      let check_refcount ~epoch ~count =
        let$ acc = !$(Variables.accumulated_reward_per_token (Epoch.of_int epoch, val_id)) in
        return
          (check u256 "accumulated_reward_per_token epoch val_id = count" U256.(of_int count) acc.refcount)
      in

      let$ () = snapshot in
      let$ () = inc_epoch in

      (* do a bunch of redelegations before snapshot *)
      let$ () =
        List.iterM
          ~f:(fun _ -> ignore <$> delegate_and_credit val_id ~sender:auth_address ~value:mon)
          (List.init 20 Fun.id)
      in

      let$ () = snapshot in

      (* and some more in the snapshot *)
      let$ () =
        List.iterM
          ~f:(fun _ -> ignore <$> delegate_and_credit val_id ~sender:auth_address ~value:mon)
          (List.init 20 Fun.id)
      in

      let$ () = check_refcount ~epoch:3 ~count:1 in
      let$ () = check_refcount ~epoch:4 ~count:1 in

      let$ () = inc_epoch in

      let$ () = pull_delegator_up_to_date val_id auth_address in

      let$ () = check_refcount ~epoch:3 ~count:0 in
      let$ () = check_refcount ~epoch:4 ~count:1 in

      let$ () = snapshot in
      let$ () = inc_epoch in

      let$ () = pull_delegator_up_to_date val_id auth_address in

      let$ () = check_refcount ~epoch:3 ~count:0 in
      let$ () = check_refcount ~epoch:4 ~count:0 in

      return () )

let test_delegator_epoch_accumulator_same_snapshot () =
  run_from_initial_state ~compare_with:"delegator_epoch_accumulator_same_snapshot"
    M.(
      let auth_address = address "0xdeadbeef" in
      let$ {val_id; sign_address = _} =
        expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ()
      in

      (* Add 2 delegators in same snapshot window. *)
      let d0 = address "0xaaaabbbb" in
      let d1 = address "0xbbbbaaaa" in
      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:d0 ~value:active_validator_stake in
      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:d1 ~value:active_validator_stake in

      let$ () = snapshot in
      let$ () = inc_epoch in

      (* 3 delegators become active. Therefore ref count should be 3 and acc is 0. *)
      let$ acc = !$(Variables.accumulated_reward_per_token (Epoch.of_int 2, val_id)) in
      check u256 "acc(2).value" U256.zero acc.value ;
      check u256 "acc(2).refcount" U256.(~$3) acc.refcount ;

      let$ () = pull_delegator_up_to_date val_id auth_address in
      let$ () = pull_delegator_up_to_date val_id d0 in
      let$ () = pull_delegator_up_to_date val_id d1 in

      (* Acc and ref should be empty now. *)
      let$ acc = !$(Variables.accumulated_reward_per_token (Epoch.of_int 3, val_id)) in
      check u256 "acc(3).value" U256.zero acc.value ;
      check u256 "acc(3).refcount" U256.zero acc.refcount ;

      return () )

let test_delegator_epoch_accumulator_diff_snapshot () =
  run_from_initial_state ~compare_with:"delegator_epoch_accumulator_diff_snapshot"
    M.(
      let auth_address = address "0xdeadbeef" in
      let$ {val_id; sign_address = _} =
        expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ()
      in

      let$ () = snapshot in
      (* Add 2 delegators in different snapshot windows. *)
      let d0 = address "0xaaaabbbb" in
      let d1 = address "0xbbbbaaaa" in
      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:d0 ~value:active_validator_stake in
      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:d1 ~value:active_validator_stake in

      let$ () = inc_epoch in

      (* 1 delegator becomes active. Therefore ref count should be 1 and acc is 0. *)
      let$ acc = !$(Variables.accumulated_reward_per_token (Epoch.of_int 2, val_id)) in
      check u256 "acc(2).value" U256.zero acc.value ;
      check u256 "acc(2).refcount" U256.one acc.refcount ;

      let$ () = snapshot in
      let$ () = inc_epoch in

      (* 2 delegators become active. Therefore ref count should be 2 and acc
         is 0 since no rewards. *)
      let$ acc = !$(Variables.accumulated_reward_per_token (Epoch.of_int 3, val_id)) in
      check u256 "acc(3).value" U256.zero acc.value ;
      check u256 "acc(3).refcount" U256.(~$2) acc.refcount ;

      let$ () = pull_delegator_up_to_date val_id auth_address in
      let$ () = pull_delegator_up_to_date val_id d0 in
      let$ () = pull_delegator_up_to_date val_id d1 in

      (* acc and ref should be empty now for both epochs. *)
      let$ acc = !$(Variables.accumulated_reward_per_token (Epoch.of_int 2, val_id)) in
      check u256 "acc(2).value" U256.zero acc.value ;
      check u256 "acc(2).refcount" U256.zero acc.refcount ;

      let$ acc = !$(Variables.accumulated_reward_per_token (Epoch.of_int 3, val_id)) in
      check u256 "acc(3).value" U256.zero acc.value ;
      check u256 "acc(3).refcount" U256.zero acc.refcount ;

      return () )

let test_delegator_epoch_nz_accumulator_diff_snapshot () =
  run_from_initial_state ~compare_with:"delegator_epoch_nz_accumulator_diff_snapshot"
    M.(
      let auth_address = address "0xdeadbeef" in
      let$ {val_id; sign_address} =
        expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ()
      in

      let$ () = snapshot in
      (* Add 2 delegators in different snapshot window. *)
      let d0 = address "0xaaaabbbb" in
      let d1 = address "0xbbbbaaaa" in
      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:d0 ~value:active_validator_stake in
      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:d1 ~value:active_validator_stake in

      let$ () = inc_epoch in

      (* 1 delegator becomes active. Therefore ref count should be 1 and acc is 0. *)
      let$ acc = !$(Variables.accumulated_reward_per_token (Epoch.of_int 2, val_id)) in
      check u256 "acc(2).value" U256.zero acc.value ;
      check u256 "acc(2).refcount" U256.one acc.refcount ;

      (* Validator is rewarded. next acc is nonzero. *)
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      let$ () = snapshot in
      let$ () = inc_epoch in

      (* 2 delegators become active. Therefore ref count should be 2 and acc is nonzero. *)
      let$ acc = !$(Variables.accumulated_reward_per_token (Epoch.of_int 3, val_id)) in
      check u256 "acc(3).value" U256.(reward * unit_bias / active_validator_stake) acc.value ;
      check u256 "acc(3).refcount" U256.(~$2) acc.refcount ;

      let$ () = pull_delegator_up_to_date val_id auth_address in
      let$ () = pull_delegator_up_to_date val_id d0 in
      let$ () = pull_delegator_up_to_date val_id d1 in

      (* acc and ref should be empty now for both epochs. *)
      let$ acc = !$(Variables.accumulated_reward_per_token (Epoch.of_int 2, val_id)) in
      check u256 "acc(2).value" U256.zero acc.value ;
      check u256 "acc(2).refcount" U256.zero acc.refcount ;

      let$ acc = !$(Variables.accumulated_reward_per_token (Epoch.of_int 3, val_id)) in
      check u256 "acc(3).value" U256.zero acc.value ;
      check u256 "acc(3).refcount" U256.zero acc.refcount ;

      let$ del_d0 = !$(Variables.delegator (val_id, d0)) in
      assert' "del_d0.rewards_per_token > 0" U256.(del_d0.rewards_per_token > zero) ;

      return () )

let test_validator_exit_delegator_boundary_nz_accumulator () =
  (* Scenario:
     Add a validator in epoch N. Validator is active in epoch N+1.  During the boundary between N+1 and N+2,
     add a delegator. Ensure the delegator's accumulator is set correctly. This is an edge case because the
     validator will be out of the set in N+2 and will therefore not push his accumulator. *)
  run_from_initial_state ~compare_with:"validator_exit_delegator_boundary_nz_accumulator"
    M.(
      let auth_address = address "0xdeadbeef" in
      let del = address "0xaaaabbbb" in
      let$ {val_id; sign_address} =
        expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ()
      in

      let$ () = skip_to_next_epoch in
      (* Reward validator so his accumulator is nonzero. *)
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ _ =
        expect_ok <$> call undelegate_function ~sender:auth_address [val_id; active_validator_stake; U8.one]
      in

      (* Add delegator in the boundary. *)
      (* He greedily sets his future accumulator to val.acc. *)
      let$ () = snapshot in
      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:del ~value:active_validator_stake in

      (* Reward the validator in the boundary, so the greedy accumulator for N+2 is now stale. *)
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      (* Goto epoch N+1. delegator is not active until N+2. *)
      let$ () = inc_epoch in

      let$ valset_exec = Storage.Array.read_to_list Variables.valset_execution in
      assert' "valset_execution.empty()" (List.length valset_exec = 0) ;
      let$ () =
        check_delegator_state ~val_id ~delegator:del ~expected_stake:U256.zero ~expected_rewards:U256.zero
      in

      (* Goto epoch N+2. *)
      let$ () = skip_to_next_epoch in

      (* Load accumulators. *)
      let$ current_epoch = !$Variables.epoch in
      let$ epoch_acc = !$(Variables.accumulated_reward_per_token (current_epoch, val_id)) in
      check u256 "epoch_acc.refcount" U256.one epoch_acc.refcount ;
      let$ ve = !$(Variables.val_execution val_id) in
      assert' "val_acc > 0" U256.(ve.rewards_per_token > zero) ;
      check u256 "val_acc = epoch_acc.value" ve.rewards_per_token epoch_acc.value ;

      return () )

let test_snapshot_set_same_order_as_consensus_set () =
  run_from_initial_state ~compare_with:"snapshot_set_same_order_as_consensus_set"
    M.(
      (* Add five validators. *)
      let auth_address = address "0xdeadbeef" in
      let$ () =
        List.iterM
          ~f:(fun i ->
            let secret = B32.of_hex_string (Format.sprintf "0x%02x" (i + 1)) in
            let$ _ =
              expect_ok
              <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ~commission:U256.zero
                    ~secret ()
            in
            return () )
          (List.init 5 Fun.id)
      in

      (* Validators join the consensus set. *)
      let$ () = skip_to_next_epoch in

      (* Consensus set copied to snapshot set. They should be the same now. *)
      let$ () = skip_to_next_epoch in

      (* Sets should be the same with ids in order. *)
      let$ consensus = Storage.Array.read_to_list Variables.valset_consensus in
      let$ snapshot = Storage.Array.read_to_list Variables.valset_snapshot in
      check int "lengths equal" (List.length consensus) (List.length snapshot) ;
      check (list validator_id) "consensus = snapshot" consensus snapshot ;

      return () )

(**** Compound/redelegate tests. ****)

let test_delegate_inter_compound_rewards () =
  run_from_initial_state ~compare_with:"delegate_inter_compound_rewards"
    M.(
      (* Epoch 1 - add validator and 2 delegators. *)
      let auth_address = address "0xdeadbeef" in
      let reward_decimal_rounding = U256.(~@"999999999999999999") in
      let$ {val_id; sign_address} =
        expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ()
      in
      let$ ve = !$(Variables.val_execution val_id) in
      check u256 "val.stake" active_validator_stake ve.stake ;

      (* Add 2 delegators. *)
      let d0 = address "0xaaaabbbb" in
      let d1 = address "0xbbbbaaaa" in
      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:d0 ~value:active_validator_stake in
      let$ ve = !$(Variables.val_execution val_id) in
      check u256 "val.stake after d0" U256.(~$2 * active_validator_stake) ve.stake ;
      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:d1 ~value:active_validator_stake in
      let$ ve = !$(Variables.val_execution val_id) in
      check u256 "val.stake after d1" U256.(~$3 * active_validator_stake) ve.stake ;

      let$ () = skip_to_next_epoch in
      (* Epoch 2 - 3 block reward. this should be split evenly. *)

      (* Auth account should get 1/3 of all rewards this epoch. *)
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      (* Auth account should get 2/4 rewards at next epoch. *)
      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:auth_address ~value:active_validator_stake in

      (* Other delegators should get 1/3 of all rewards this epoch. *)
      let$ () = pull_delegator_up_to_date val_id d0 in
      let$ () = pull_delegator_up_to_date val_id d1 in

      let$ ve = !$(Variables.val_execution val_id) in
      check u256 "val.stake after re-delegate" U256.(~$4 * active_validator_stake) ve.stake ;

      (* Decimal inaccuracy. Off by 1 wei. *)
      let$ del_auth = !$(Variables.delegator (val_id, auth_address)) in
      check u256 "del_auth.rewards" reward_decimal_rounding del_auth.rewards ;
      let$ del_d0 = !$(Variables.delegator (val_id, d0)) in
      check u256 "del_d0.rewards" reward_decimal_rounding del_d0.rewards ;
      let$ del_d1 = !$(Variables.delegator (val_id, d1)) in
      check u256 "del_d1.rewards" reward_decimal_rounding del_d1.rewards ;

      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      let$ () = skip_to_next_epoch in
      (* Epoch 3 - 6 block reward. this should be 1/2 validator, 1/4 to each delegator. *)

      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      (* Delegator rewards should be p*(accumulated_reward_per_token(epoch) -
         accumulated_reward_per_token(del)) + p + r
         *(accumulated_reward_per_token(curr) -
         accumulated_reward_per_token(epoch)) *)
      let$ () = pull_delegator_up_to_date val_id auth_address in
      let$ () = pull_delegator_up_to_date val_id d0 in
      let$ () = pull_delegator_up_to_date val_id d1 in

      let$ del_auth = !$(Variables.delegator (val_id, auth_address)) in
      check u256 "del_auth.rewards final"
        U256.((~$2 * reward_decimal_rounding) + (reward / ~$2) + reward)
        del_auth.rewards ;

      let$ del_d0 = !$(Variables.delegator (val_id, d0)) in
      check u256 "del_d0.rewards final"
        U256.((~$2 * reward_decimal_rounding) + (~$3 * reward / ~$4))
        del_d0.rewards ;
      let$ del_d1 = !$(Variables.delegator (val_id, d1)) in
      check u256 "del_d1.rewards final"
        U256.((~$2 * reward_decimal_rounding) + (~$3 * reward / ~$4))
        del_d1.rewards ;

      return () )

let test_delegate_intra_compound_rewards () =
  run_from_initial_state ~compare_with:"delegate_intra_compound_rewards"
    M.(
      let auth_address = address "0xdeadbeef" in
      let reward_decimal_rounding = U256.(~@"999999999999999999") in
      let$ {val_id; sign_address} =
        expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ()
      in
      let$ ve = !$(Variables.val_execution val_id) in
      check u256 "val.stake" active_validator_stake ve.Val_execution.stake ;

      (* Add 2 delegators. *)
      let d0 = address "0xaaaabbbb" in
      let d1 = address "0xbbbbaaaa" in
      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:d0 ~value:active_validator_stake in
      let$ ve = !$(Variables.val_execution val_id) in
      check u256 "val.stake after d0" U256.(~$2 * active_validator_stake) ve.Val_execution.stake ;
      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:d1 ~value:active_validator_stake in
      let$ ve = !$(Variables.val_execution val_id) in
      check u256 "val.stake after d1" U256.(~$3 * active_validator_stake) ve.Val_execution.stake ;

      let$ () = skip_to_next_epoch in

      (* Auth account should get 1/3 of all rewards this epoch. *)
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      (* Auth account should get 2/4 rewards at next epoch. *)
      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:auth_address ~value:active_validator_stake in

      (* Other delegators should get 1/3 of all rewards this epoch. *)
      let$ () = pull_delegator_up_to_date val_id d0 in
      let$ () = pull_delegator_up_to_date val_id d1 in

      let$ ve = !$(Variables.val_execution val_id) in
      check u256 "val.stake after re-delegate" U256.(~$4 * active_validator_stake) ve.Val_execution.stake ;

      (* Decimal inaccuracy. Off by 1 wei. *)
      let$ del_auth = !$(Variables.delegator (val_id, auth_address)) in
      check u256 "del_auth.rewards" reward_decimal_rounding del_auth.rewards ;
      let$ del_d0 = !$(Variables.delegator (val_id, d0)) in
      check u256 "del_d0.rewards" reward_decimal_rounding del_d0.rewards ;
      let$ del_d1 = !$(Variables.delegator (val_id, d1)) in
      check u256 "del_d1.rewards" reward_decimal_rounding del_d1.rewards ;

      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      (* Auth account should get 3/5 rewards at next epoch. *)
      (* Other delegators should get 1/5 of all rewards next epoch. *)
      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:auth_address ~value:active_validator_stake in

      let$ () = skip_to_next_epoch in

      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      let$ () = pull_delegator_up_to_date val_id auth_address in
      let$ () = pull_delegator_up_to_date val_id d0 in
      let$ () = pull_delegator_up_to_date val_id d1 in

      let$ del_auth = !$(Variables.delegator (val_id, auth_address)) in
      check u256 "del_auth.rewards final"
        U256.((~$2 * reward_decimal_rounding) + (~$9 * reward / ~$5))
        del_auth.rewards ;

      let$ del_d0 = !$(Variables.delegator (val_id, d0)) in
      check u256 "del_d0.rewards final"
        U256.((~$2 * reward_decimal_rounding) + (~$3 * reward / ~$5))
        del_d0.rewards ;
      let$ del_d1 = !$(Variables.delegator (val_id, d1)) in
      check u256 "del_d1.rewards final"
        U256.((~$2 * reward_decimal_rounding) + (~$3 * reward / ~$5))
        del_d1.rewards ;

      return () )

let test_delegate_compound_boundary () =
  run_from_initial_state ~compare_with:"delegate_compound_boundary"
    M.(
      (* Epoch 1 - Add validator *)
      let auth_address = address "0xdeadbeef" in
      let$ {val_id; sign_address} =
        expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ()
      in

      let$ () = skip_to_next_epoch in

      (* Epoch 2 - validator gets reward and compounds it in snapshot *)
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = snapshot in

      let$ _ = expect_ok <$> call compound_function ~sender:auth_address [val_id] in
      let$ del = !$(Variables.delegator (val_id, auth_address)) in
      check u256 "del.rewards" U256.zero del.rewards ;
      check u256 "del.stake" active_validator_stake del.stake ;
      check u256 "del.next_delta_stake" reward del.next_delta_stake ;
      check epoch "del.next_delta_epoch" Epoch.(of_int 4) del.epochs.next_delta_epoch ;

      let$ () = inc_epoch in

      (* Epoch 3 - validator compounds touches state *)
      let$ () = pull_delegator_up_to_date val_id auth_address in
      let$ del = !$(Variables.delegator (val_id, auth_address)) in
      check u256 "del.rewards" U256.zero del.rewards ;
      check u256 "del.stake" active_validator_stake del.stake ;
      check u256 "del.delta_stake" reward del.delta_stake ;
      check u256 "del.next_delta_stake" U256.zero del.next_delta_stake ;
      check epoch "del.delta_epoch" Epoch.(of_int 4) del.epochs.delta_epoch ;
      check epoch "del.next_delta_epoch" Epoch.zero del.epochs.next_delta_epoch ;

      let$ () = skip_to_next_epoch in

      (* Epoch 4 - Compound rewards should take effect now. *)
      let$ _ = expect_ok <$> call compound_function ~sender:auth_address [val_id] in
      let$ del = !$(Variables.delegator (val_id, auth_address)) in
      check u256 "del.rewards" U256.zero del.rewards ;
      check u256 "del.stake" U256.(active_validator_stake + reward) del.stake ;
      check u256 "del.delta_stake" U256.zero del.delta_stake ;
      check u256 "del.next_delta_stake" U256.zero del.next_delta_stake ;
      check epoch "del.delta_epoch" Epoch.zero del.epochs.delta_epoch ;
      check epoch "del.next_delta_epoch" Epoch.zero del.epochs.next_delta_epoch ;

      return () )

let test_delegate_compound () =
  run_from_initial_state ~compare_with:"delegate_compound"
    M.(
      (* Epoch 1. *)
      let auth_address = address "0xdeadbeef" in
      let$ {val_id; sign_address} =
        expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ()
      in
      let reward = U256.(~$50 * mon) in

      let d0 = address "0xaaaabbbb" in
      let d1 = address "0xbbbbaaaa" in
      let d2 = address "0xbbbbaaaabbbb" in

      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:d0 ~value:active_validator_stake in
      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:d1 ~value:active_validator_stake in
      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:d2 ~value:active_validator_stake in
      let$ ve = !$(Variables.val_execution val_id) in
      check u256 "val.stake" U256.(~$4 * active_validator_stake) ve.Val_execution.stake ;
      let$ () = skip_to_next_epoch in

      (* Epoch 2. *)
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      let$ () =
        check_delegator_state ~val_id ~delegator:auth_address ~expected_stake:active_validator_stake
          ~expected_rewards:U256.(reward / ~$4 * ~$1)
      in
      let$ () =
        check_delegator_state ~val_id ~delegator:d0 ~expected_stake:active_validator_stake
          ~expected_rewards:U256.(reward / ~$4 * ~$1)
      in

      let$ _ = expect_ok <$> call compound_function ~sender:auth_address [val_id] in
      let$ _ = expect_ok <$> call compound_function ~sender:d0 [val_id] in

      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      let$ () =
        check_delegator_state ~val_id ~delegator:auth_address ~expected_stake:active_validator_stake
          ~expected_rewards:U256.(reward / ~$4 * ~$1)
      in
      let$ () =
        check_delegator_state ~val_id ~delegator:d1 ~expected_stake:active_validator_stake
          ~expected_rewards:U256.(reward / ~$4 * ~$2)
      in

      let$ _ = expect_ok <$> call compound_function ~sender:auth_address [val_id] in
      let$ _ = expect_ok <$> call compound_function ~sender:d1 [val_id] in

      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      let$ () =
        check_delegator_state ~val_id ~delegator:auth_address ~expected_stake:active_validator_stake
          ~expected_rewards:U256.(reward / ~$4 * ~$1)
      in
      let$ () =
        check_delegator_state ~val_id ~delegator:d2 ~expected_stake:active_validator_stake
          ~expected_rewards:U256.(reward / ~$4 * ~$3)
      in

      let$ _ = expect_ok <$> call compound_function ~sender:auth_address [val_id] in
      let$ _ = expect_ok <$> call compound_function ~sender:d2 [val_id] in

      let$ () = snapshot in

      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      let$ () =
        check_delegator_state ~val_id ~delegator:auth_address ~expected_stake:active_validator_stake
          ~expected_rewards:U256.(reward / ~$4 * ~$1)
      in
      let$ () =
        check_delegator_state ~val_id ~delegator:d0 ~expected_stake:active_validator_stake
          ~expected_rewards:U256.(reward / ~$4 * ~$3)
      in

      let$ _ = expect_ok <$> call compound_function ~sender:auth_address [val_id] in
      let$ _ = expect_ok <$> call compound_function ~sender:d0 [val_id] in

      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      let$ () =
        check_delegator_state ~val_id ~delegator:auth_address ~expected_stake:active_validator_stake
          ~expected_rewards:U256.(reward / ~$4 * ~$1)
      in
      let$ () =
        check_delegator_state ~val_id ~delegator:d1 ~expected_stake:active_validator_stake
          ~expected_rewards:U256.(reward / ~$4 * ~$3)
      in

      let$ _ = expect_ok <$> call compound_function ~sender:auth_address [val_id] in
      let$ _ = expect_ok <$> call compound_function ~sender:d1 [val_id] in

      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      let$ () =
        check_delegator_state ~val_id ~delegator:auth_address ~expected_stake:active_validator_stake
          ~expected_rewards:U256.(reward / ~$4 * ~$1)
      in
      let$ () =
        check_delegator_state ~val_id ~delegator:d2 ~expected_stake:active_validator_stake
          ~expected_rewards:U256.(reward / ~$4 * ~$3)
      in

      let$ _ = expect_ok <$> call compound_function ~sender:auth_address [val_id] in
      let$ _ = expect_ok <$> call compound_function ~sender:d2 [val_id] in

      let$ () = inc_epoch in

      (* Epoch 3 - compound reward is now active *)
      let$ () =
        check_delegator_state ~val_id ~delegator:auth_address
          ~expected_stake:U256.(active_validator_stake + (reward / ~$4 * ~$3))
          ~expected_rewards:U256.zero
      in
      let$ () =
        check_delegator_state ~val_id ~delegator:d0
          ~expected_stake:U256.(active_validator_stake + (reward / ~$4 * ~$1))
          ~expected_rewards:U256.(reward / ~$4 * ~$2)
      in
      let$ () =
        check_delegator_state ~val_id ~delegator:d1
          ~expected_stake:U256.(active_validator_stake + (reward / ~$4 * ~$2))
          ~expected_rewards:U256.(reward / ~$4 * ~$1)
      in
      let$ () =
        check_delegator_state ~val_id ~delegator:d2
          ~expected_stake:U256.(active_validator_stake + (reward / ~$4 * ~$3))
          ~expected_rewards:U256.zero
      in

      let$ _ = expect_ok <$> call compound_function ~sender:d0 [val_id] in

      let$ () = snapshot in

      let$ _ = expect_ok <$> call compound_function ~sender:d1 [val_id] in

      let$ () = inc_epoch in
      let$ () = pull_delegator_up_to_date val_id auth_address in
      let$ () = pull_delegator_up_to_date val_id d0 in
      let$ () = pull_delegator_up_to_date val_id d1 in
      let$ () = pull_delegator_up_to_date val_id d2 in

      let$ () =
        check_delegator_state ~val_id ~delegator:auth_address
          ~expected_stake:U256.(active_validator_stake + (reward / ~$4 * ~$6))
          ~expected_rewards:U256.zero
      in
      let$ () =
        check_delegator_state ~val_id ~delegator:d0
          ~expected_stake:U256.(active_validator_stake + (reward / ~$4 * ~$6))
          ~expected_rewards:U256.zero
      in
      let$ () =
        check_delegator_state ~val_id ~delegator:d1
          ~expected_stake:U256.(active_validator_stake + (reward / ~$4 * ~$5))
          ~expected_rewards:U256.zero
      in
      let$ () =
        check_delegator_state ~val_id ~delegator:d2
          ~expected_stake:U256.(active_validator_stake + (reward / ~$4 * ~$6))
          ~expected_rewards:U256.zero
      in

      let$ () = skip_to_next_epoch in

      let$ () =
        check_delegator_state ~val_id ~delegator:d1
          ~expected_stake:U256.(active_validator_stake + (reward / ~$4 * ~$6))
          ~expected_rewards:U256.zero
      in

      return () )

let test_undelegate_compound () =
  run_from_initial_state ~compare_with:"undelegate_compound"
    M.(
      let reward = U256.(~$10 * mon) in
      let auth_address = address "0xdeadbeef" in
      let d0 = address "0xaaaabbbb" in
      let d1 = address "0xbbbbaaaa" in
      let$ {val_id; sign_address} =
        expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ()
      in

      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:d0 ~value:active_validator_stake in
      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:d1 ~value:active_validator_stake in

      let$ ve = !$(Variables.val_execution val_id) in
      check u256 "val.stake" U256.(~$3 * active_validator_stake) ve.Val_execution.stake ;
      let$ () = skip_to_next_epoch in

      (* Epoch 2. *)
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      let$ () =
        check_delegator_state ~val_id ~delegator:auth_address ~expected_stake:active_validator_stake
          ~expected_rewards:U256.(reward / ~$3 * ~$2)
      in
      let$ () =
        check_delegator_state ~val_id ~delegator:d0 ~expected_stake:active_validator_stake
          ~expected_rewards:U256.(reward / ~$3 * ~$2)
      in
      let$ () =
        check_delegator_state ~val_id ~delegator:d1 ~expected_stake:active_validator_stake
          ~expected_rewards:U256.(reward / ~$3 * ~$2)
      in

      let$ _ = expect_ok <$> call compound_function ~sender:auth_address [val_id] in
      let$ _ = expect_ok <$> call compound_function ~sender:d0 [val_id] in
      let$ _ = expect_ok <$> call compound_function ~sender:d1 [val_id] in

      let withdrawal_id = U8.one in

      let$ _ =
        expect_ok <$> call undelegate_function ~sender:d0 [val_id; active_validator_stake; withdrawal_id]
      in
      let$ () =
        check_delegator_state ~val_id ~delegator:d0 ~expected_stake:U256.zero ~expected_rewards:U256.zero
      in

      let$ () = snapshot in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () =
        check_delegator_state ~val_id ~delegator:auth_address ~expected_stake:active_validator_stake
          ~expected_rewards:U256.(reward / ~$3 * ~$1)
      in
      let$ () =
        check_delegator_state ~val_id ~delegator:d0 ~expected_stake:U256.zero ~expected_rewards:U256.zero
      in

      let$ _ = expect_ok <$> call compound_function ~sender:auth_address [val_id] in
      let$ _ = expect_ok <$> call compound_function ~sender:d0 [val_id] in
      let$ _ = expect_ok <$> call compound_function ~sender:d1 [val_id] in
      let$ _ =
        expect_ok <$> call undelegate_function ~sender:d1 [val_id; active_validator_stake; withdrawal_id]
      in

      let$ () =
        check_delegator_state ~val_id ~delegator:d1 ~expected_stake:U256.zero ~expected_rewards:U256.zero
      in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      let$ () = inc_epoch in
      (* Epoch 3 *)
      let$ () =
        check_delegator_state ~val_id ~delegator:auth_address
          ~expected_stake:U256.(active_validator_stake + (reward / ~$3 * ~$2))
          ~expected_rewards:U256.(reward / ~$3)
      in
      let$ () =
        check_delegator_state ~val_id ~delegator:d0
          ~expected_stake:U256.(reward / ~$3 * ~$2)
          ~expected_rewards:U256.zero
      in
      let$ () =
        check_delegator_state ~val_id ~delegator:d1
          ~expected_stake:U256.(reward / ~$3 * ~$2)
          ~expected_rewards:U256.zero
      in

      let$ () = skip_to_next_epoch in
      let$ () = skip_to_next_epoch in
      let$ () = skip_to_next_epoch in

      let$ _ = expect_ok <$> call withdraw_function ~sender:d0 [val_id; withdrawal_id] in
      let$ _ = expect_ok <$> call withdraw_function ~sender:d1 [val_id; withdrawal_id] in
      let$ () =
        check u256 "balance d0" U256.(active_validator_stake + (reward / ~$3 * ~$2))
        <$> !(TransactionState.balance d0)
      in
      let$ () =
        check u256 "balance d1" U256.(active_validator_stake + (reward / ~$3))
        <$> !(TransactionState.balance d1)
      in

      return () )

let test_undelegate_compound_partial () =
  run_from_initial_state ~compare_with:"undelegate_compound_partial"
    M.(
      let reward = U256.(~$10 * mon) in
      let auth_address = address "0xdeadbeef" in
      let d0 = address "0xaaaabbbb" in
      let d1 = address "0xbbbbaaaa" in
      let$ {val_id; sign_address} =
        expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ()
      in

      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:d0 ~value:active_validator_stake in
      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:d1 ~value:active_validator_stake in

      let$ ve = !$(Variables.val_execution val_id) in
      check u256 "val.stake" U256.(~$3 * active_validator_stake) ve.Val_execution.stake ;
      let$ () = skip_to_next_epoch in

      (* Epoch 2. *)
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      let$ () =
        check_delegator_state ~val_id ~delegator:auth_address ~expected_stake:active_validator_stake
          ~expected_rewards:U256.(reward / ~$3 * ~$2)
      in
      let$ () =
        check_delegator_state ~val_id ~delegator:d0 ~expected_stake:active_validator_stake
          ~expected_rewards:U256.(reward / ~$3 * ~$2)
      in
      let$ () =
        check_delegator_state ~val_id ~delegator:d1 ~expected_stake:active_validator_stake
          ~expected_rewards:U256.(reward / ~$3 * ~$2)
      in

      let$ _ = expect_ok <$> call compound_function ~sender:auth_address [val_id] in
      let$ _ = expect_ok <$> call compound_function ~sender:d0 [val_id] in
      let$ _ = expect_ok <$> call compound_function ~sender:d1 [val_id] in

      let withdrawal_id = U8.one in
      let$ _ =
        expect_ok
        <$> call undelegate_function ~sender:d0 [val_id; U256.(active_validator_stake / ~$2); withdrawal_id]
      in
      let$ () =
        check_delegator_state ~val_id ~delegator:d0
          ~expected_stake:U256.(active_validator_stake / ~$2)
          ~expected_rewards:U256.zero
      in

      let$ () = snapshot in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      let$ () =
        check_delegator_state ~val_id ~delegator:auth_address ~expected_stake:active_validator_stake
          ~expected_rewards:U256.(reward / ~$3 * ~$1)
      in
      let$ () =
        check_delegator_state ~val_id ~delegator:d0
          ~expected_stake:U256.(active_validator_stake / ~$2)
          ~expected_rewards:U256.(reward / ~$6)
      in

      let$ _ = expect_ok <$> call compound_function ~sender:auth_address [val_id] in
      let$ _ = expect_ok <$> call compound_function ~sender:d0 [val_id] in
      let$ _ = expect_ok <$> call compound_function ~sender:d1 [val_id] in
      let$ _ =
        expect_ok
        <$> call undelegate_function ~sender:d1 [val_id; U256.(active_validator_stake / ~$2); withdrawal_id]
      in
      let$ () =
        check_delegator_state ~val_id ~delegator:d1
          ~expected_stake:U256.(active_validator_stake / ~$2)
          ~expected_rewards:U256.zero
      in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      let$ () = inc_epoch in
      (* Epoch 3 *)
      let$ () =
        check_delegator_state ~val_id ~delegator:auth_address
          ~expected_stake:U256.(active_validator_stake + (reward / ~$3 * ~$2))
          ~expected_rewards:U256.(reward / ~$3)
      in
      let$ () =
        check_delegator_state ~val_id ~delegator:d0
          ~expected_stake:U256.((active_validator_stake / ~$2) + (reward / ~$3 * ~$2))
          ~expected_rewards:U256.(reward / ~$6)
      in
      let$ () =
        check_delegator_state ~val_id ~delegator:d1
          ~expected_stake:U256.((active_validator_stake / ~$2) + (reward / ~$3 * ~$2))
          ~expected_rewards:U256.(reward / ~$6)
      in

      let$ () = skip_to_next_epoch in
      let$ () = skip_to_next_epoch in
      let$ () = skip_to_next_epoch in

      let$ _ = expect_ok <$> call withdraw_function ~sender:d0 [val_id; withdrawal_id] in
      let$ _ = expect_ok <$> call withdraw_function ~sender:d1 [val_id; withdrawal_id] in
      let$ () =
        check u256 "balance d0" U256.((active_validator_stake / ~$2) + (reward / ~$3))
        <$> !(TransactionState.balance d0)
      in
      let$ () =
        check u256 "balance d1" U256.((active_validator_stake / ~$2) + (reward / ~$6))
        <$> !(TransactionState.balance d1)
      in

      let$ () =
        check_delegator_state ~val_id ~delegator:d0
          ~expected_stake:U256.((active_validator_stake / ~$2) + (reward / ~$3 * ~$2) + (reward / ~$6))
          ~expected_rewards:U256.(reward / ~$6)
      in
      let$ () =
        check_delegator_state ~val_id ~delegator:d1
          ~expected_stake:U256.((active_validator_stake / ~$2) + (reward / ~$3 * ~$2) + (reward / ~$3))
          ~expected_rewards:U256.(reward / ~$6)
      in

      return () )

(**** Undelegate tests. ****)

let test_undelegate_revert_insufficient_funds () =
  run_from_initial_state ~compare_with:"undelegate_revert_insufficient_funds"
    M.(
      let auth_address = address "0xdeadbeef" in
      let del_address = address "0xaaaabbbb" in
      let$ {val_id; _} = expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake () in
      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:del_address ~value:active_validator_stake in
      let$ () = skip_to_next_epoch in

      let withdrawal_id = U8.one in
      let$ () =
        expect_error Insufficient_stake
        <$> call undelegate_function ~sender:del_address
              [val_id; U256.(active_validator_stake + ~$1); withdrawal_id]
      in

      let$ () = pull_delegator_up_to_date val_id auth_address in
      let$ del = !$(Variables.delegator (val_id, auth_address)) in
      check u256 "del.stake" active_validator_stake del.stake ;
      check u256 "del.rewards" U256.zero del.rewards ;

      let$ () = check u256 "balance del_address" U256.zero <$> !(TransactionState.balance del_address) in

      return () )

let test_undelegate_boundary_pool () =
  run_from_initial_state ~compare_with:"undelegate_boundary_pool"
    M.(
      let auth_address = address "0xdeadbeef" in
      let del_address = address "0xaaaabbbb" in
      let$ {val_id; sign_address} =
        expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ()
      in
      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:del_address ~value:active_validator_stake in
      let$ () = skip_to_next_epoch in

      (* Undelegate this epoch. *)
      let withdrawal_id = U8.one in
      let$ _ =
        expect_ok
        <$> call undelegate_function ~sender:del_address [val_id; active_validator_stake; withdrawal_id]
      in

      (* Reward during the block boundary. *)
      let$ () = snapshot in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      (* Skip delay. *)
      let$ () = inc_epoch in

      let$ () = pull_delegator_up_to_date val_id auth_address in
      let$ () = pull_delegator_up_to_date val_id del_address in

      (* Validator should get all the rewards since the secondary delegator
         does not become active in the consensus view until after the window
         expires. *)
      let$ del_auth = !$(Variables.delegator (val_id, auth_address)) in
      check u256 "del_auth.rewards" U256.(reward / ~$2) del_auth.rewards ;
      let$ del_del = !$(Variables.delegator (val_id, del_address)) in
      check u256 "del_del.stake" U256.zero del_del.stake ;
      check u256 "del_del.rewards" U256.zero del_del.rewards ;

      let$ () =
        expect_error Withdrawal_not_ready
        <$> call withdraw_function ~sender:del_address [val_id; withdrawal_id]
      in

      (* Reward the validator in this epoch which the delegator should not
         get. he has a 1 epoch delay where he continues to deactivate, and
         another epoch delay for the slashing window in which no rewards are
         earned. *)
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      let$ () = skip_to_next_epoch in

      (* Withdrawal should succeed. *)
      let$ _ = expect_ok <$> call withdraw_function ~sender:del_address [val_id; withdrawal_id] in

      (* Primary delegator get all the rewards after the secondary delegator
         becomes inactive. *)
      let$ () = pull_delegator_up_to_date val_id auth_address in
      let$ del_auth = !$(Variables.delegator (val_id, auth_address)) in
      check u256 "del_auth.rewards final" U256.(reward + (reward / ~$2)) del_auth.rewards ;

      (* Delegator gets his principal and rewards accured during deactivation
         period. *)
      let$ () =
        check u256 "balance del_address" U256.(active_validator_stake + (reward / ~$2))
        <$> !(TransactionState.balance del_address)
      in

      return () )

let test_undelegate_snapshot_boundary_pool () =
  run_from_initial_state ~compare_with:"undelegate_snapshot_boundary_pool"
    M.(
      let auth_address = address "0xdeadbeef" in
      let del_address = address "0xaaaabbbb" in
      let$ {val_id; sign_address} =
        expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ()
      in
      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:del_address ~value:active_validator_stake in
      let$ () = skip_to_next_epoch in

      (* Undelegate this epoch. *)
      let withdrawal_id = U8.one in

      (* Reward during the block boundary. *)
      let$ () = snapshot in
      let$ _ =
        expect_ok
        <$> call undelegate_function ~sender:del_address [val_id; active_validator_stake; withdrawal_id]
      in

      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      (* Skip delay. *)
      let$ () = inc_epoch in

      let$ () = pull_delegator_up_to_date val_id auth_address in
      let$ () = pull_delegator_up_to_date val_id del_address in

      let$ del_auth = !$(Variables.delegator (val_id, auth_address)) in
      check u256 "del_auth.rewards" U256.(reward / ~$2) del_auth.rewards ;
      let$ del_del = !$(Variables.delegator (val_id, del_address)) in
      check u256 "del_del.stake" U256.zero del_del.stake ;
      check u256 "del_del.rewards" U256.zero del_del.rewards ;

      let$ () =
        expect_error Withdrawal_not_ready
        <$> call withdraw_function ~sender:del_address [val_id; withdrawal_id]
      in

      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      let$ () = skip_to_next_epoch in
      let$ () = skip_to_next_epoch in

      (* Withdrawal should succeed. *)
      let$ _ = expect_ok <$> call withdraw_function ~sender:del_address [val_id; withdrawal_id] in

      let$ () = pull_delegator_up_to_date val_id auth_address in
      let$ del_auth = !$(Variables.delegator (val_id, auth_address)) in
      check u256 "del_auth.rewards final" reward del_auth.rewards ;

      let$ () =
        check u256 "balance del_address" U256.(active_validator_stake + reward)
        <$> !(TransactionState.balance del_address)
      in

      return () )

(**** Withdraw tests. ****)

let test_double_withdraw () =
  run_from_initial_state ~compare_with:"double_withdraw"
    M.(
      let auth_address = address "0xdeadbeef" in
      let$ {val_id; _} = expect_ok <$> add_validator_wrapper ~auth_address ~stake:min_auth_address_stake () in
      let$ () = skip_to_next_epoch in
      let$ _ =
        expect_ok <$> call undelegate_function ~sender:auth_address [val_id; min_auth_address_stake; U8.one]
      in
      let$ () = skip_to_next_epoch in
      let$ () = skip_to_next_epoch in
      let$ () = check u256 "balance before" U256.zero <$> !(TransactionState.balance auth_address) in
      let$ _ = expect_ok <$> call withdraw_function ~sender:auth_address [val_id; U8.one] in
      let$ () =
        check u256 "balance after withdraw" min_auth_address_stake
        <$> !(TransactionState.balance auth_address)
      in
      let$ () =
        expect_error Unknown_withdrawal_id <$> call withdraw_function ~sender:auth_address [val_id; U8.one]
      in
      let$ () =
        check u256 "balance unchanged" min_auth_address_stake <$> !(TransactionState.balance auth_address)
      in
      return () )

let test_withdraw_reusable_id () =
  run_from_initial_state ~compare_with:"withdraw_reusable_id"
    M.(
      let auth_address = address "0xdeadbeef" in
      let$ {val_id; _} = expect_ok <$> add_validator_wrapper ~auth_address ~stake:min_auth_address_stake () in
      let$ () = skip_to_next_epoch in
      let$ _ =
        expect_ok <$> call undelegate_function ~sender:auth_address [val_id; min_auth_address_stake; U8.one]
      in
      let$ () = skip_to_next_epoch in
      let$ () = skip_to_next_epoch in
      let$ _ = expect_ok <$> call withdraw_function ~sender:auth_address [val_id; U8.one] in

      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:auth_address ~value:active_validator_stake in

      let$ () = skip_to_next_epoch in
      let$ () = skip_to_next_epoch in

      let$ _ =
        expect_ok <$> call undelegate_function ~sender:auth_address [val_id; min_auth_address_stake; U8.one]
      in

      let$ () = skip_to_next_epoch in
      let$ () = skip_to_next_epoch in
      let$ _ = expect_ok <$> call withdraw_function ~sender:auth_address [val_id; U8.one] in
      return () )

(**** claim_rewards tests. ****)

let test_claim_rewards () =
  run_from_initial_state ~compare_with:"claim_rewards"
    M.(
      let auth_address = address "0xdeadbeef" in
      let$ {val_id; sign_address} =
        expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ()
      in
      let$ () = skip_to_next_epoch in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = check u256 "balance before" U256.zero <$> !(TransactionState.balance auth_address) in
      let$ _ = expect_ok <$> call claim_rewards_function ~sender:auth_address [val_id] in
      let$ () = check u256 "balance after" reward <$> !(TransactionState.balance auth_address) in
      return () )

let test_claim_noop () =
  run_from_initial_state ~compare_with:"claim_noop"
    M.(
      let auth_address = address "0xdeadbeef" in
      let$ {val_id; _} = expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake () in
      let$ () = skip_to_next_epoch in
      let$ () = check u256 "balance before" U256.zero <$> !(TransactionState.balance auth_address) in
      let$ _ = expect_ok <$> call claim_rewards_function ~sender:auth_address [val_id] in
      let$ () = check u256 "balance after" U256.zero <$> !(TransactionState.balance auth_address) in
      return () )

let test_claim_rewards_compound () =
  run_from_initial_state ~compare_with:"claim_rewards_compound"
    M.(
      let auth_address = address "0xdeadbeef" in
      let$ {val_id; sign_address} =
        expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ()
      in
      let$ () = skip_to_next_epoch in

      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () = check u256 "balance 1" U256.zero <$> !(TransactionState.balance auth_address) in
      let$ _ = expect_ok <$> call claim_rewards_function ~sender:auth_address [val_id] in
      let$ () = check u256 "balance 2" reward <$> !(TransactionState.balance auth_address) in

      let$ _ = expect_ok <$> call compound_function ~sender:auth_address [val_id] in
      let$ () = snapshot in
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

      let$ () = check u256 "balance 3" reward <$> !(TransactionState.balance auth_address) in
      let$ _ = expect_ok <$> call claim_rewards_function ~sender:auth_address [val_id] in
      let$ () = check u256 "balance 4" U256.(~$2 * reward) <$> !(TransactionState.balance auth_address) in

      let$ _ = expect_ok <$> call compound_function ~sender:auth_address [val_id] in
      let$ () =
        check_delegator_state ~val_id ~delegator:auth_address ~expected_stake:active_validator_stake
          ~expected_rewards:U256.zero
      in
      let$ () = inc_epoch in
      let$ () =
        check_delegator_state ~val_id ~delegator:auth_address ~expected_stake:active_validator_stake
          ~expected_rewards:U256.zero
      in
      return () )

(**** sys_call_reward tests. ****)

let test_reward_unknown_validator () =
  run_from_initial_state ~compare_with:"reward_unknown_validator"
    M.(
      let unknown = address "0x1234" in
      let$ _ =
        expect_error Not_in_validator_set <$> syscall syscall_reward_function ~value:reward [unknown]
      in
      return () )

let test_reward_crash_no_snapshot_missing_validator () =
  run_from_initial_state ~compare_with:"reward_crash_no_snapshot_missing_validator"
    M.(
      let auth_address = address "0xdeadbeef" in
      let$ {val_id = _; sign_address} =
        expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ()
      in
      let$ () = inc_epoch in
      let$ () =
        expect_error Not_in_validator_set <$> syscall syscall_reward_function ~value:reward [sign_address]
      in
      return () )

let test_reward_sets_block_proposer () =
  run_from_initial_state ~compare_with:"reward_sets_block_proposer"
    M.(
      let$ vals =
        List.mapM
          ~f:(fun secret ->
            expect_ok
            <$> add_validator_wrapper ~auth_address:(address "0xdeadbeef") ~stake:active_validator_stake
                  ~commission:U256.zero ~secret () )
          [B32.of_hex_string "0x01"; B32.of_hex_string "0x02"; B32.of_hex_string "0x03"]
      in

      let$ () = skip_to_next_epoch in

      let$ () =
        List.iterM
          ~f:(fun {val_id; sign_address} ->
            let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in

            (* The spec does not implement old forks so we take the >= MONAD_FIVE branch is tested here. *)
            let$ proposer = !$Variables.proposer_val_id in
            check validator_id "proposer_val_id slot" val_id proposer ;

            let$ getter_result = expect_ok <$> call get_proposer_val_id_function ~sender:Address.zero [] in
            check validator_id "proposer_val_id getter" val_id getter_result ;

            return () )
          vals
      in
      return () )

(**** sys_call_snapshot tests. ****)

let test_multiple_snapshot_error () =
  run_from_initial_state ~compare_with:"multiple_snapshot_error"
    M.(
      let$ () = snapshot in
      let$ () = expect_error Snapshot_in_boundary <$> syscall syscall_snapshot_function [] in
      let$ () = inc_epoch in
      let$ () = snapshot in
      return () )

let test_valset_exceeds_n () =
  run_from_initial_state ~compare_with:"valset_exceeds_n"
    M.(
      let active_valset_size = 200 in
      let$ vals =
        List.mapM
          ~f:(fun (i : int) ->
            let stake = U256.(active_validator_stake + ~$Stdlib.(1000 - i)) in
            let secret = B32.of_hex_string (Printf.sprintf "0x%04x" i) in
            let$ {val_id; _} =
              expect_ok
              <$> add_validator_wrapper ~auth_address:(address "0xdeadbeef") ~stake ~commission:U256.zero
                    ~secret ()
            in
            return (val_id, stake) )
          (List.init 1000 (fun i -> i + 1))
      in
      let$ () =
        let ve = Storage.Array.read_to_list Variables.valset_execution in
        check int "valset_execution length" 1000 <$> (List.length <$> ve)
      in

      let$ () = skip_to_next_epoch in
      let$ () =
        let vs = Storage.Array.read_to_list Variables.valset_snapshot in
        check int "valset_snapshot length" 0 <$> (List.length <$> vs)
      in
      let$ () =
        let vc = Storage.Array.read_to_list Variables.valset_consensus in
        check int "valset_consensus length" active_valset_size <$> (List.length <$> vc)
      in

      let$ valset_consensus = Storage.Array.read_to_list Variables.valset_consensus in
      let$ () =
        List.iterM
          ~f:(fun (i, (val_id, stake)) ->
            let in_valset = List.exists (fun x -> Val_id.(x = val_id)) valset_consensus in
            if i <= active_valset_size then begin
              assert' "is_in_valset" in_valset ;
              let$ cv = !$(Variables.consensus_view val_id) in
              check u256 "consensus_view.stake" stake cv.Consensus_view.stake ;
              return ()
            end
            else begin
              assert' "not_in_valset" (not in_valset) ;
              let$ cv = !$(Variables.consensus_view val_id) in
              check u256 "consensus_view.stake" U256.zero cv.Consensus_view.stake ;
              return ()
            end )
          (List.mapi (fun i x -> (i + 1, x)) vals)
      in

      let$ () = skip_to_next_epoch in
      let$ () =
        check int "valset_snapshot length 2" active_valset_size
        <$> (List.length <$> Storage.Array.read_to_list Variables.valset_snapshot)
      in
      let$ () =
        check int "valset_consensus length 2" active_valset_size
        <$> (List.length <$> Storage.Array.read_to_list Variables.valset_consensus)
      in

      return () )

(**** sys_call_epoch_change tests. ****)

let test_epoch_goes_backwards () =
  run_from_initial_state ~compare_with:"epoch_goes_backwards"
    M.(
      let$ () = expect_ok <$> syscall syscall_on_epoch_change_function [Epoch.of_int 3] in
      let$ () = expect_error Invalid_epoch_change <$> syscall syscall_on_epoch_change_function [Epoch.one] in
      let$ () =
        expect_error Invalid_epoch_change <$> syscall syscall_on_epoch_change_function [Epoch.of_int 2]
      in
      let$ () =
        expect_error Invalid_epoch_change <$> syscall syscall_on_epoch_change_function [Epoch.of_int 3]
      in
      let$ () = expect_ok <$> syscall syscall_on_epoch_change_function [Epoch.of_int 4] in
      return () )

let test_contract_bootstrap () =
  run_from_initial_state ~compare_with:"contract_bootstrap"
    M.(
      let e = Epoch.of_int 20 in
      let e_prev = Epoch.of_int 19 in
      let$ () = Variables.epoch $= Epoch.zero in

      (* Consensus initializes the epoch by calling epoch change. *)
      let$ () = expect_ok <$> syscall syscall_on_epoch_change_function [e_prev] in

      (* Sets should be empty. *)
      let$ () =
        check int "valset_execution length" 0
        <$> (List.length <$> Storage.Array.read_to_list Variables.valset_execution)
      in
      let$ () =
        check int "valset_snapshot length" 0
        <$> (List.length <$> Storage.Array.read_to_list Variables.valset_snapshot)
      in
      let$ () =
        check int "valset_consensus length" 0
        <$> (List.length <$> Storage.Array.read_to_list Variables.valset_consensus)
      in
      let$ ep = !$Variables.epoch in
      check epoch "epoch" e_prev ep ;

      let auth_address = address "0xdeadbeef" in

      (* Add two validators. *)
      let$ {val_id = val1_id; _} =
        expect_ok
        <$> add_validator_wrapper ~auth_address ~stake:min_auth_address_stake ~commission:U256.zero
              ~secret:(B32.of_hex_string "0x1000") ()
      in
      let$ {val_id = val2_id; _} =
        expect_ok
        <$> add_validator_wrapper ~auth_address ~stake:min_auth_address_stake ~commission:U256.zero
              ~secret:(B32.of_hex_string "0x1002") ()
      in

      (* Delegate with validator 1. *)
      let d1 = address "0xaaaabbbb" in
      let$ _ = expect_ok <$> delegate_and_credit val1_id ~sender:d1 ~value:U256.(~$10 * mon) in
      let$ _ = expect_ok <$> delegate_and_credit val1_id ~sender:d1 ~value:active_validator_stake in

      (* Verify no undelegations before activation. *)
      let$ () =
        expect_error Insufficient_stake
        <$> call undelegate_function ~sender:d1 [val1_id; active_validator_stake; U8.one]
      in

      (* Verify withdrawals don't work. *)
      let$ () =
        List.iterM
          ~f:(fun i ->
            let$ () =
              expect_error Unknown_withdrawal_id <$> call withdraw_function ~sender:d1 [val1_id; U8.of_int i]
            in
            return () )
          (List.init 256 Fun.id)
      in

      let$ () = snapshot in
      let$ () = expect_ok <$> syscall syscall_on_epoch_change_function [e] in

      (* All delegators have their principal (no rewards earned). *)
      let$ () =
        check_delegator_state ~val_id:val1_id ~delegator:auth_address ~expected_stake:min_auth_address_stake
          ~expected_rewards:U256.zero
      in
      let$ () =
        check_delegator_state ~val_id:val1_id ~delegator:d1
          ~expected_stake:U256.((~$10 * mon) + active_validator_stake)
          ~expected_rewards:U256.zero
      in
      let$ () =
        check_delegator_state ~val_id:val2_id ~delegator:auth_address ~expected_stake:min_auth_address_stake
          ~expected_rewards:U256.zero
      in

      (* Only one of the validators had enough stake to be active. *)
      let$ () =
        check int "valset_consensus length" 1
        <$> (List.length <$> Storage.Array.read_to_list Variables.valset_consensus)
      in
      let$ () =
        check int "valset_snapshot length" 0
        <$> (List.length <$> Storage.Array.read_to_list Variables.valset_snapshot)
      in
      let$ valset_consensus = Storage.Array.read_to_list Variables.valset_consensus in
      check validator_id "valset_consensus[0]" val1_id (List.nth valset_consensus 0) ;

      (* Check: accumulator refcounts are cleared. *)
      let$ acc = !$(Variables.accumulated_reward_per_token (e_prev, val1_id)) in
      check u256 "acc.refcount" U256.zero acc.refcount ;
      check u256 "acc.value" U256.zero acc.value ;
      let$ acc2 = !$(Variables.accumulated_reward_per_token (e_prev, val2_id)) in
      check u256 "acc2.refcount" U256.zero acc2.refcount ;
      check u256 "acc2.value" U256.zero acc2.value ;

      return () )

let test_zero_reward_epochs () =
  run_from_initial_state ~compare_with:"zero_reward_epochs"
    M.(
      let auth_address = address "0xdeadbeef" in
      let delegators = [address "0xdead"; address "0xbeef"; address "0x600d"; address "0xbadd"] in
      let delegator_stake = U256.(~$1_000_000 * mon) in

      let$ () = Variables.epoch $= Epoch.of_int 49 in

      let$ validators =
        List.mapM
          ~f:(fun i ->
            let commission = if i mod 2 = 0 then U256.(mon * ~$10 / ~$100) else U256.zero in
            let secret = B32.of_hex_string (Printf.sprintf "0x%04x" (i + 1)) in
            let$ v =
              expect_ok
              <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ~commission ~secret ()
            in
            let$ () =
              List.iterM
                ~f:(fun d -> ignore <$> delegate_and_credit v.val_id ~sender:d ~value:delegator_stake)
                delegators
            in
            return v )
          (List.init 10 Fun.id)
      in

      let$ () = skip_to_next_epoch in

      let$ () =
        List.iterM
          ~f:(fun epoch ->
            let$ () =
              List.iterM
                ~f:(fun block ->
                  let proposer = (List.nth validators (block mod List.length validators)).sign_address in
                  let$ () = if block = 40 then snapshot else return () in
                  let$ () = expect_ok <$> syscall syscall_reward_function ~value:U256.zero [proposer] in
                  return () )
                (List.init 50 Fun.id)
            in
            let$ () = expect_ok <$> syscall syscall_on_epoch_change_function [Epoch.of_int epoch] in
            return () )
          (List.init 10 (fun i -> i + 51))
      in

      (* Check no staking emissions occurred. *)
      let$ () =
        check u256 "staking balance" U256.((active_validator_stake * ~$10) + (delegator_stake * ~$4 * ~$10))
        <$> !(TransactionState.balance staking_address)
      in
      let$ () =
        List.iterM
          ~f:(fun {val_id; _} ->
            let$ ve = !$(Variables.val_execution val_id) in
            check u256 "val.stake"
              U256.(active_validator_stake + (delegator_stake * ~$4))
              ve.Val_execution.stake ;
            check u256 "val.rewards_per_token" U256.zero ve.Val_execution.rewards_per_token ;
            check u256 "val.unclaimed_rewards" U256.zero ve.Val_execution.unclaimed_rewards ;

            let$ () = pull_delegator_up_to_date val_id auth_address in
            let$ auth_del = !$(Variables.delegator (val_id, auth_address)) in
            check u256 "auth_del.stake" active_validator_stake auth_del.stake ;
            check u256 "auth_del.rewards_per_token" U256.zero auth_del.rewards_per_token ;
            check u256 "auth_del.rewards" U256.zero auth_del.rewards ;

            let$ () =
              List.iterM
                ~f:(fun d ->
                  let$ () = pull_delegator_up_to_date val_id d in
                  let$ del = !$(Variables.delegator (val_id, d)) in
                  check u256 "del.stake" delegator_stake del.stake ;
                  check u256 "del.rewards_per_token" U256.zero del.rewards_per_token ;
                  check u256 "del.rewards" U256.zero del.rewards ;
                  return () )
                delegators
            in
            return () )
          validators
      in

      return () )

(**** Getter tests. ****)

let test_get_valset_empty () =
  run_from_initial_state ~compare_with:"get_valset_empty"
    M.(
      let$ () =
        assert' "List.is_empty valset_execution"
        <$> (List.is_empty <$> Storage.Array.read_to_list Variables.valset_execution)
      in
      let$ () =
        assert' "List.is_empty valset_consensus"
        <$> (List.is_empty <$> Storage.Array.read_to_list Variables.valset_consensus)
      in
      let$ () =
        assert' "List.is_empty valset_snapshot"
        <$> (List.is_empty <$> Storage.Array.read_to_list Variables.valset_snapshot)
      in
      return () )

let test_empty_get_delegators_for_validator_getter () =
  run_from_initial_state ~compare_with:"empty_get_delegators_for_validator_getter"
    M.(
      let$ () =
        (* Validator doesn't exist. *)
        let$ done_, _, delegators =
          expect_ok <$> Delegators_for_validator.traverse Val_id.one Address.zero Int.max_int
        in
        assert' "done_" done_ ;
        assert' "List.is_empty delegators" (List.is_empty delegators) ;
        return ()
      in

      let$ () =
        (* Validator exists, bogus delegator start pointer provided. *)
        let$ {val_id; _} =
          expect_ok
          <$> add_validator_wrapper ~auth_address:(address "0xdeadbeef") ~stake:active_validator_stake ()
        in
        let$ done_, _, delegators =
          expect_ok <$> Delegators_for_validator.traverse val_id (address "0x1337") Int.max_int
        in
        assert' "done_" done_ ;
        assert' "List.is_empty delegators" (List.is_empty delegators) ;
        return ()
      in

      return () )

let test_empty_get_validators_for_delegator_getter () =
  run_from_initial_state ~compare_with:"empty_get_validators_for_delegator_getter"
    M.(
      let$ () =
        (* Validator doesn't exist. *)
        let$ done_, _, validators =
          expect_ok <$> Validators_for_delegator.traverse (address "0x1337") Val_id.zero Int.max_int
        in
        assert' "done_" done_ ;
        assert' "List.is_empty validators" (List.is_empty validators) ;
        return ()
      in

      let$ () =
        (* Validator exists, bogus val_id start pointer provided. *)
        let$ _ =
          expect_ok
          <$> add_validator_wrapper ~auth_address:(address "0xdeadbeef") ~stake:active_validator_stake ()
        in
        let$ done_, _, validators =
          expect_ok <$> Validators_for_delegator.traverse (address "0x1337") Val_id.zero Int.max_int
        in
        assert' "done_" done_ ;
        assert' "List.is_empty validators" (List.is_empty validators) ;
        return ()
      in
      return () )

let test_get_delegators_for_validator () =
  run_from_initial_state ~compare_with:"get_delegators_for_validator"
    M.(
      let auth_address = address "0xdeadbeef" in

      let$ {val_id; _} = expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake () in

      let$ delegators =
        Seq.fold_leftM
          ~f:(fun delegators i ->
            let addr = Address.of_u256_truncating (U256.of_int (i + 1)) in
            let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:addr ~value:U256.(~$100 * mon) in
            (* Delegate twice to make sure duplicates are handled correctly. *)
            let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:addr ~value:U256.(~$100 * mon) in
            return (Address.Set.add addr delegators) )
          (Address.Set.singleton auth_address)
          Seq.(take 999 (ints 0))
      in

      let$ () =
        let$ done_, _, contract_delegators =
          expect_ok <$> Delegators_for_validator.traverse val_id Address.zero Int.max_int
        in
        assert' "done_" done_ ;
        check int "List.length contract_delegators" (Address.Set.cardinal delegators)
          (List.length contract_delegators) ;
        List.iter
          (fun del -> assert' "Address.Set.mem del delegators" (Address.Set.mem del delegators))
          contract_delegators ;
        return ()
      in

      (* Activate the stake so it can be undelegated. *)
      let$ () = skip_to_next_epoch in

      (* Undelegate some of the delegators. *)
      let d0 = Address.of_u256_truncating U256.(~$20) in
      let d1 = Address.of_u256_truncating U256.(~$101) in
      let d2 = Address.of_u256_truncating U256.(~$500) in
      let$ _ = expect_ok <$> call undelegate_function ~sender:d0 [val_id; U256.(~$200 * mon); U8.one] in
      let$ _ = expect_ok <$> call undelegate_function ~sender:d1 [val_id; U256.(~$200 * mon); U8.one] in
      let$ _ = expect_ok <$> call undelegate_function ~sender:d2 [val_id; U256.(~$200 * mon); U8.one] in
      let delegators = Address.(Set.(delegators |> remove d0 |> remove d1 |> remove d2)) in

      let$ () =
        let$ done_, _, contract_delegators =
          expect_ok <$> Delegators_for_validator.traverse val_id Address.zero Int.max_int
        in
        assert' "done_" done_ ;
        check int "List.length contract_delegators" (Address.Set.cardinal delegators)
          (List.length contract_delegators) ;
        List.iter
          (fun del -> assert' "Address.Set.mem del delegators" (Address.Set.mem del delegators))
          contract_delegators ;
        return ()
      in
      return () )

let test_get_validators_for_delegator () =
  (* The original monad test uses std::unordered_set, which means delegations happen in an unspecified order.
     The fixture used here was generated from a patched version of the original test, to ensure delegation
     order is consistent. *)
  run_from_initial_state ~compare_with:"get_validators_for_delegator"
    M.(
      let auth_address = address "0xdeadbeef" in
      let$ validators =
        let make_secret i = U256.(to_repr ~$Stdlib.(1000 + i)) in
        U64.Set.of_seq
        <$> Seq.mapM
              ~f:(fun i ->
                let$ {val_id = Val_id val_id; _} =
                  expect_ok
                  <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake
                        ~secret:(make_secret i) ()
                in
                return val_id )
              Seq.(take 999 (ints 0))
      in

      let del = address "0x1337" in
      let$ () =
        U64.Set.to_seq validators
        |> Seq.iterM ~f:(fun val_id ->
            let val_id = Val_id.Val_id val_id in
            (* Delegate twice with every validator. *)
            let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:del ~value:U256.(~$100 * mon) in
            ignore <$> delegate_and_credit val_id ~sender:del ~value:U256.(~$100 * mon) )
      in

      let$ () =
        let$ done_, _, contract_validators =
          expect_ok <$> Validators_for_delegator.traverse del Val_id.zero Int.max_int
        in
        assert' "done_" done_ ;
        check int "List.length contract_validators" (U64.Set.cardinal validators)
          (List.length contract_validators) ;
        List.iter
          (fun (Val_id.Val_id val_id) ->
            assert' "U64.Set.mem val_id validators" (U64.Set.mem val_id validators) )
          contract_validators ;
        return ()
      in

      (* Activate the stake so it can be undelegated. *)
      let$ () = skip_to_next_epoch in

      (* Undelegate from some of the validators. *)
      let v0 = U64.of_int 20 in
      let v1 = U64.of_int 101 in
      let v2 = U64.of_int 500 in
      let$ _ = expect_ok <$> call undelegate_function ~sender:del [Val_id v0; U256.(~$200 * mon); U8.one] in
      let$ _ = expect_ok <$> call undelegate_function ~sender:del [Val_id v1; U256.(~$200 * mon); U8.one] in
      let$ _ = expect_ok <$> call undelegate_function ~sender:del [Val_id v2; U256.(~$200 * mon); U8.one] in
      let validators = U64.(Set.(validators |> remove v0 |> remove v1 |> remove v2)) in

      let$ () =
        let$ done_, _, contract_validators =
          expect_ok <$> Validators_for_delegator.traverse del Val_id.zero Int.max_int
        in
        assert' "done_" done_ ;
        check int "List.length contract_validators" (U64.Set.cardinal validators)
          (List.length contract_validators) ;
        List.iter
          (fun (Val_id.Val_id val_id) ->
            assert' "U64.Set.mem val_id validators" (U64.Set.mem val_id validators) )
          contract_validators ;
        return ()
      in
      return () )

let test_get_valset_paginated_reads () =
  run_from_initial_state ~compare_with:"get_valset_paginated_reads"
    M.(
      let auth_address = address "0xdeadbeef" in
      let$ () =
        Seq.iterM
          ~f:(fun i ->
            let secret = U256.(to_repr ~$Stdlib.(i + 1)) in
            ignore
            <$> (expect_ok <$> add_validator_wrapper ~secret ~auth_address ~stake:active_validator_stake ()) )
          Seq.(take 999 (ints 0))
      in

      (* Read valset in one read. Note that we access the valset location directly. *)
      let$ valset_one_read = Storage.Array.read_to_list Variables.valset_execution in
      check int "List.length valset_one_read" 999 (List.length valset_one_read) ;

      (* Read valset in pages. *)
      let$ valset_paginated =
        let rec loop valset next_index =
          let$ [done_; next_index; valset_page] =
            expect_ok
            <$> get_valset Variables.valset_execution ~sender:Address.zero ~value:U256.zero [next_index]
          in
          (* This is inefficient, but it should be fine for a test. *)
          let valset = valset @ valset_page in
          if done_ then return valset else loop valset next_index
        in
        loop [] U32.zero
      in

      check (list validator_id) "valset_paginated" valset_one_read valset_paginated ;
      return () )

let test_get_delegators_for_validator_paginated_reads () =
  run_from_initial_state ~compare_with:"get_delegators_for_validator_paginated_reads"
    M.(
      let auth_address = address "0xdeadbeef" in
      let$ {val_id; _} = expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake () in
      (* This is 1000 because the auth address is a delegator. *)
      let n_delegators = 999 + 1 in

      let$ () =
        Seq.iterM
          ~f:(fun i ->
            let del = Address.of_u256_truncating (U256.of_int (i + 1)) in
            (* Delegate twice to make sure dups are handled correctly. *)
            let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:del ~value:U256.(~$100 * mon) in
            let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:del ~value:U256.(~$100 * mon) in
            return () )
          Seq.(take (n_delegators - 1) (ints 0))
      in

      (* Read all the delegators. *)
      let$ done1, _, delegators_one_read =
        expect_ok <$> Delegators_for_validator.traverse val_id Address.zero Int.max_int
      in
      assert' "done1" done1 ;
      check int "List.length delegators_one_read" n_delegators (List.length delegators_one_read) ;

      let$ delegators_paginated =
        let rec loop delegators next_delegator =
          let$ done_, next_delegator, delegators_page =
            expect_ok <$> Delegators_for_validator.traverse val_id next_delegator linked_list_pagination
          in
          let delegators = delegators @ delegators_page in
          if done_ then return delegators else loop delegators next_delegator
        in
        loop [] Address.zero
      in

      check (list Utils.address) "delegators_paginated" delegators_one_read delegators_paginated ;
      return () )

let test_get_proposer_val_id_fork () =
  (* The original C++ test does not run any API calls, so there is no meaningful post-state fixture. *)
  run_from_initial_state
    M.(
      let$ {val_id; sign_address} =
        expect_ok
        <$> add_validator_wrapper ~auth_address:(address "0xdeadbeef") ~stake:active_validator_stake ()
      in

      let$ () = skip_to_next_epoch in
      (* The spec does not implement legacy Monad versions, so we test only the >= MONAD_FIVE branch. *)
      let$ () = expect_ok <$> syscall syscall_reward_function [sign_address] in
      let$ id = expect_ok <$> call get_proposer_val_id_function ~sender:Address.zero [] in
      check validator_id "proposer_val_id = val_id" val_id id ;
      return () )

(**** Solvency tests. ****)

let test_validator_insolvent () =
  run_from_initial_state ~compare_with:"validator_insolvent"
    M.(
      let auth_address = address "0xdeadbeef" in
      let$ {val_id; _} = expect_ok <$> add_validator_wrapper ~auth_address ~stake:min_auth_address_stake () in

      let$ () = skip_to_next_epoch in

      (* Simulate an accumulator error. *)
      let$ () =
        update_field
          (Storage.Loc.lens (Variables.val_execution val_id))
          (fun v -> {v with Val_execution.rewards_per_token = U256.(~$10 * mon)})
      in

      let$ () = expect_error Solvency_error <$> call claim_rewards_function ~sender:auth_address [val_id] in

      return () )

let test_withdrawal_insolvent () =
  run_from_initial_state ~compare_with:"withdrawal_insolvent"
    M.(
      let auth_address = address "0xdeadbeef" in
      let$ {val_id; _} = expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake () in

      let$ () = skip_to_next_epoch in
      (* Activate the stake. *)
      let$ _ =
        expect_ok <$> call undelegate_function ~sender:auth_address [val_id; active_validator_stake; U8.one]
      in

      (* Simulate an accumulator error before the epoch change. This is so the error becomes part of the
         pending undelegation during this epoch. *)
      let$ () =
        update_field
          (Storage.Loc.lens (Variables.val_execution val_id))
          (fun v -> {v with Val_execution.rewards_per_token = U256.(~$10 * mon)})
      in

      let$ () = skip_to_next_epoch in
      (* Withdrawal is insolvent, but inactive. *)
      let$ () = skip_to_next_epoch in
      (* Withdrawal is insolvent and active. *)

      let$ () =
        expect_error Solvency_error <$> call withdraw_function ~sender:auth_address [val_id; U8.one]
      in

      return () )

let test_withdrawal_state_override () =
  run_from_initial_state ~compare_with:"withdrawal_state_override"
    M.(
      let auth_address = address "0xdeadbeef" in
      let$ {val_id; _} = expect_ok <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake () in

      let$ () = skip_to_next_epoch in
      let$ _ =
        expect_ok <$> call undelegate_function ~sender:auth_address [val_id; active_validator_stake; U8.one]
      in
      let$ () = skip_to_next_epoch in
      let$ () = skip_to_next_epoch in

      let$ () = TransactionState.balance staking_address := U256.zero in
      (* Here the C++ equivalent test throws an exception inside `undelegate`, and the state is not
           rolled back, so we use the same behavior, as that is what the fixture expects. *)
      let$ _ =
        expect_error Internal_error
        <$> call withdraw_function ~sender:auth_address ~on_error:`Keep [val_id; U8.one]
      in

      return () )

(**** Dust tests. ****)

let test_dust_hunter () =
  run_from_initial_state ~compare_with:"dust_hunter"
    M.(
      let auth_address = address "0xdeadbeef" in
      let delegator_addr = address "0x1234" in

      let rewards_fn stake keydata =
        let secret = B32.of_hex_string (Printf.sprintf "0x%04x" keydata) in
        let$ {val_id; sign_address} =
          expect_ok
          <$> add_validator_wrapper ~auth_address ~stake:active_validator_stake ~commission:U256.zero ~secret
                ()
        in
        let keydata = keydata + 1 in
        (* Validator keys cannot be reused. *)
        (* Set the delegator's stake manually instead of going through delegation precompile to bypass the
           dust threshold. *)
        let$ () =
          update_field
            (Storage.Loc.lens (Variables.delegator (val_id, delegator_addr)))
            (fun d -> {d with Delegator.stake})
        in
        let$ () = skip_to_next_epoch in
        let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
        let$ () = pull_delegator_up_to_date val_id delegator_addr in
        let$ del = !$(Variables.delegator (val_id, delegator_addr)) in
        return (del.rewards, keydata)
      in

      let rec loop lo hi keydata =
        if U256.(lo < hi) then
          let mid = U256.(lo + ((hi - lo + one) / ~$2)) in
          let$ r, keydata = rewards_fn mid keydata in
          if U256.(r = zero) then loop mid hi keydata else loop lo U256.(mid - one) keydata
        else return (lo, keydata)
      in

      let$ needle, keydata = loop U256.zero U256.(~$10 * mon) 1 in
      let$ r, keydata = rewards_fn needle keydata in
      check u256 "rewards_fn(needle) = 0" U256.zero r ;
      let$ r, _ = rewards_fn U256.(needle + one) keydata in
      assert' "rewards_fn(needle+1) > 0" U256.(r > zero) ;
      assert' "DUST_THRESHOLD >= needle" U256.(dust_threshold >= needle) ;

      return () )

let test_delegate_dust () =
  run_from_initial_state ~compare_with:"delegate_dust"
    M.(
      let delegator = address "0xaaaa" in
      let$ {val_id; _} =
        expect_ok
        <$> add_validator_wrapper ~auth_address:(address "0xdeadbeef") ~stake:active_validator_stake ()
      in
      let$ () = skip_to_next_epoch in

      (* Delegate. *)
      let$ () =
        expect_error Delegation_too_small
        <$> delegate_and_credit val_id ~sender:delegator ~value:U256.(dust_threshold / ~$2)
      in
      let$ () =
        expect_error Delegation_too_small
        <$> delegate_and_credit val_id ~sender:delegator ~value:U256.(dust_threshold - ~$1)
      in

      (* Above the threshold. *)
      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:delegator ~value:dust_threshold in

      (* Compound (invokes delegate). *)
      let$ () =
        let$ del = !$(Variables.delegator (val_id, delegator)) in
        Variables.delegator (val_id, delegator) $= {del with rewards = U256.(dust_threshold / ~$2)}
      in
      let$ () = expect_error Delegation_too_small <$> call compound_function ~sender:delegator [val_id] in
      let$ () =
        let$ del = !$(Variables.delegator (val_id, delegator)) in
        Variables.delegator (val_id, delegator) $= {del with rewards = U256.(dust_threshold - ~$1)}
      in
      let$ () = expect_error Delegation_too_small <$> call compound_function ~sender:delegator [val_id] in

      (* Above the threshold. *)
      let$ () =
        let$ del = !$(Variables.delegator (val_id, delegator)) in
        Variables.delegator (val_id, delegator) $= {del with rewards = dust_threshold}
      in
      let$ _ = expect_ok <$> call compound_function ~sender:delegator [val_id] in

      return () )

let test_undelegate_dust () =
  run_from_initial_state ~compare_with:"undelegate_dust"
    M.(
      let delegator = address "0xaaaa" in
      let$ {val_id; _} =
        expect_ok
        <$> add_validator_wrapper ~auth_address:(address "0xdeadbeef") ~stake:active_validator_stake ()
      in
      let$ () = skip_to_next_epoch in

      (* Delegate over the dust threshold, with an extra 300 wei dust. *)
      let$ _ =
        expect_ok <$> delegate_and_credit val_id ~sender:delegator ~value:U256.(dust_threshold + ~$300)
      in

      (* Activate delegation. *)
      let$ () = skip_to_next_epoch in
      let$ () = pull_delegator_up_to_date val_id delegator in
      let$ () =
        let$ del = !$(Variables.delegator (val_id, delegator)) in
        return (check u256 "delegator.stake = dust_threshold + 300" U256.(dust_threshold + ~$300) del.stake)
      in

      (* Undelegate, leaving the 300 we in the delegator. *)
      let$ _ = call undelegate_function ~sender:delegator [val_id; dust_threshold; U8.one] in

      (* Withdrawal request should include the dust. *)
      let$ () =
        let$ req = Option.get <$> !$(Variables.withdrawal_request (val_id, delegator, U8.one)) in
        return (check u256 "req.amount = dust_threshold + 300" U256.(dust_threshold + ~$300) req.amount)
      in

      (* Delegator should have zero balance. *)
      let$ () = pull_delegator_up_to_date val_id delegator in
      let$ () =
        let$ del = !$(Variables.delegator (val_id, delegator)) in
        return (check u256 "delegator.stake = 0" U256.zero del.stake)
      in

      let$ () = skip_to_next_epoch in
      let$ () = skip_to_next_epoch in
      let$ _ = expect_ok <$> call withdraw_function ~sender:delegator [val_id; U8.one] in
      let$ () =
        check u256 "delegator.balance = dust_threshold + 300" U256.(dust_threshold + ~$300)
        <$> !(TransactionState.balance delegator)
      in

      return () )

(**** Events tests. ****)

(* The spec does not implement old forks so only the >= MONAD_EIGHT branch is tested here. *)
let test_events () =
  run_from_initial_state ~compare_with:"events"
    M.(
      (* Logs are stored in reverse order in the transaction state. We reverse the list on access. *)
      let get_logs = List.rev <$> !TransactionState.logs in

      let auth = address "0xdeadbeef" in

      (* Add validator with enough stake to activate immediately
         1. Validator created
         2. Validator status changed to active.
         3. Delegate event *)
      let$ {val_id; sign_address} =
        expect_ok <$> add_validator_wrapper ~auth_address:auth ~stake:active_validator_stake ()
      in
      let seen_events = 0 in
      let$ () = check int "logs.size = 3" 3 <$> (List.length <$> get_logs) in
      let seen_events = seen_events + 3 in

      (* Change to new commission
         1. Commission changed event *)
      let$ _ =
        expect_ok <$> call change_commission_function ~sender:auth [val_id; U256.(mon * ~$25 / ~$100)]
      in
      let$ () =
        check int "logs.size += 1 (change_commission)" (seen_events + 1) <$> (List.length <$> get_logs)
      in
      let seen_events = seen_events + 1 in

      (* Change to the same commission. No events emitted *)
      let$ _ =
        expect_ok <$> call change_commission_function ~sender:auth [val_id; U256.(mon * ~$25 / ~$100)]
      in
      let$ () =
        check int "logs.size unchanged (same commission)" seen_events <$> (List.length <$> get_logs)
      in

      (* Epoch change
         1. Epoch changed event *)
      let$ () = skip_to_next_epoch in
      let$ () = check int "logs.size += 1 (epoch change)" (seen_events + 1) <$> (List.length <$> get_logs) in
      let seen_events = seen_events + 1 in

      (* Undelegate, setting validator inactive
         1. Undelegate event
         2. Validator status changed to inactive *)
      let$ _ = expect_ok <$> call undelegate_function ~sender:auth [val_id; U256.(~$50 * mon); U8.one] in
      let$ () =
        check int "logs.size += 2 (undelegate inactive)" (seen_events + 2) <$> (List.length <$> get_logs)
      in
      let seen_events = seen_events + 2 in

      (* Undelegate without changing validator state
         1. Undelegate event *)
      let$ _ = expect_ok <$> call undelegate_function ~sender:auth [val_id; U256.(~$10 * mon); U8.of_int 2] in
      let$ () =
        check int "logs.size += 1 (undelegate no change)" (seen_events + 1) <$> (List.length <$> get_logs)
      in
      let seen_events = seen_events + 1 in

      (* Delegate without changing validator state
         1. Delegate event *)
      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:auth ~value:U256.(~$10 * mon) in
      let$ () =
        check int "logs.size += 1 (delegate no change)" (seen_events + 1) <$> (List.length <$> get_logs)
      in
      let seen_events = seen_events + 1 in

      (* Delegate, setting validator active
         1. Delegate event
         2. Validator status changed *)
      let$ _ = expect_ok <$> delegate_and_credit val_id ~sender:auth ~value:U256.(~$50 * mon) in
      let$ () =
        check int "logs.size += 2 (delegate active)" (seen_events + 2) <$> (List.length <$> get_logs)
      in
      let seen_events = seen_events + 2 in

      (* Claim with no rewards. No events emitted *)
      let$ _ = expect_ok <$> call claim_rewards_function ~sender:auth [val_id] in
      let$ () =
        check int "logs.size unchanged (claim no reward)" seen_events <$> (List.length <$> get_logs)
      in

      (* Reward syscall
         1. Reward originating from the contract *)
      let$ () = expect_ok <$> syscall syscall_reward_function ~value:reward [sign_address] in
      let$ () =
        check int "logs.size += 1 (syscall_reward)" (seen_events + 1) <$> (List.length <$> get_logs)
      in
      let$ () =
        let$ logs = get_logs in
        let last_log = List.nth logs (List.length logs - 1) in
        return
          (check b32 "reward topics[2] = SYSTEM_SENDER"
             (B20.to_bytes32 Chain.Monad.system_sender)
             (List.nth last_log.Log.topics 2) )
      in
      let seen_events = seen_events + 1 in

      (* Claim with nonzero rewards.
         1. Claim event *)
      let$ _ = expect_ok <$> call claim_rewards_function ~sender:auth [val_id] in
      let$ () = check int "logs.size += 1 (claim reward)" (seen_events + 1) <$> (List.length <$> get_logs) in
      let seen_events = seen_events + 1 in

      (* External reward
         1. Reward originating from the sender *)
      let$ () = external_reward_and_credit val_id ~sender:auth ~value:U256.(~$5 * mon) in
      let$ () =
        check int "logs.size += 1 (external_reward)" (seen_events + 1) <$> (List.length <$> get_logs)
      in
      let$ () =
        let$ logs = get_logs in
        let last_log = List.nth logs (List.length logs - 1) in
        return
          (check b32 "external_reward topics[2] = auth" (B20.to_bytes32 auth) (List.nth last_log.Log.topics 2))
      in
      let seen_events = seen_events + 1 in

      (* Compound without changing validator state
         1. Claim event
         2. Delegate event *)
      let$ _ = expect_ok <$> call compound_function ~sender:auth [val_id] in
      let$ () = check int "logs.size += 2 (compound)" (seen_events + 2) <$> (List.length <$> get_logs) in
      let seen_events = seen_events + 2 in

      (* Compound with no rewards. Note that all reward for `auth` were just
         compounded in the last step. No events emitted. *)
      let$ _ = expect_ok <$> call compound_function ~sender:auth [val_id] in
      let$ () =
        check int "logs.size unchanged (compound no reward)" seen_events <$> (List.length <$> get_logs)
      in

      (* Withdraw one of the pending delegations
         1. Withdraw event *)
      let$ () = skip_to_next_epoch in
      let$ () = skip_to_next_epoch in
      let seen_events = seen_events + 2 in
      (* Two epoch changed events *)
      let$ _ = expect_ok <$> call withdraw_function ~sender:auth [val_id; U8.one] in
      let$ () = check int "logs.size += 1 (withdraw)" (seen_events + 1) <$> (List.length <$> get_logs) in
      let seen_events = seen_events + 1 in
      ignore seen_events ;

      (* All logs should come from the staking contract *)
      let$ () =
        let$ logs = get_logs in
        List.iter
          (fun log -> assert' "log.address = STAKING_CA" Address.(equal staking_address log.Log.address))
          logs ;
        return ()
      in

      (* Compute data hash and topics hash *)
      let$ () =
        let$ logs = get_logs in
        let abi_u64 n = B32.to_bytes (List.hd (Type.enc Type.U64.t (U64.of_int n))) in
        let data_blob =
          List.fold_left
            (fun acc log -> acc ^ abi_u64 (Byte_string.Bytes.length log.Log.data) ^ log.Log.data)
            "" logs
        in
        let topics_blob =
          List.fold_left
            (fun acc log ->
              List.fold_left
                (fun acc topic -> acc ^ B32.to_bytes topic)
                (acc ^ abi_u64 (List.length log.Log.topics))
                log.Log.topics )
            "" logs
        in
        let data_hash = Crypto.blake3 data_blob in
        let topics_hash = Crypto.blake3 topics_blob in
        check b32 "data_hash"
          (B32.of_hex_string "0x5CB7B14B95EAEBED9F9C5A0D7EB0F0BF28A209CA329950E5F6325447D6DC08B0")
          data_hash ;
        check b32 "topics_hash"
          (B32.of_hex_string "0x698CB2EE95A576037A3D5EDDA5FFA5ABC8741E6DB69883C899CC93C0EBB55AB6")
          topics_hash ;
        return ()
      in

      return () )

let () =
  let open Alcotest in
  run "Staking"
    [ ( "Miscellaneous tests"
      , [ test_case "simple_add_validator" `Quick test_simple_add_validator
        ; test_case "invoke_fallback" `Quick test_invoke_fallback
        ; test_case "accumulator_is_monotonic_again" `Quick test_accumulator_is_monotonic_again ] )
    ; ( "Commission tests"
      , [ test_case "revert_if_commission_too_high" `Quick test_revert_if_commission_too_high
        ; test_case "non_auth_attempts_to_change_commission" `Quick
            test_non_auth_attempts_to_change_commission
        ; test_case "validator_has_commission" `Quick test_validator_has_commission
        ; test_case "validator_changes_commission" `Quick test_validator_changes_commission ] )
    ; ( "Input validation tests"
      , [ test_case "add_validator_revert_invalid_input_size" `Quick
            test_add_validator_revert_invalid_input_size
        ; test_case "add_validator_revert_bad_signature" `Quick test_add_validator_revert_bad_signature
        ; test_case "add_validator_revert_msg_value_not_signed" `Quick
            test_add_validator_revert_msg_value_not_signed
        ; test_case "add_validator_revert_already_exists" `Quick test_add_validator_revert_already_exists
        ; test_case "add_validator_revert_minimum_stake_not_met" `Quick
            test_add_validator_revert_minimum_stake_not_met
        ; test_case "nonpayable_functions_revert" `Quick test_nonpayable_functions_revert
        ; test_case "auth_address_conflicts_with_linked_list" `Quick
            test_auth_address_conflicts_with_linked_list
        ; test_case "linked_list_removal_state_override" `Quick test_linked_list_removal_state_override ] )
    ; ( "Add validator tests"
      , [ test_case "add_validator_sufficent_balance" `Quick test_add_validator_sufficient_balance
        ; test_case "add_validator_insufficent_balance" `Quick test_add_validator_insufficient_balance
        ; test_case "add_validator_active_stake_fork" `Quick test_add_validator_active_stake_fork ] )
    ; ( "Validator tests"
      , [ test_case "validator_delegate_before_active" `Quick test_validator_delegate_before_active
        ; test_case "validator_multiple_delegations" `Quick test_validator_multiple_delegations
        ; test_case "validator_compound" `Quick test_validator_compound
        ; test_case "validator_undelegate" `Quick test_validator_undelegate
        ; test_case "validator_exit_via_validator" `Quick test_validator_exit_via_validator
        ; test_case "validator_exit_via_delegator" `Quick test_validator_exit_via_delegator
        ; test_case "validator_exit_multiple_delegations" `Quick test_validator_exit_multiple_delegations
        ; test_case "validator_exit_multiple_delegations_full_withdrawal" `Quick
            test_validator_exit_multiple_delegations_full_withdrawal
        ; test_case "validator_exit_claim_rewards" `Quick test_validator_exit_claim_rewards
        ; test_case "validator_exit_compound" `Quick test_validator_exit_compound
        ; test_case "validator_activation_via_delegate" `Quick test_validator_activation_via_delegate
        ; test_case "validator_undelegates_and_redelegates_in_epoch_delay_period" `Quick
            test_validator_undelegates_and_redelegates_in_epoch_delay_period
        ; test_case "validator_joins_in_epoch_delay_period" `Quick test_validator_joins_in_epoch_delay_period
        ; test_case "validator_compound_before_active" `Quick test_validator_compound_before_active
        ; test_case "validator_withdrawal_before_active" `Quick test_validator_withdrawal_before_active
        ; test_case "validator_undelegate_before_delegator_active" `Quick
            test_validator_undelegate_before_delegator_active
        ; test_case "validator_removes_self" `Quick test_validator_removes_self
        ; test_case "two_validators_remove_self" `Quick test_two_validators_remove_self
        ; test_case "validator_constant_validator_set" `Quick test_validator_constant_validator_set
        ; test_case "validator_joining_boundary_rewards" `Quick test_validator_joining_boundary_rewards
        ; test_case "validator_miss_snapshot_miss_activation" `Quick
            test_validator_miss_snapshot_miss_activation
        ; test_case "validator_miss_snapshot_miss_deactivation" `Quick
            test_validator_miss_snapshot_miss_deactivation
        ; test_case "validator_external_rewards_failure_conditions" `Quick
            test_validator_external_rewards_failure_conditions
        ; test_case "validator_external_rewards_uniform_reward_pool" `Quick
            test_validator_external_rewards_uniform_reward_pool ] )
    ; ( "Delegate tests"
      , [ test_case "delegator_none_init" `Quick test_delegator_none_init
        ; test_case "random_delegator_not_allocated_state" `Quick test_random_delegator_not_allocated_state
        ; test_case "delegator_state_cleared_after_withdraw" `Quick
            test_delegator_state_cleared_after_withdraw
        ; test_case "delegate_noop_add_zero_stake" `Quick test_delegate_noop_add_zero_stake
        ; test_case "delegate_noop_subsequent_zero_stake" `Quick test_delegate_noop_subsequent_zero_stake
        ; test_case "delegate_revert_unknown_validator" `Quick test_delegate_revert_unknown_validator
        ; test_case "delegate_init" `Quick test_delegate_init
        ; test_case "delegate_redelegate_before_activation" `Quick test_delegate_redelegate_before_activation
        ; test_case "delegate_redelegate_after_activation" `Quick test_delegate_redelegate_after_activation
        ; test_case "delegate_undelegate_withdraw_redelegate" `Quick
            test_delegate_undelegate_withdraw_redelegate
        ; test_case "delegator_delegates_in_epoch_delay_period" `Quick
            test_delegator_delegates_in_epoch_delay_period
        ; test_case "delegate_redelegation_refcount_before_activation" `Quick
            test_delegate_redelegation_refcount_before_activation
        ; test_case "delegate_redelegation_refcount_after_activation" `Quick
            test_delegate_redelegation_refcount_after_activation
        ; test_case "delegator_epoch_accumulator_same_snapshot" `Quick
            test_delegator_epoch_accumulator_same_snapshot
        ; test_case "delegator_epoch_accumulator_diff_snapshot" `Quick
            test_delegator_epoch_accumulator_diff_snapshot
        ; test_case "delegator_epoch_nz_accumulator_diff_snapshot" `Quick
            test_delegator_epoch_nz_accumulator_diff_snapshot
        ; test_case "validator_exit_delegator_boundary_nz_accumulator" `Quick
            test_validator_exit_delegator_boundary_nz_accumulator
        ; test_case "snapshot_set_same_order_as_consensus_set" `Quick
            test_snapshot_set_same_order_as_consensus_set ] )
    ; ( "Compound / redelegate tests"
      , [ test_case "delegate_inter_compound_rewards" `Quick test_delegate_inter_compound_rewards
        ; test_case "delegate_intra_compound_rewards" `Quick test_delegate_intra_compound_rewards
        ; test_case "delegate_compound_boundary" `Quick test_delegate_compound_boundary
        ; test_case "delegate_compound" `Quick test_delegate_compound
        ; test_case "undelegate_compound" `Quick test_undelegate_compound
        ; test_case "undelegate_compound_partial" `Quick test_undelegate_compound_partial ] )
    ; ( "Undelegate tests"
      , [ test_case "undelegate_boundary_pool" `Quick test_undelegate_boundary_pool
        ; test_case "undelegate_snapshot_boundary_pool" `Quick test_undelegate_snapshot_boundary_pool
        ; test_case "undelegate_revert_insufficient_funds" `Quick test_undelegate_revert_insufficient_funds ]
      )
    ; ( "Withdraw tests"
      , [ test_case "double_withdraw" `Quick test_double_withdraw
        ; test_case "withdraw_reusable_id" `Quick test_withdraw_reusable_id ] )
    ; ( "claim_rewards tests"
      , [ test_case "claim_rewards" `Quick test_claim_rewards
        ; test_case "claim_noop" `Quick test_claim_noop
        ; test_case "claim_rewards_compound" `Quick test_claim_rewards_compound ] )
    ; ( "sys_call_reward tests"
      , [ test_case "reward_unknown_validator" `Quick test_reward_unknown_validator
        ; test_case "reward_sets_block_proposer" `Quick test_reward_sets_block_proposer
        ; test_case "reward_crash_no_snapshot_missing_validator" `Quick
            test_reward_crash_no_snapshot_missing_validator ] )
    ; ( "sys_call_snapshot tests"
      , [ test_case "multiple_snapshot_error" `Quick test_multiple_snapshot_error
        ; test_case "valset_exceeds_n" `Quick test_valset_exceeds_n ] )
    ; ( "sys_call_epoch_change tests"
      , [ test_case "epoch_goes_backwards" `Quick test_epoch_goes_backwards
        ; test_case "contract_bootstrap" `Quick test_contract_bootstrap
        ; test_case "zero_reward_epochs" `Quick test_zero_reward_epochs ] )
    ; ( "Getter tests"
      , [ test_case "get_valset_empty" `Quick test_get_valset_empty
        ; test_case "empty_get_delegators_for_validator_getter" `Quick
            test_empty_get_delegators_for_validator_getter
        ; test_case "empty_get_validators_for_delegator_getter" `Quick
            test_empty_get_validators_for_delegator_getter
        ; test_case "get_delegators_for_validator" `Quick test_get_delegators_for_validator
        ; test_case "get_validators_for_delegator" `Quick test_get_validators_for_delegator
        ; test_case "get_valset_paginated_reads" `Quick test_get_valset_paginated_reads
        ; test_case "get_delegators_for_validator_paginated_reads" `Quick
            test_get_delegators_for_validator_paginated_reads
        ; test_case "get_proposer_val_id_fork" `Quick test_get_proposer_val_id_fork ] )
    ; ( "Solvency tests"
      , [ test_case "validator_insolvent" `Quick test_validator_insolvent
        ; test_case "withdrawal_insolvent" `Quick test_withdrawal_insolvent
        ; test_case "withdrawal_state_override" `Quick test_withdrawal_state_override ] )
    ; ( "Dust tests"
      , [ test_case "dust_hunter" `Quick test_dust_hunter
        ; test_case "delegate_dust" `Quick test_delegate_dust
        ; test_case "undelegate_dust" `Quick test_undelegate_dust ] )
    ; ("Events tests", [test_case "events" `Quick test_events]) ]
