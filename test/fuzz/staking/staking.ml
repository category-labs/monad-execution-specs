(** Model-based fuzzing of the staking precompile, ported from the C++ fuzzer in
    [category/execution/monad/staking/fuzzer].

    [Model] is the shadow ledger of the C++ [StakingContractModel] together with the bookkeeping that the C++
    [StakingContractMachine] keeps for its generators. [Concrete] runs each command against the spec and checks
    the C++ postconditions on the contract state; [Concrete.check] checks the C++ invariants. The C++
    postconditions that only compare the shadow ledger with itself are not ported. [Gen] holds the generators
    and transitions of the C++ machine.

    Each command is a single call. The C++ transitions that make several calls (skipping epochs, adding a
    validator when none exists, taking a snapshot before an epoch change) emit several commands.
    [distributePriorityFees] is not ported because the spec does not implement it. *)

open Monad_lib
open Numeric
open Byte_string
open Chain.Ethereum
open State
open Lens.Infix
module Staking = Monad_lib.Staking
module Val_id = Staking.Val_id
module Epoch = Staking.Epoch
module Variables = Staking.Variables

(* Constants, named as in the C++ machine. *)
let dust_threshold = Staking.dust_threshold
let max_commission = Staking.max_commission
let min_validate_stake = Staking.min_auth_address_stake
let active_valset_size = Staking.active_valset_size
let active_validator_stake = Staking.active_validator_stake
let unit_bias = Staking.unit_bias
let max_stake = unit_bias
let max_delegable_stake = U256.(max_stake - dust_threshold)

let epoch_add (Epoch.Epoch e) n = Epoch.Epoch U64.(e + of_int n)

(* A delegator is identified by a validator id and an address. *)
module Delegator_key = struct
  type t = Val_id.t * Address.t
  let compare (v1, a1) (v2, a2) = match Val_id.compare v1 v2 with 0 -> Address.compare a1 a2 | c -> c
end
module Delegator_map = Map.Make (Delegator_key)
module Delegator_set = Set.Make (Delegator_key)
module Int_set = Set.Make (Int)

module Model = struct
  type cmd =
    | Syscall_on_epoch_change of Epoch.t
    | Syscall_snapshot
    | Syscall_reward of {block_author : Address.t; reward : U256.t}
    | Add_validator of
        { message : Bytes.t
        ; secp_signature : Bytes.t
        ; bls_signature : Bytes.t
        ; signer : Address.t  (** The address of the validator's secp key, which [Syscall_reward] takes. *)
        ; sender : Address.t
        ; value : U256.t }
    | Delegate of {val_id : Val_id.t; sender : Address.t; value : U256.t}
    | Undelegate of {val_id : Val_id.t; amount : U256.t; withdrawal_id : U8.t; sender : Address.t}
    | Compound of {val_id : Val_id.t; sender : Address.t}
    | Withdraw of {val_id : Val_id.t; withdrawal_id : U8.t; sender : Address.t}
    | Claim_rewards of {val_id : Val_id.t; sender : Address.t}
    | Change_commission of {val_id : Val_id.t; commission : U256.t; sender : Address.t}
    | External_reward of {val_id : Val_id.t; sender : Address.t; value : U256.t}
    | Get_delegator of {val_id : Val_id.t; address : Address.t; sender : Address.t}

  type res =
    | Unit
    | Validator_added of Val_id.t
    | Epoch_changed of (Val_id.t * Staking.Consensus_view.t) list
        (** The new consensus valset, with each validator's stake and commission. *)
    | Rewards of U256.t
        (** The exact rewards that [Compound], [Claim_rewards] or [Withdraw] compounded or paid out, computed
            from the state before the call. *)

  type error =
    | Invalid_epoch_change of {epoch : Epoch.t; next_epoch : Epoch.t}
    | Snapshot_in_delay_period
    | Validator_exists of Val_id.t
    | Unknown_block_author of Address.t
    | Inactive_validator of Val_id.t  (** A reward for a validator with no active consensus stake. *)
    | Stake_mismatch of {val_id : Val_id.t; ledger : U256.t; active : U256.t}
        (** The ledger's stake for a validator differs from its active consensus stake. *)

  type validator = {signer : Address.t; auth_address : Address.t}

  type t =
    { epoch : Epoch.t
    ; in_epoch_delay_period : bool
    ; (* The shadow ledger. *)
      error_bound : U256.t  (** An upper bound on reward rounding errors. *)
    ; unit_bias_rewards : U256.t Delegator_map.t
          (** The rewards distributed to each delegator but not yet claimed or compounded, times
              [unit_bias]. *)
    ; active_consensus_stake : U256.t Val_id.Map.t
    ; active_consensus_commission : U256.t Val_id.Map.t
    ; delegator_stake : U256.t Epoch.Map.t Delegator_map.t
          (** Each delegator's stake from each epoch onwards: the stake in an epoch is the entry for the
              latest epoch up to it. *)
    ; withdrawal_stake : U256.t Epoch.Map.t Delegator_map.t
          (** Each delegator's undelegated stake that still earns rewards in an epoch. *)
    ; historic_delegators : Address.Set.t Val_id.Map.t
    ; withdrawal_ids : Int_set.t Delegator_map.t  (** The ids of each delegator's withdrawal requests. *)
    ; (* Bookkeeping for the generator. *)
      addresses : Address.Set.t
    ; validators : validator Val_id.Map.t
    ; signers : Val_id.t Address.Map.t
    ; delegable_val_ids : Val_id.Set.t  (** Validators whose stake is at most [max_delegable_stake]. *)
    ; delegators : Delegator_set.t }

  let init =
    { epoch = Epoch.zero
    ; in_epoch_delay_period = false
    ; error_bound = U256.zero
    ; unit_bias_rewards = Delegator_map.empty
    ; active_consensus_stake = Val_id.Map.empty
    ; active_consensus_commission = Val_id.Map.empty
    ; delegator_stake = Delegator_map.empty
    ; withdrawal_stake = Delegator_map.empty
    ; historic_delegators = Val_id.Map.empty
    ; withdrawal_ids = Delegator_map.empty
    ; addresses = Address.Set.empty
    ; validators = Val_id.Map.empty
    ; signers = Address.Map.empty
    ; delegable_val_ids = Val_id.Set.empty
    ; delegators = Delegator_set.empty }

  let auth_address_of_message (message : Bytes.t) = Address.sub message 81

  let u256_or_zero = function Some x -> x | None -> U256.zero

  let unit_bias_rewards t key = u256_or_zero (Delegator_map.find_opt key t.unit_bias_rewards)
  let active_consensus_stake t v = u256_or_zero (Val_id.Map.find_opt v t.active_consensus_stake)
  let active_consensus_commission t v = u256_or_zero (Val_id.Map.find_opt v t.active_consensus_commission)
  let historic_delegators t v =
    Option.value ~default:Address.Set.empty (Val_id.Map.find_opt v t.historic_delegators)
  let withdrawal_ids t key = Option.value ~default:Int_set.empty (Delegator_map.find_opt key t.withdrawal_ids)

  let delegator_stake t key epoch =
    match Delegator_map.find_opt key t.delegator_stake with
    | None -> U256.zero
    | Some stakes -> (
      match Epoch.Map.find_last_opt (fun e -> Epoch.(e <= epoch)) stakes with
      | Some (_, stake) -> stake
      | None -> U256.zero )

  let withdrawal_stake t key epoch =
    match Delegator_map.find_opt key t.withdrawal_stake with
    | None -> U256.zero
    | Some stakes -> u256_or_zero (Epoch.Map.find_opt epoch stakes)

  (* A validator's stake once all pending stake changes have activated. *)
  let validator_stake t v =
    let final_stake a =
      match Delegator_map.find_opt (v, a) t.delegator_stake with
      | None -> U256.zero
      | Some stakes -> ( match Epoch.Map.max_binding_opt stakes with Some (_, s) -> s | None -> U256.zero )
    in
    Address.Set.fold (fun a sum -> U256.(sum + final_stake a)) (historic_delegators t v) U256.zero

  let activation_epoch t = epoch_add t.epoch (if t.in_epoch_delay_period then 2 else 1)

  (* As in the C++, arithmetic wraps around, so a decrease is passed as its two's complement. *)
  let neg x = U256.(zero - x)

  let add_delegator_stake key epoch delta t =
    let stakes = Option.value ~default:Epoch.Map.empty (Delegator_map.find_opt key t.delegator_stake) in
    let previous = delegator_stake t key epoch in
    let stakes = Epoch.Map.mapi (fun e s -> if Epoch.(e > epoch) then U256.(s + delta) else s) stakes in
    let stakes = Epoch.Map.add epoch U256.(previous + delta) stakes in
    {t with delegator_stake = Delegator_map.add key stakes t.delegator_stake}

  (* Add [delta] to the withdrawal stake from the current epoch up to [end_epoch], exclusive. *)
  let add_withdrawal_stake key ~end_epoch delta t =
    let rec loop e stakes =
      if Epoch.(e >= end_epoch) then stakes
      else
        let stake = u256_or_zero (Epoch.Map.find_opt e stakes) in
        loop (epoch_add e 1) (Epoch.Map.add e U256.(stake + delta) stakes)
    in
    let stakes = Option.value ~default:Epoch.Map.empty (Delegator_map.find_opt key t.withdrawal_stake) in
    {t with withdrawal_stake = Delegator_map.add key (loop t.epoch stakes) t.withdrawal_stake}

  let add_unit_bias_rewards key delta t =
    { t with
      unit_bias_rewards = Delegator_map.add key U256.(unit_bias_rewards t key + delta) t.unit_bias_rewards }

  let add_error_bound n t = {t with error_bound = U256.(t.error_bound + of_int n)}

  let add_historic_delegator v a t =
    { t with
      historic_delegators =
        Val_id.Map.add v (Address.Set.add a (historic_delegators t v)) t.historic_delegators }

  let update_withdrawal_ids key f t =
    {t with withdrawal_ids = Delegator_map.add key (f (withdrawal_ids t key)) t.withdrawal_ids}

  let update_delegable_val_ids f t = {t with delegable_val_ids = f t.delegable_val_ids}

  (* Distribute [reward] to a validator's delegators in proportion to the stake that earns rewards this
     epoch. *)
  let distribute_reward v reward t =
    let active_stake = active_consensus_stake t v in
    if U256.(active_stake = zero) then Error (Inactive_validator v)
    else
      let reward_per_token = U256.(reward * unit_bias / active_stake) in
      let t, total =
        Address.Set.fold
          (fun a (t, total) ->
            let stake = U256.(delegator_stake t (v, a) t.epoch + withdrawal_stake t (v, a) t.epoch) in
            (add_unit_bias_rewards (v, a) U256.(stake * reward_per_token) t, U256.(total + stake)) )
          (historic_delegators t v) (t, U256.zero)
      in
      if U256.(total <> active_stake) then
        Error (Stake_mismatch {val_id = v; ledger = total; active = active_stake})
      else Ok t

  let addresses_of = function
    | Syscall_on_epoch_change _ | Syscall_snapshot | Syscall_reward _ -> []
    | Add_validator {message; sender; _} -> [sender; auth_address_of_message message]
    | Delegate {sender; _}
     |Undelegate {sender; _}
     |Compound {sender; _}
     |Withdraw {sender; _}
     |Claim_rewards {sender; _}
     |Change_commission {sender; _}
     |External_reward {sender; _} ->
        [sender]
    | Get_delegator {address; sender; _} -> [address; sender]

  let ( let* ) = Result.bind

  let step t cmd res =
    let t = {t with addresses = List.fold_left (Fun.flip Address.Set.add) t.addresses (addresses_of cmd)} in
    match (cmd, res) with
    | Syscall_on_epoch_change next_epoch, Epoch_changed consensus ->
        if Epoch.( <= ) next_epoch t.epoch then Error (Invalid_epoch_change {epoch = t.epoch; next_epoch})
        else
          let active_consensus_stake, active_consensus_commission =
            List.fold_left
              (fun (stakes, commissions) (v, (view : Staking.Consensus_view.t)) ->
                (Val_id.Map.add v view.stake stakes, Val_id.Map.add v view.commission commissions) )
              (Val_id.Map.empty, Val_id.Map.empty) consensus
          in
          Ok
            { t with
              epoch = next_epoch
            ; in_epoch_delay_period = false
            ; active_consensus_stake
            ; active_consensus_commission }
    | Syscall_snapshot, Unit ->
        if t.in_epoch_delay_period then Error Snapshot_in_delay_period
        else Ok {t with in_epoch_delay_period = true}
    | Syscall_reward {block_author; reward}, Unit -> (
      match Address.Map.find_opt block_author t.signers with
      | None -> Error (Unknown_block_author block_author)
      | Some v ->
          let {auth_address; _} = Val_id.Map.find v t.validators in
          let commission = U256.(reward * active_consensus_commission t v / Staking.mon) in
          let t = add_unit_bias_rewards (v, auth_address) U256.(commission * unit_bias) t in
          let* t = distribute_reward v U256.(reward - commission) t in
          Ok (add_error_bound 1 t) )
    | Add_validator {message; signer; value; _}, Validator_added v ->
        if Val_id.Map.mem v t.validators then Error (Validator_exists v)
        else
          let auth_address = auth_address_of_message message in
          let t = add_delegator_stake (v, auth_address) (activation_epoch t) value t in
          let t = add_historic_delegator v auth_address t in
          let t =
            if U256.(value <= max_delegable_stake) then update_delegable_val_ids (Val_id.Set.add v) t else t
          in
          Ok
            { t with
              validators = Val_id.Map.add v {signer; auth_address} t.validators
            ; signers = Address.Map.add signer v t.signers
            ; delegators = Delegator_set.add (v, auth_address) t.delegators }
    | Delegate {val_id = v; sender; value}, Unit ->
        let t = add_delegator_stake (v, sender) (activation_epoch t) value t in
        let t = add_error_bound 3 (add_historic_delegator v sender t) in
        if U256.(value = zero) then Ok t
        else
          let t =
            if U256.(validator_stake t v > max_delegable_stake) then
              update_delegable_val_ids (Val_id.Set.remove v) t
            else t
          in
          Ok {t with delegators = Delegator_set.add (v, sender) t.delegators}
    | Undelegate {val_id = v; amount; withdrawal_id; sender}, Unit ->
        let key = (v, sender) in
        let before = delegator_stake t key t.epoch in
        let effective = if U256.(before - amount >= dust_threshold) then amount else before in
        let end_epoch = activation_epoch t in
        let t = add_delegator_stake key t.epoch (neg effective) t in
        let t = add_withdrawal_stake key ~end_epoch effective t in
        let t =
          if U256.(effective > zero) then update_withdrawal_ids key (Int_set.add (U8.to_int withdrawal_id)) t
          else t
        in
        let t = add_error_bound 3 t in
        if U256.(amount = zero) then Ok t
        else
          let t =
            if U256.(delegator_stake t key t.epoch = zero) then
              {t with delegators = Delegator_set.remove key t.delegators}
            else t
          in
          if U256.(validator_stake t v <= max_delegable_stake) then
            Ok (update_delegable_val_ids (Val_id.Set.add v) t)
          else Ok t
    | Compound {val_id = v; sender}, Rewards rewards ->
        let key = (v, sender) in
        let t = add_unit_bias_rewards key (neg U256.(rewards * unit_bias)) t in
        let t = add_error_bound 3 (add_delegator_stake key (activation_epoch t) rewards t) in
        if U256.(rewards <> zero) && U256.(validator_stake t v > max_delegable_stake) then
          Ok (update_delegable_val_ids (Val_id.Set.remove v) t)
        else Ok t
    | Withdraw {val_id = v; withdrawal_id; sender}, Rewards reward ->
        let key = (v, sender) in
        let t = add_error_bound 1 (add_unit_bias_rewards key (neg U256.(reward * unit_bias)) t) in
        Ok (update_withdrawal_ids key (Int_set.remove (U8.to_int withdrawal_id)) t)
    | Claim_rewards {val_id = v; sender}, Rewards reward ->
        Ok (add_error_bound 3 (add_unit_bias_rewards (v, sender) (neg U256.(reward * unit_bias)) t))
    | Change_commission _, Unit -> Ok t
    | External_reward {val_id = v; value; _}, Unit ->
        let* t = distribute_reward v value t in
        Ok (add_error_bound 1 t)
    | Get_delegator _, Unit -> Ok (add_error_bound 3 t)
    | _ -> invalid_arg "Staking.Model.step: the result does not match the command"
end

(**** Helpers copied from test/unit/staking.ml. ****)

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

module Instantiation = Test_utils.Utils.Make (Test_utils.Utils.Monad_nine)

(* Call a contract function via a message pass, performing ABI encoding and decoding. On error, the state is
   rolled back. *)
let call
    (type i o)
    (fn : (i, o) Staking.Function.impl)
    ~sender
    ?(endpoint = Staking.precompile)
    ?(value = U256.zero)
    (input : i)
    (state : TransactionState.t) : (o, Staking.Error.t) result * TransactionState.t =
  let msg =
    Staking.Abi.Signature.input_to_message ~prepend_selector:true ~value ~sender
      ~recipient:Staking.staking_address ~gas:100_000_000L
      ~memory_capacity:(Uint.to_uint32 Instantiation.Evm.Vm.Memory.max_memory_usage)
      fn.signature input
  in
  let result, state' = endpoint msg state in
  match result.status_code with
  | Success ->
      (* Output decoding should not fail under any circumstances. *)
      let outputs = Result.get_ok Staking.Type.(dec_bytes fn.signature.output result.output_data) in
      (Ok outputs, state')
  | _ -> (Error (error_of_output_string result.output_data), state)

let syscall (fn : ('i, 'o) Staking.Function.impl) ?(value = U256.zero) (input : 'i) state =
  call fn ~endpoint:Staking.staking_syscalls ~sender:Chain.Monad.system_sender ~value input state

(* The inputs to [addValidator] for a validator whose keys are derived from [secret], and the address of its
   secp key. *)
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
  ((message, secp_sig, bls_sig), Crypto.Secp.address_of_pubkey secp_pk)

module Concrete = struct
  module Model = Model

  type t = TransactionState.t

  type error =
    | Call_failed of Staking.Error.t  (** A call that the fuzzer expects to succeed reverted. *)
    | Violated of string  (** A postcondition or invariant does not hold. *)

  (* As in the C++, the contract starts at epoch 0. A nonce of 1 keeps the staking account from being deleted
     as empty. *)
  let init = TransactionState.empty.^(Staking.staking_account |-- Account.nonce) <- U64.one

  let ( let* ) = Result.bind

  let rec iter_r f = function
    | [] -> Ok ()
    | x :: xs ->
        let* () = f x in
        iter_r f xs

  let fold_r f init l = List.fold_left (fun acc x -> Result.bind acc (fun acc -> f acc x)) (Ok init) l

  let ensure what cond = if cond then Ok () else Error (Violated what)

  (* Add the validator and address an invariant failed for to its description. *)
  let at ~val_id:(Val_id.Val_id v) ?address result =
    match result with
    | Error (Violated what) ->
        let address = match address with Some a -> ", address 0x" ^ Address.to_hex_string a | None -> "" in
        Error (Violated (Printf.sprintf "%s (validator %s%s)" what (U64.to_string v) address))
    | _ -> result

  (* Reading the contract state. *)

  let get loc (st : t) = st.^(Staking.Storage.Loc.lens loc)
  let read_array arr (st : t) = fst (Staking.Storage.Array.read_to_list arr st)
  let balance address (st : t) = st.^(TransactionState.account address |-- Account.balance)
  let staking_balance = balance Staking.staking_address

  let epoch = get Variables.epoch
  let in_epoch_delay_period = get Variables.in_epoch_delay_period
  let val_execution v = get (Variables.val_execution v)
  let delegator v a = get (Variables.delegator (v, a))
  let accumulator e v = get (Variables.accumulated_reward_per_token (e, v))
  let withdrawal_request v a i = get (Variables.withdrawal_request (v, a, U8.of_int i))

  (* All validator ids up to two past the last one, as in the C++. *)
  let val_ids st =
    let (Val_id.Val_id last) = get Variables.last_val_id st in
    List.init (U64.to_int last + 3) Val_id.of_int

  let activation_epoch st = epoch_add (epoch st) (if in_epoch_delay_period st then 2 else 1)

  let this_epoch_view v st =
    get ((if in_epoch_delay_period st then Variables.snapshot_view else Variables.consensus_view) v) st

  let in_valset arr v st = List.exists (Val_id.equal v) (read_array arr st)

  (* The stake of a validator's auth delegator, including pending changes. *)
  let auth_stake v st =
    Staking.Delegator.next_epoch_stake (delegator v (val_execution v st).address_flags.auth_address st)

  (* A delegator's stake in [epoch]. *)
  let active_stake ~epoch (del : Staking.Delegator.t) =
    let stake =
      if Epoch.(del.epochs.delta_epoch <= epoch) then U256.(del.stake + del.delta_stake) else del.stake
    in
    if Epoch.(del.epochs.next_delta_epoch <= epoch) then U256.(stake + del.next_delta_stake) else stake

  let delegators_of v st =
    match fst (Staking.Delegators_for_validator.traverse v Address.zero max_int st) with
    | Ok (_, _, delegators) -> delegators
    | Error _ -> assert false

  let validators_of a st =
    match fst (Staking.Validators_for_delegator.traverse a Val_id.zero max_int st) with
    | Ok (_, _, validators) -> validators
    | Error _ -> assert false

  (* Rewards, computed from the contract state as in the C++ model. *)

  let calculate_rewards stake ~current ~last = U256.(stake * (current - last) / unit_bias)

  let unaccumulated_rewards v a st =
    let del = delegator v a st in
    let epoch = epoch st in
    let {Staking.Epochs.delta_epoch; next_delta_epoch} = del.epochs in
    let has_activated e = Epoch.(e <> zero) && Epoch.(e <= epoch) in
    let p1 = del.rewards_per_token in
    let q1 = if has_activated delta_epoch then (accumulator delta_epoch v st).value else p1 in
    let* () = ensure "the accumulator at delta_epoch is at least the delegator's" U256.(q1 >= p1) in
    let r1 = calculate_rewards del.stake ~current:q1 ~last:p1 in
    let t2 = if Epoch.(delta_epoch <= epoch) then U256.(del.stake + del.delta_stake) else del.stake in
    let q2 = if has_activated next_delta_epoch then (accumulator next_delta_epoch v st).value else q1 in
    let* () =
      ensure "the accumulator at next_delta_epoch is at least the one at delta_epoch" U256.(q2 >= q1)
    in
    let r2 = calculate_rewards t2 ~current:q2 ~last:q1 in
    let t3 = if Epoch.(next_delta_epoch <= epoch) then U256.(t2 + del.next_delta_stake) else t2 in
    let q3 = (val_execution v st).rewards_per_token in
    let* () =
      ensure "the validator's rewards per token are at least the delegator's accumulator" U256.(q3 >= q2)
    in
    Ok U256.(r1 + r2 + calculate_rewards t3 ~current:q3 ~last:q2)

  (* A delegator's accumulated and unaccumulated rewards. *)
  let delegator_rewards v a st =
    let* unaccumulated = unaccumulated_rewards v a st in
    Ok U256.((delegator v a st).rewards + unaccumulated)

  let withdrawal_reward v a i st =
    match withdrawal_request v a i st with
    | None -> Ok U256.zero
    | Some req when Epoch.(req.epoch = zero) -> Ok U256.zero
    | Some req ->
        let current =
          if Epoch.(epoch st < req.epoch) then (val_execution v st).rewards_per_token
          else (accumulator req.epoch v st).value
        in
        let* () =
          ensure "the accumulator of a withdrawal request is at least its own" U256.(current >= req.acc)
        in
        Ok (calculate_rewards req.amount ~current ~last:req.acc)

  let pending_rewards (m : Model.t) (v, a) st =
    let* withdrawals =
      fold_r
        (fun sum i ->
          let* reward = withdrawal_reward v a i st in
          Ok U256.(sum + reward) )
        U256.zero
        (Int_set.elements (Model.withdrawal_ids m (v, a)))
    in
    let* unaccumulated = unaccumulated_rewards v a st in
    Ok U256.(withdrawals + unaccumulated)

  (* Calls. *)

  let must_succeed (result, st) =
    match result with Ok output -> Ok (output, st) | Error err -> Error (Call_failed err)

  (* Call the precompile, first crediting [value] to the staking contract as a value transfer would. *)
  let precompile fn ~sender ?(value = U256.zero) input st =
    let st =
      if U256.(value = zero) then st
      else st.^(Staking.staking_account |-- Account.balance) <- U256.(staking_balance st + value)
    in
    must_succeed (call fn ~sender ~value input st)

  let precompile_true fn ~sender ?value input st =
    let* ok, st = precompile fn ~sender ?value input st in
    let* () = ensure "the call returns true" ok in
    Ok st

  let active_validator_in_valset v st =
    let ve = val_execution v st in
    ensure "a validator with active stake and enough auth stake is in valset_execution"
      ( (not (U256.(ve.stake >= active_validator_stake) && U256.(auth_stake v st >= min_validate_stake)))
      || in_valset Variables.valset_execution v st )

  let exec (cmd : Model.cmd) (st : t) : (Model.res * t, error) result =
    match cmd with
    | Syscall_on_epoch_change next_epoch ->
        let* (), st' = must_succeed (syscall Staking.syscall_on_epoch_change_function next_epoch st) in
        let* () = ensure "an epoch change ends the epoch delay period" (not (in_epoch_delay_period st')) in
        let* () = ensure "an epoch change sets the epoch" Epoch.(epoch st' = next_epoch) in
        let consensus =
          List.map
            (fun v -> (v, get (Variables.consensus_view v) st'))
            (read_array Variables.valset_consensus st')
        in
        Ok (Model.Epoch_changed consensus, st')
    | Syscall_snapshot ->
        let* (), st' = must_succeed (syscall Staking.syscall_snapshot_function () st) in
        let* () = ensure "a snapshot starts the epoch delay period" (in_epoch_delay_period st') in
        let* () =
          iter_r
            (fun v ->
              at ~val_id:v
                (ensure "validators in valset_execution have active stake"
                   U256.((val_execution v st').stake >= active_validator_stake) ) )
            (read_array Variables.valset_execution st')
        in
        let consensus = Val_id.Set.of_list (read_array Variables.valset_consensus st') in
        let vals =
          List.map
            (fun v -> (v, (val_execution v st').stake, Val_id.Set.mem v consensus, auth_stake v st'))
            (val_ids st')
        in
        let* () =
          iter_r
            (fun (_, v_stake, v_in_consensus, _) ->
              if not v_in_consensus then Ok ()
              else
                iter_r
                  (fun (u, u_stake, u_in_consensus, u_auth_stake) ->
                    at ~val_id:u
                      (ensure "valset_consensus holds the validators with the most stake"
                         ( u_in_consensus
                         || U256.(v_stake >= u_stake)
                         || U256.(u_auth_stake < min_validate_stake) ) ) )
                  vals )
            vals
        in
        Ok (Model.Unit, st')
    | Syscall_reward {block_author; reward} ->
        let* (), st' = must_succeed (syscall Staking.syscall_reward_function ~value:reward block_author st) in
        let* v =
          Option.to_result ~none:(Violated "syscall_reward succeeds for validators only")
            (get (Variables.val_id block_author) st)
        in
        let commission = U256.(reward * (this_epoch_view v st).commission / Staking.mon) in
        let* () =
          ensure "unclaimed rewards grow by the reward minus the commission"
            U256.(
              (val_execution v st').unclaimed_rewards
              = (val_execution v st).unclaimed_rewards + reward - commission )
        in
        let* () =
          ensure "the rewarded validator is the proposer" Val_id.(get Variables.proposer_val_id st' = v)
        in
        Ok (Model.Unit, st')
    | Add_validator {message; secp_signature; bls_signature; sender; value; signer = _} ->
        let* v, st' =
          precompile Staking.add_validator_function ~sender ~value (message, secp_signature, bls_signature) st
        in
        let* () =
          ensure "the staking balance grows by the stake"
            U256.(staking_balance st' - staking_balance st = value)
        in
        let* () =
          let (Val_id.Val_id before) = get Variables.last_val_id st in
          let (Val_id.Val_id after) = get Variables.last_val_id st' in
          ensure "last_val_id is incremented" U64.(after = before + one)
        in
        let ve = val_execution v st' in
        let* () =
          ensure "the validator has the signed keys"
            Staking.Keys.(equal ve.keys {secp_pubkey = B33.sub message 0; bls_pubkey = B48.sub message 33})
        in
        let* () =
          ensure "the validator has the signed commission"
            U256.(ve.commission = of_repr (Repr.sub message 133))
        in
        let* () = ensure "the validator's stake is the sent value" U256.(ve.stake = value) in
        let* () =
          ensure "a validator in valset_execution has active stake"
            ((not (in_valset Variables.valset_execution v st')) || U256.(value >= active_validator_stake))
        in
        let* () =
          ensure "the validator is in its auth address's delegations"
            (List.exists (Val_id.equal v) (validators_of (Model.auth_address_of_message message) st'))
        in
        Ok (Model.Validator_added v, st')
    | Delegate {val_id = v; sender; value} ->
        let* st' = precompile_true Staking.delegate_function ~sender ~value v st in
        let* () =
          if U256.(value = zero) then Ok ()
          else
            let* () =
              ensure "the staking balance grows by the delegated stake"
                U256.(staking_balance st' - staking_balance st = value)
            in
            let* () =
              ensure "the validator's stake grows by the delegated stake"
                U256.((val_execution v st').stake - (val_execution v st).stake = value)
            in
            let* () = active_validator_in_valset v st' in
            ensure "the validator is in the delegator's delegations"
              (List.exists (Val_id.equal v) (validators_of sender st'))
        in
        Ok (Model.Unit, st')
    | Undelegate {val_id = v; amount; withdrawal_id; sender} ->
        let stake = active_stake ~epoch:(epoch st) (delegator v sender st) in
        let effective = if U256.(stake - amount < dust_threshold) then stake else amount in
        let* st' = precompile_true Staking.undelegate_function ~sender (v, amount, withdrawal_id) st in
        let* () =
          if U256.(amount = zero) then Ok ()
          else
            let* req =
              Option.to_result ~none:(Violated "undelegate creates a withdrawal request")
                (get (Variables.withdrawal_request (v, sender, withdrawal_id)) st')
            in
            let* () =
              ensure "the withdrawal request holds the undelegated stake" U256.(req.amount = effective)
            in
            let* () =
              ensure "the withdrawal request is for the next stake change"
                Epoch.(req.epoch = activation_epoch st)
            in
            ensure "a delegator with no stake is not in the delegations"
              (U256.(stake <> zero) || not (List.exists (Val_id.equal v) (validators_of sender st')))
        in
        Ok (Model.Unit, st')
    | Compound {val_id = v; sender} ->
        let* rewards = delegator_rewards v sender st in
        let* st' = precompile_true Staking.compound_function ~sender v st in
        let* () =
          if U256.(rewards = zero) then Ok ()
          else
            let* () =
              ensure "the validator's stake grows by the compounded rewards"
                U256.((val_execution v st').stake - (val_execution v st).stake = rewards)
            in
            active_validator_in_valset v st'
        in
        Ok (Model.Rewards rewards, st')
    | Withdraw {val_id = v; withdrawal_id; sender} ->
        let i = U8.to_int withdrawal_id in
        let* reward = withdrawal_reward v sender i st in
        let amount =
          match withdrawal_request v sender i st with
          | Some req -> U256.(req.amount + reward)
          | None -> reward
        in
        let* st' = precompile_true Staking.withdraw_function ~sender (v, withdrawal_id) st in
        let* () =
          ensure "the staking balance shrinks by the withdrawal"
            U256.(staking_balance st - staking_balance st' = amount)
        in
        let* () =
          ensure "the sender's balance grows by the withdrawal"
            U256.(balance sender st' - balance sender st = amount)
        in
        let* () =
          ensure "unclaimed rewards shrink by the withdrawal's rewards"
            U256.((val_execution v st).unclaimed_rewards - (val_execution v st').unclaimed_rewards = reward)
        in
        Ok (Model.Rewards reward, st')
    | Claim_rewards {val_id = v; sender} ->
        let* reward = delegator_rewards v sender st in
        let* st' = precompile_true Staking.claim_rewards_function ~sender v st in
        let* () =
          ensure "the staking balance shrinks by the rewards"
            U256.(staking_balance st - staking_balance st' = reward)
        in
        let* () =
          ensure "the sender's balance grows by the rewards"
            U256.(balance sender st' - balance sender st = reward)
        in
        Ok (Model.Rewards reward, st')
    | Change_commission {val_id = v; commission; sender} ->
        let* st' = precompile_true Staking.change_commission_function ~sender (v, commission) st in
        let* () =
          ensure "the validator has the new commission" U256.((val_execution v st').commission = commission)
        in
        Ok (Model.Unit, st')
    | External_reward {val_id = v; sender; value} ->
        let* st' = precompile_true Staking.external_reward_function ~sender ~value v st in
        let* () =
          ensure "unclaimed rewards grow by the reward"
            U256.((val_execution v st').unclaimed_rewards = (val_execution v st).unclaimed_rewards + value)
        in
        Ok (Model.Unit, st')
    | Get_delegator {val_id = v; address; sender} ->
        let* unaccumulated = unaccumulated_rewards v address st in
        let* _, st' = precompile Staking.get_delegator_function ~sender (v, address) st in
        let* () =
          ensure "getDelegator accumulates the delegator's rewards"
            U256.((delegator v address st').rewards = (delegator v address st).rewards + unaccumulated)
        in
        let* unaccumulated' = unaccumulated_rewards v address st' in
        let* () = ensure "getDelegator leaves no rewards unaccumulated" U256.(unaccumulated' = zero) in
        Ok (Model.Unit, st')

  (* Invariants. *)

  let valset_invariants (m : Model.t) val_ids st =
    let execution = read_array Variables.valset_execution st in
    let consensus = read_array Variables.valset_consensus st in
    let snapshot = read_array Variables.valset_snapshot st in
    let execution_set = Val_id.Set.of_list execution in
    let consensus_set = Val_id.Set.of_list consensus in
    let snapshot_set = Val_id.Set.of_list snapshot in
    let* () =
      ensure "valset_execution has no duplicates" (Val_id.Set.cardinal execution_set = List.length execution)
    in
    let* () =
      iter_r
        (fun v ->
          at ~val_id:v
            (ensure "validators in valset_execution have an auth address"
               Address.((val_execution v st).address_flags.auth_address <> zero) ) )
        execution
    in
    let* () =
      ensure "valset_consensus has no duplicates" (Val_id.Set.cardinal consensus_set = List.length consensus)
    in
    let* () = ensure "valset_consensus is not too large" (List.length consensus <= active_valset_size) in
    let* () =
      ensure "valset_snapshot has no duplicates" (Val_id.Set.cardinal snapshot_set = List.length snapshot)
    in
    let* () = ensure "valset_snapshot is not too large" (List.length snapshot <= active_valset_size) in
    let* () =
      ensure "valset_consensus is a subset of valset_execution"
        (Val_id.Set.subset consensus_set execution_set)
    in
    iter_r
      (fun v ->
        at ~val_id:v
          (let consensus_view = get (Variables.consensus_view v) st in
           let snapshot_view = get (Variables.snapshot_view v) st in
           let* () =
             ensure "validators are in valset_consensus iff their consensus stake is active"
               (Bool.equal (Val_id.Set.mem v consensus_set)
                  U256.(consensus_view.stake >= active_validator_stake) )
           in
           let* () =
             ensure "validators are in valset_snapshot iff their snapshot stake is active"
               (Bool.equal (Val_id.Set.mem v snapshot_set)
                  U256.(snapshot_view.stake >= active_validator_stake) )
           in
           let* () =
             ensure "the consensus commission is not too high"
               U256.(consensus_view.commission <= max_commission)
           in
           let* () =
             ensure "the snapshot commission is not too high" U256.(snapshot_view.commission <= max_commission)
           in
           let* () =
             let bucket = get (Variables.val_bitset_bucket v) st in
             ensure "the valset bitset matches valset_execution"
               (Bool.equal
                  U256.(logand bucket (Staking.val_id_to_mask v) <> zero)
                  (Val_id.Set.mem v execution_set) )
           in
           let* () =
             let ve = val_execution v st in
             let auth_stake = (delegator v ve.address_flags.auth_address st).stake in
             ensure "validators with active stake and enough auth stake are in valset_execution"
               ( U256.(ve.stake < active_validator_stake)
               || U256.(auth_stake < min_validate_stake)
               || Val_id.Set.mem v execution_set )
           in
           let view = if in_epoch_delay_period st then snapshot_view else consensus_view in
           let* () =
             ensure "the model's active consensus stake matches the contract"
               U256.(Model.active_consensus_stake m v = view.stake)
           in
           ensure "the model's active consensus commission matches the contract"
             U256.(Model.active_consensus_commission m v = view.commission) ) )
      val_ids

  let val_execution_invariants val_ids st =
    let (Val_id.Val_id last) = get Variables.last_val_id st in
    let exists (Val_id.Val_id v) = U64.(v <> zero && v <= last) in
    let auth_address v = (val_execution v st).address_flags.auth_address in
    iter_r
      (fun v ->
        at ~val_id:v
          (let ve = val_execution v st in
           let has_flag flag = U64.(logand ve.address_flags.flags flag <> zero) in
           let* () =
             ensure "validators up to last_val_id have an auth address"
               ((not (exists v)) || Address.(auth_address v <> zero))
           in
           let* () =
             ensure "validator 0 has no auth address" (exists v || Address.(auth_address Val_id.zero = zero))
           in
           let* () =
             let (Val_id.Val_id i) = v in
             ensure "validators are created in order"
               ( Val_id.(v = zero)
               || Address.(auth_address (Val_id.Val_id U64.(i + one)) = zero)
               || Address.(auth_address v <> zero) )
           in
           let* () =
             ensure "a validator is withdrawn iff its auth stake is below the minimum"
               ( (not (exists v))
               || Bool.equal
                    U256.(auth_stake v st >= min_validate_stake)
                    (not (has_flag Staking.Address_flags.withdrawn)) )
           in
           let* () = ensure "the commission is not too high" U256.(ve.commission <= max_commission) in
           let* () = ensure "only known flags are set" U64.(ve.address_flags.flags < of_int 4) in
           ensure "a validator's stake is too low iff it is below the active stake"
             ( (not (exists v))
             || Bool.equal
                  U256.(ve.stake >= active_validator_stake)
                  (not (has_flag Staking.Address_flags.stake_too_low)) ) ) )
      val_ids

  let delegator_invariants (m : Model.t) val_ids addresses st =
    let epoch = epoch st in
    let* () =
      iter_r
        (fun v ->
          iter_r
            (fun a ->
              at ~val_id:v ~address:a
                (let del = delegator v a st in
                 let {Staking.Epochs.delta_epoch; next_delta_epoch} = del.epochs in
                 let zero_or_above_dust x = U256.(x = zero || x >= dust_threshold) in
                 let* () =
                   ensure "next_delta_stake is zero or above dust" (zero_or_above_dust del.next_delta_stake)
                 in
                 let* () = ensure "delta_stake is zero or above dust" (zero_or_above_dust del.delta_stake) in
                 let* () = ensure "stake is zero or above dust" (zero_or_above_dust del.stake) in
                 let* () =
                   ensure "next_delta_stake is zero iff next_delta_epoch is zero"
                     (Bool.equal U256.(del.next_delta_stake = zero) Epoch.(next_delta_epoch = zero))
                 in
                 let* () =
                   ensure "delta_stake is zero iff delta_epoch is zero"
                     (Bool.equal U256.(del.delta_stake = zero) Epoch.(delta_epoch = zero))
                 in
                 let* () =
                   ensure "next_delta_epoch follows delta_epoch"
                     ( Epoch.(delta_epoch = zero)
                     || Epoch.(next_delta_epoch = zero)
                     || Epoch.(next_delta_epoch = epoch_add delta_epoch 1) )
                 in
                 let* () =
                   ensure "delta_epoch is at most epoch + 1" Epoch.(delta_epoch <= epoch_add epoch 1)
                 in
                 let* () =
                   ensure "next_delta_epoch is at most epoch + 2" Epoch.(next_delta_epoch <= epoch_add epoch 2)
                 in
                 let* requests =
                   fold_r
                     (fun requests i ->
                       let* (req : Staking.Withdrawal_request.t) =
                         Option.to_result ~none:(Violated "the model's withdrawal requests exist")
                           (withdrawal_request v a i st)
                       in
                       let* () = ensure "withdrawal requests have an amount" U256.(req.amount > zero) in
                       let* () = ensure "withdrawal requests have an epoch" Epoch.(req.epoch > zero) in
                       Ok (req :: requests) )
                     []
                     (Int_set.elements (Model.withdrawal_ids m (v, a)))
                 in
                 let* () =
                   let error_bound = U256.(m.error_bound + of_int 3 + of_int 256) in
                   let unit_bias_rewards = Model.unit_bias_rewards m (v, a) in
                   let* pending = pending_rewards m (v, a) st in
                   let rewards = U256.(del.rewards + pending) in
                   let* () =
                     ensure "the model's rewards are at most the delegator's plus the error bound"
                       U256.(unit_bias_rewards <= (rewards + error_bound) * unit_bias)
                   in
                   ensure "the model's rewards are at least the delegator's"
                     U256.(
                       (rewards + error_bound) * unit_bias <= unit_bias_rewards + (error_bound * unit_bias) )
                 in
                 let* () =
                   ensure "the model's delegator stake matches the contract"
                     U256.(Model.delegator_stake m (v, a) epoch = active_stake ~epoch del)
                 in
                 let withdrawal_stake =
                   List.fold_left
                     (fun sum (req : Staking.Withdrawal_request.t) ->
                       if Epoch.(req.epoch > epoch) then U256.(sum + req.amount) else sum )
                     U256.zero requests
                 in
                 ensure "the model's withdrawal stake matches the contract"
                   U256.(Model.withdrawal_stake m (v, a) epoch = withdrawal_stake) ) )
            addresses )
        val_ids
    in
    iter_r
      (fun v ->
        let stake =
          List.fold_left
            (fun sum a ->
              U256.(sum + Model.delegator_stake m (v, a) epoch + Model.withdrawal_stake m (v, a) epoch) )
            U256.zero addresses
        in
        let active = Model.active_consensus_stake m v in
        at ~val_id:v
          (ensure "the active consensus stake is the model's delegator and withdrawal stake"
             U256.(active = zero || active = stake) ) )
      val_ids

  let accumulated_rewards_invariants (m : Model.t) val_ids addresses st =
    let epoch = epoch st in
    let epochs =
      let (Epoch.Epoch e) = epoch in
      let first = Epoch.Epoch U64.(if e >= of_int 2 then e - of_int 2 else zero) in
      let last = epoch_add epoch 4 in
      let rec from e = if Epoch.(e > last) then [] else e :: from (epoch_add e 1) in
      from first
    in
    iter_r
      (fun v ->
        at ~val_id:v
          (let ve = val_execution v st in
           let delegators =
             List.map
               (fun a ->
                 let requests =
                   List.filter_map
                     (fun i -> withdrawal_request v a i st)
                     (Int_set.elements (Model.withdrawal_ids m (v, a)))
                 in
                 (a, delegator v a st, requests) )
               addresses
           in
           let* () =
             iter_r
               (fun e ->
                 let acc = accumulator e v st in
                 let refs e' = if Epoch.(e <> zero) && Epoch.(e' = e) then 1 else 0 in
                 let refcount =
                   List.fold_left
                     (fun n (_, (del : Staking.Delegator.t), requests) ->
                       n
                       + refs del.epochs.delta_epoch
                       + refs del.epochs.next_delta_epoch
                       + List.fold_left
                           (fun n (req : Staking.Withdrawal_request.t) -> n + refs req.epoch)
                           0 requests )
                     0 delegators
                 in
                 let* () =
                   ensure "the accumulator's refcount counts its references"
                     U256.(acc.refcount = of_int refcount)
                 in
                 let* () =
                   ensure "only accumulators for epochs 1 to epoch + 2 are referenced"
                     ((Epoch.(e <> zero) && Epoch.(e <= epoch_add epoch 2)) || U256.(acc.refcount = zero))
                 in
                 let* () =
                   ensure "unreferenced accumulators are zero" U256.(acc.refcount <> zero || acc.value = zero)
                 in
                 let* () =
                   let next = accumulator (epoch_add e 1) v st in
                   ensure "accumulators increase with the epoch"
                     U256.(next.refcount = zero || acc.value <= next.value)
                 in
                 ensure "accumulators are at most the validator's rewards per token"
                   U256.(acc.value <= ve.rewards_per_token) )
               epochs
           in
           iter_r
             (fun (a, (del : Staking.Delegator.t), requests) ->
               at ~val_id:v ~address:a
                 (let* () =
                    iter_r
                      (fun (req : Staking.Withdrawal_request.t) ->
                        ensure "a withdrawal request's accumulator is at most its epoch's"
                          U256.(req.acc <= (accumulator req.epoch v st).value) )
                      requests
                  in
                  let* () =
                    ensure "a delegator's accumulator is at most the validator's rewards per token"
                      U256.(del.rewards_per_token <= ve.rewards_per_token)
                  in
                  let {Staking.Epochs.delta_epoch; next_delta_epoch} = del.epochs in
                  let has_activated e = Epoch.(e <> zero) && Epoch.(e <= epoch) in
                  let* () =
                    if has_activated delta_epoch then
                      ensure "a delegator's accumulator is at most the one at delta_epoch"
                        U256.(del.rewards_per_token <= (accumulator delta_epoch v st).value)
                    else Ok ()
                  in
                  if has_activated next_delta_epoch then
                    let* () =
                      ensure "a delegator's accumulator is at most the one at next_delta_epoch"
                        U256.(del.rewards_per_token <= (accumulator next_delta_epoch v st).value)
                    in
                    ensure "the accumulator at delta_epoch is at most the one at next_delta_epoch"
                      U256.((accumulator delta_epoch v st).value <= (accumulator next_delta_epoch v st).value)
                  else Ok () ) )
             delegators ) )
      val_ids

  let linked_list_invariants val_ids addresses st =
    let* delegator_sets =
      fold_r
        (fun sets v ->
          let delegators = delegators_of v st in
          let set = Address.Set.of_list delegators in
          let* () =
            at ~val_id:v
              (ensure "a validator's delegators are listed once"
                 (Address.Set.cardinal set = List.length delegators) )
          in
          Ok (Val_id.Map.add v set sets) )
        Val_id.Map.empty val_ids
    in
    let* validator_sets =
      fold_r
        (fun sets a ->
          let validators = validators_of a st in
          let set = Val_id.Set.of_list validators in
          let* () =
            if Val_id.Set.cardinal set = List.length validators then Ok ()
            else
              Error
                (Violated
                   ("a delegator's validators are listed once (address 0x" ^ Address.to_hex_string a ^ ")") )
          in
          Ok (Address.Map.add a set sets) )
        Address.Map.empty addresses
    in
    iter_r
      (fun v ->
        iter_r
          (fun a ->
            at ~val_id:v ~address:a
              (let listed = Address.Set.mem a (Val_id.Map.find v delegator_sets) in
               let* () =
                 ensure "the two delegation lists agree"
                   (Bool.equal listed (Val_id.Set.mem v (Address.Map.find a validator_sets)))
               in
               ensure "delegators are listed iff they have stake"
                 (Bool.equal listed U256.(Staking.Delegator.next_epoch_stake (delegator v a st) > zero)) ) )
          addresses )
      val_ids

  let solvency_invariants (m : Model.t) val_ids addresses st =
    let requests v a =
      List.filter_map
        (fun i -> withdrawal_request v a i st)
        (Int_set.elements (Model.withdrawal_ids m (v, a)))
    in
    let* () =
      let owed =
        List.fold_left
          (fun sum v ->
            let ve = val_execution v st in
            List.fold_left
              (fun sum a ->
                List.fold_left
                  (fun sum (req : Staking.Withdrawal_request.t) -> U256.(sum + req.amount))
                  U256.(sum + (delegator v a st).rewards)
                  (requests v a) )
              U256.(sum + ve.stake + ve.unclaimed_rewards)
              addresses )
          U256.zero val_ids
      in
      ensure "the staking balance is the stake, rewards and withdrawals owed" U256.(staking_balance st = owed)
    in
    let error_bound =
      List.fold_left
        (fun bound v ->
          List.fold_left
            (fun bound a ->
              let n = Int_set.cardinal (Model.withdrawal_ids m (v, a)) in
              let n =
                if U256.(Staking.Delegator.next_epoch_stake (delegator v a st) > zero) then n + 3 else n
              in
              U256.(bound + of_int n) )
            bound addresses )
        m.error_bound val_ids
    in
    iter_r
      (fun v ->
        at ~val_id:v
          (let ve = val_execution v st in
           let* pending =
             fold_r
               (fun sum a ->
                 let* rewards = pending_rewards m (v, a) st in
                 Ok U256.(sum + rewards) )
               U256.zero addresses
           in
           let* () =
             ensure "pending rewards are at most the unclaimed rewards" U256.(pending <= ve.unclaimed_rewards)
           in
           let* () =
             ensure "unclaimed rewards are at most the pending rewards plus the error bound"
               U256.(ve.unclaimed_rewards <= pending + error_bound)
           in
           let stake =
             List.fold_left
               (fun sum a -> U256.(sum + Staking.Delegator.next_epoch_stake (delegator v a st)))
               U256.zero addresses
           in
           ensure "a validator's stake is its delegators' stake" U256.(ve.stake = stake) ) )
      val_ids

  let check (m : Model.t) (st : t) : (unit, error) result =
    let* () = ensure "the model tracks the epoch" Epoch.(m.epoch = epoch st) in
    let* () =
      ensure "the model tracks the epoch delay period"
        (Bool.equal m.in_epoch_delay_period (in_epoch_delay_period st))
    in
    let val_ids = val_ids st in
    let addresses = Address.Set.elements m.addresses in
    let* () = valset_invariants m val_ids st in
    let* () = val_execution_invariants val_ids st in
    let* () = delegator_invariants m val_ids addresses st in
    let* () = accumulated_rewards_invariants m val_ids addresses st in
    let* () = linked_list_invariants val_ids addresses st in
    solvency_invariants m val_ids addresses st
end

(** The generators and transitions of the C++ machine. A transition reads both states and sends its commands,
    setup commands first, through [emit], which executes a command as the runner does and returns the new
    states. A transition returns the final states and whether it could be generated, which is the C++ [ok]. *)
module Gen = struct
  module Choice = Fuzz.Choice

  type state = Model.t * Concrete.t
  type 'e emit = state -> Model.cmd -> (state, 'e) result

  let ( let* ) = Result.bind

  let min_delegate_stake = dust_threshold
  let withdrawal_delay = Staking.withdrawal_delay

  (* Addresses. Unlike in the C++, a new address only becomes old once a command that uses it has run. *)

  let new_address rng = Address.of_bytes_exn (Choice.bytes rng 20)

  let new_or_old_address rng (m : Model.t) =
    if Address.Set.is_empty m.addresses then new_address rng
    else
      Choice.discrete_choice rng
        ~default:(fun () -> new_address rng)
        [(0.80, fun () -> Choice.sample rng (Address.Set.elements m.addresses))]

  (* Numbers. *)

  let bound_biased rng ~lower ~upper = Choice.bound_biased_u256 rng ~lower ~upper

  (* A stake between [lower] and [upper] inclusive, biased towards values that the C++ found to increase
     coverage. *)
  let stake rng ~lower ~upper =
    assert (U256.(lower <= upper)) ;
    let candidate x =
      let inside = U256.(lower <= x && x <= upper) in
      if U256.(upper - lower < x) then if inside then Some x else None
      else if inside then
        Some
          (Choice.discrete_choice rng
             ~default:(fun () -> U256.(lower + x))
             [(0.33, fun () -> U256.(upper - x)); (0.33, fun () -> x)] )
      else
        Some
          (Choice.discrete_choice rng
             ~default:(fun () -> U256.(lower + x))
             [(0.50, fun () -> U256.(upper - x))] )
    in
    let around x = [U256.(x - one); x; U256.(x + one)] in
    let thresholds = List.concat_map around [dust_threshold; min_validate_stake; active_validator_stake] in
    match
      Choice.discrete_choice rng
        ~default:(fun () -> None)
        (List.map (fun x -> (0.10, fun () -> candidate x)) thresholds)
    with
    | Some x -> x
    | None -> bound_biased rng ~lower ~upper

  (* Any validator id up to two past the last one. *)
  let any_val_id rng st =
    let (Val_id.Val_id last) = Concrete.get Variables.last_val_id st in
    Val_id.of_int (Random.State.int rng (U64.to_int last + 3))

  let potential_val_id rng (m : Model.t) =
    let random () = Val_id.Val_id (Choice.u64 rng) in
    if Val_id.Map.is_empty m.validators then random ()
    else
      Choice.discrete_choice rng ~default:random
        [(0.50, fun () -> fst (Choice.sample rng (Val_id.Map.bindings m.validators)))]

  (* A delegator's rewards. Computing them fails only if an accumulator invariant does not hold, which
     [Concrete.check] has ruled out. *)
  let rewards v a st =
    match Concrete.delegator_rewards v a st with Ok rewards -> rewards | Error _ -> assert false

  (* Validators and delegators. *)

  (* Add a validator with a stake between [lower] and [upper], returning its id and auth address. *)
  let add_validator rng ~emit ~lower ~upper (((m, _) : state) as s) =
    assert (U256.(min_validate_stake <= lower && upper <= max_stake)) ;
    let sender = new_or_old_address rng m in
    let value = stake rng ~lower ~upper in
    let auth_address = new_or_old_address rng m in
    let commission = bound_biased rng ~lower:U256.zero ~upper:max_commission in
    let secret = B32.of_bytes_exn (Choice.bytes rng 32) in
    let (message, secp_signature, bls_signature), signer =
      craft_add_validator_input ~auth_address ~stake:value ~commission ~secret
    in
    let* (((m, _) : state) as s) =
      emit s (Model.Add_validator {message; secp_signature; bls_signature; signer; sender; value})
    in
    Ok ((Address.Map.find signer m.signers, auth_address), s)

  let validator_auth_address rng ~emit (s : state) =
    let* (((m, _) : state) as s) =
      if Val_id.Map.is_empty (fst s).validators then
        let* _, s = add_validator rng ~emit ~lower:min_validate_stake ~upper:max_stake s in
        Ok s
      else Ok s
    in
    let v, (validator : Model.validator) = Choice.sample rng (Val_id.Map.bindings m.validators) in
    Ok ((v, validator.auth_address), s)

  let delegable_val_id rng ~emit (((m, _) : state) as s) =
    if Val_id.Set.is_empty m.delegable_val_ids then
      let* (v, _), s = add_validator rng ~emit ~lower:min_validate_stake ~upper:max_delegable_stake s in
      Ok (v, s)
    else Ok (Choice.sample rng (Val_id.Set.elements m.delegable_val_ids), s)

  let delegator rng ~emit (s : state) =
    let* (((m, _) : state) as s) =
      if Delegator_set.is_empty (fst s).delegators then
        let* _, s = add_validator rng ~emit ~lower:min_validate_stake ~upper:max_stake s in
        Ok s
      else Ok s
    in
    Ok (Choice.sample rng (Delegator_set.elements m.delegators), s)

  let active_consensus_val_id rng st =
    let valset =
      if Concrete.in_epoch_delay_period st then Variables.valset_snapshot else Variables.valset_consensus
    in
    match Concrete.read_array valset st with [] -> None | val_ids -> Some (Choice.sample rng val_ids)

  let withdrawal_requests (m : Model.t) =
    Delegator_map.fold
      (fun (v, a) ids requests -> Int_set.fold (fun i requests -> (v, a, i) :: requests) ids requests)
      m.withdrawal_ids []

  let skip_epochs ~emit n (((m, _) : state) as s) =
    let rec loop i s =
      if i >= n then Ok s
      else
        let* (((m, _) : state) as s) = emit s Model.Syscall_snapshot in
        let* s = emit s (Model.Syscall_on_epoch_change (epoch_add m.epoch 1)) in
        loop (i + 1) s
    in
    if n = 0 then Ok s
    else if Epoch.(m.epoch = zero) || m.in_epoch_delay_period then
      let* s = emit s (Model.Syscall_on_epoch_change (epoch_add m.epoch 1)) in
      loop 1 s
    else loop 0 s

  (* Command inputs that the C++ generates separately from their transition. *)

  (* An undelegation of at least [lower], or [None] if a few attempts don't find a delegator with enough
     stake. *)
  let undelegate_input rng ~emit ~lower s =
    let rec find i s =
      let* (v, a), (((_, st) : state) as s) = delegator rng ~emit s in
      let del_stake = (Concrete.delegator v a st).stake in
      if U256.(del_stake >= lower) || i >= 9 then Ok ((v, a, del_stake), s) else find (i + 1) s
    in
    let* (v, a, del_stake), s = find 0 s in
    if U256.(del_stake < lower) then Ok (None, s)
    else
      (* A delegator that has used up all withdrawal ids is swapped for a new validator's auth delegator. *)
      let* (v, a, del_stake), (((m, _) : state) as s) =
        if Int_set.cardinal (Model.withdrawal_ids (fst s) (v, a)) < 256 then Ok ((v, a, del_stake), s)
        else
          let* (v, a), (((_, st) : state) as s) =
            add_validator rng ~emit ~lower:min_validate_stake ~upper:max_delegable_stake s
          in
          Ok ((v, a, (Concrete.delegator v a st).stake), s)
      in
      let used = Model.withdrawal_ids m (v, a) in
      let available = List.filter (fun i -> not (Int_set.mem i used)) (List.init 256 Fun.id) in
      let withdrawal_id = U8.of_int (Choice.sample rng available) in
      let amount = stake rng ~lower ~upper:del_stake in
      Ok (Some (Model.Undelegate {val_id = v; amount; withdrawal_id; sender = a}), s)

  (* A delegator whose rewards can be compounded, or [None] if a few attempts don't find one. *)
  let compound_input rng ~emit (((m, st) : state) as s) =
    let fits v rewards st = U256.((Concrete.val_execution v st).stake + rewards <= max_stake) in
    let arbitrary =
      if Choice.with_probability rng 0.005 then
        let v = any_val_id rng st in
        let a = new_or_old_address rng m in
        let r = rewards v a st in
        if fits v r st && U256.(r = zero || r >= min_delegate_stake) then Some (v, a) else None
      else None
    in
    match arbitrary with
    | Some input -> Ok (Some input, s)
    | None ->
        let rec find i s =
          if i >= 10 then Ok (None, s)
          else
            let* (v, a), (((_, st) : state) as s) = delegator rng ~emit s in
            let r = rewards v a st in
            if U256.(r = zero) || (U256.(r >= min_delegate_stake) && fits v r st) then Ok (Some (v, a), s)
            else find (i + 1) s
        in
        find 0 s

  (* Transitions. *)

  let syscall_on_epoch_change rng ~emit (((m, _) : state) as s) =
    let* s =
      if Epoch.(m.epoch = zero) then
        emit s (Model.Syscall_on_epoch_change (Epoch.of_int (1 + Random.State.int rng 1_000_000)))
      else
        let* s = if m.in_epoch_delay_period then Ok s else emit s Model.Syscall_snapshot in
        emit s (Model.Syscall_on_epoch_change (epoch_add m.epoch 1))
    in
    Ok (s, true)

  let syscall_snapshot _rng ~emit (((m, _) : state) as s) =
    if Epoch.(m.epoch = zero) then Ok (s, true)
    else
      let* s =
        if m.in_epoch_delay_period then emit s (Model.Syscall_on_epoch_change (epoch_add m.epoch 1)) else Ok s
      in
      let* s = emit s Model.Syscall_snapshot in
      Ok (s, true)

  let syscall_reward rng ~emit (((m, st) : state) as s) =
    match active_consensus_val_id rng st with
    | None -> Ok (s, false)
    | Some v ->
        let (validator : Model.validator) = Val_id.Map.find v m.validators in
        let reward = bound_biased rng ~lower:U256.zero ~upper:U256.(of_int 1_000_000 * Staking.mon) in
        let* s = emit s (Model.Syscall_reward {block_author = validator.signer; reward}) in
        Ok (s, true)

  let add_validator_transition rng ~emit s =
    let* _, s = add_validator rng ~emit ~lower:min_validate_stake ~upper:max_stake s in
    Ok (s, true)

  let delegate rng ~emit (((m, _) : state) as s) =
    let sender = new_or_old_address rng m in
    let* (val_id, value), s =
      Choice.discrete_choice rng
        ~default:(fun () ->
          let* val_id, (((_, st) : state) as s) = delegable_val_id rng ~emit s in
          let val_stake = (Concrete.val_execution val_id st).stake in
          assert (U256.(val_stake <= max_delegable_stake)) ;
          Ok ((val_id, stake rng ~lower:min_delegate_stake ~upper:U256.(max_stake - val_stake)), s) )
        [(0.01, fun () -> Ok ((potential_val_id rng m, U256.zero), s))]
    in
    let* s = emit s (Model.Delegate {val_id; sender; value}) in
    Ok (s, true)

  let undelegate rng ~emit s =
    let* cmd, s = undelegate_input rng ~emit ~lower:U256.zero s in
    (* Every delegator has at least zero stake. *)
    let* s = emit s (Option.get cmd) in
    Ok (s, true)

  let compound rng ~emit s =
    let* input, s = compound_input rng ~emit s in
    match input with
    | None -> Ok (s, false)
    | Some (val_id, sender) ->
        let* s = emit s (Model.Compound {val_id; sender}) in
        Ok (s, true)

  let withdraw rng ~emit s =
    let* s, has_request =
      match withdrawal_requests (fst s) with
      | _ :: _ -> Ok (s, true)
      | [] -> (
          let* cmd, s = undelegate_input rng ~emit ~lower:U256.one s in
          match cmd with
          | None -> Ok (s, false)
          | Some cmd ->
              let* s = emit s cmd in
              Ok (s, true) )
    in
    if not has_request then Ok (s, false)
    else
      let ((m, st) : state) = s in
      let v, a, i = Choice.sample rng (withdrawal_requests m) in
      (* Skip to the epoch where the request can be withdrawn. *)
      let request_epoch =
        match Concrete.withdrawal_request v a i st with Some req -> req.epoch | None -> Epoch.zero
      in
      let (Epoch.Epoch ready) = epoch_add request_epoch withdrawal_delay in
      let (Epoch.Epoch now) = m.epoch in
      let* s = if U64.(now < ready) then skip_epochs ~emit (U64.to_int U64.(ready - now)) s else Ok s in
      let* s = emit s (Model.Withdraw {val_id = v; withdrawal_id = U8.of_int i; sender = a}) in
      Ok (s, true)

  let claim_rewards rng ~emit (((m, st) : state) as s) =
    let* (val_id, sender), s =
      if Choice.with_probability rng 0.005 then
        let val_id = any_val_id rng st in
        Ok ((val_id, new_or_old_address rng m), s)
      else delegator rng ~emit s
    in
    let* s = emit s (Model.Claim_rewards {val_id; sender}) in
    Ok (s, true)

  let change_commission rng ~emit s =
    let* (val_id, sender), s = validator_auth_address rng ~emit s in
    let commission = bound_biased rng ~lower:U256.zero ~upper:max_commission in
    let* s = emit s (Model.Change_commission {val_id; commission; sender}) in
    Ok (s, true)

  let external_reward rng ~emit (((m, st) : state) as s) =
    match active_consensus_val_id rng st with
    | None -> Ok (s, false)
    | Some val_id ->
        let sender = new_or_old_address rng m in
        let value = bound_biased rng ~lower:Staking.min_external_reward ~upper:Staking.max_external_reward in
        let* s = emit s (Model.External_reward {val_id; sender; value}) in
        Ok (s, true)

  let get_delegator rng ~emit (((m, st) : state) as s) =
    let* (val_id, address, sender), s =
      Choice.discrete_choice rng
        ~default:(fun () ->
          let* (val_id, address), (((m, _) : state) as s) = delegator rng ~emit s in
          Ok ((val_id, address, new_or_old_address rng m), s) )
        [ ( 0.05
          , fun () ->
              let val_id = any_val_id rng st in
              let address = new_or_old_address rng m in
              Ok ((val_id, address, new_or_old_address rng m), s) ) ]
    in
    let* s = emit s (Model.Get_delegator {val_id; address; sender}) in
    Ok (s, true)

  (** The start of a C++ run: with probability 0.001 each, add [active_valset_size - 1] or 260 validators with
      active stake. *)
  let start rng ~emit (s : state) =
    let add n s =
      let rec loop i s =
        if i >= n then Ok s
        else
          let* _, s = add_validator rng ~emit ~lower:active_validator_stake ~upper:max_stake s in
          loop (i + 1) s
      in
      let* (((_, st) : state) as s) = loop 0 s in
      assert (List.length (Concrete.read_array Variables.valset_execution st) = n) ;
      Ok s
    in
    Choice.discrete_choice rng
      ~default:(fun () -> Ok s)
      [(0.001, fun () -> add (active_valset_size - 1) s); (0.001, fun () -> add 260 s)]

  (** One step of a C++ run: a random transition, then, with probability 0.2, skipping [withdrawal_delay]
      epochs so that withdrawal requests become ready. *)
  let transition rng ~emit s =
    let transition =
      let p = Random.State.int rng 100 in
      if p < 20 then syscall_reward
      else if p < 30 then external_reward
      else
        match Random.State.int rng 12 with
        | 0 -> syscall_on_epoch_change
        | 1 -> syscall_snapshot
        | 2 -> syscall_reward
        | 3 -> add_validator_transition
        | 4 -> delegate
        | 5 -> undelegate
        | 6 -> compound
        | 7 -> withdraw
        | 8 -> claim_rewards
        | 9 -> change_commission
        | 10 -> external_reward
        | _ -> get_delegator
    in
    let* s, generated = transition rng ~emit s in
    let* s = if Choice.with_probability rng 0.20 then skip_epochs ~emit withdrawal_delay s else Ok s in
    Ok (s, generated)
end

module _ : Fuzz.MODEL = Model
module _ : Fuzz.CONCRETE = Concrete
