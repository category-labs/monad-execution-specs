open Byte_string
open Numeric
open State
open Chain.Ethereum

module Error = struct
  type t =
    | Internal_error
    | Method_not_supported
    | Invalid_input
    | Validator_exists
    | Unknown_validator
    | Unknown_delegator
    | Withdrawal_id_exists
    | Unknown_withdrawal_id
    | Withdrawal_not_ready
    | Insufficient_stake
    | Invalid_secp_pubkey
    | Invalid_bls_pubkey
    | Invalid_secp_signature
    | Invalid_bls_signature
    | Secp_signature_verification_failed
    | Bls_signature_verification_failed
    | Not_in_validator_set
    | Solvency_error
    | Snapshot_in_boundary
    | Invalid_epoch_change
    | Requires_auth_address
    | Commission_too_high
    | Delegation_too_small
    | External_reward_too_small
    | External_reward_too_large
    | Length_mismatch
    | Arithmetic_error of Numeric.arithmetic_error
    (* Generic error messages produced by the contract harness. *)
    | Value_non_zero
    | Input_too_short

  (* Error messages are returned as output data from the staking contract, so this is observable. *)
  let encode_error = function
    | Internal_error -> "internal error"
    | Method_not_supported -> "method not supported"
    | Invalid_input -> "invalid input"
    | Validator_exists -> "validator exists"
    | Unknown_validator -> "unknown validator"
    | Unknown_delegator -> "unknown delegator"
    | Withdrawal_id_exists -> "withdrawal id exists"
    | Unknown_withdrawal_id -> "unknown withdrawal id"
    | Withdrawal_not_ready -> "withdrawal not ready"
    | Insufficient_stake -> "insufficient stake"
    | Invalid_secp_pubkey -> "invalid secp pubkey"
    | Invalid_bls_pubkey -> "invalid bls pubkey"
    | Invalid_secp_signature -> "invalid secp signature"
    | Invalid_bls_signature -> "invalid bls signature"
    | Secp_signature_verification_failed -> "secp signature verification failed"
    | Bls_signature_verification_failed -> "bls signature verification failed"
    | Not_in_validator_set -> "not in validator set"
    | Solvency_error -> "solvency error"
    | Snapshot_in_boundary -> "called snapshot while in boundary"
    | Invalid_epoch_change -> "invalid epoch change"
    | Requires_auth_address -> "requires auth address"
    | Commission_too_high -> "commission too high"
    | Delegation_too_small -> "delegation is too small"
    | External_reward_too_small -> "external reward too small"
    | External_reward_too_large -> "external reward too large"
    | Length_mismatch -> "length mismatch"
    | Arithmetic_error Overflow -> "overflow"
    | Arithmetic_error Underflow -> "underflow"
    | Arithmetic_error Division_by_zero -> "division by zero"
    | Value_non_zero -> "value is nonzero"
    | Input_too_short -> "input too short"
end
type error = Error.t

let staking_address = Address.of_hex_string "0x1000"
let staking_account = TransactionState.account staking_address

module Contract = Contract.Make (struct
  let address = staking_address
  type error = Error.t
  let encode_error = Error.encode_error

  let value_non_zero = Error.Value_non_zero
  let decode_error : Contract.Type.decode_error -> Error.t = function
    | Input_too_short -> Input_too_short
    | Input_too_long | Length_overflow | Map_error _ -> Invalid_input
end)
include Contract

(* Both validator ids and epochs are represented by U64.t. In order to prevent confusion, we create
   separate types, but note that the type name is identical so they give the same function signature
   hashes. *)
(* TODO: this would be a good reason to separate Val_id.internal and Val_id.external. *)
module Val_id = struct
  type t = Val_id of U64.t

  let zero = Val_id U64.zero
  let one = Val_id U64.one

  let of_int i = Val_id (U64.of_int i)

  let sentinel = Val_id U64.(lognot zero)

  let t =
    let repr = Type.U64.t in
    let encode (Val_id i) = i in
    let decode i = Ok (Val_id i) in
    let name = Type.type_name Type.U64.t in
    Type.Map {repr; encode; decode; name}
  let t_option = Type.option ~empty:zero t

  include Comparable.Make (struct
    type nonrec t = t
    let compare (Val_id e1) (Val_id e2) = U64.(compare e1 e2)
  end)
end

module Epoch = struct
  type t = Epoch of U64.t

  let zero = Epoch U64.zero
  let one = Epoch U64.one

  let of_int i = Epoch (U64.of_int i)

  let t =
    let repr = Type.U64.t in
    let encode (Epoch i) = i in
    let decode i = Ok (Epoch i) in
    let name = Type.type_name Type.U64.t in
    Type.Map {repr; encode; decode; name}

  (* More useful than symmetric binary addition. The C++ implementation here over/underflows silently and
     wraps around. *)
  let ( + ) (Epoch e1) (d : int) : (t, Numeric.arithmetic_error) result =
    match U64.(Checked.(e1 + ~$d)) with Ok result -> Ok (Epoch result) | Error err -> Error err
  let ( - ) (Epoch e1) (d : int) : (t, Numeric.arithmetic_error) result =
    match U64.(Checked.(e1 - ~$d)) with Ok result -> Ok (Epoch result) | Error err -> Error err
  include Comparable.Make (struct
    type nonrec t = t
    let compare (Epoch e1) (Epoch e2) = U64.(compare e1 e2)
  end)
end

module M = struct
  include Contract.M
  open Lens.Infix

  (* Embed an arithmetic error into a staking contract computation. *)
  let checked_arith (v : ('a, Numeric.arithmetic_error) result) : 'a t =
    match v with Ok v -> return v | Error err -> fail (Arithmetic_error err)

  (* Send tokens from the staking contract. *)
  let send_tokens ~(to_ : Address.t) ~(amount : U256.t) : unit t =
    let$ bal = !(staking_account |-- Account.balance) in
    let$ () = when_ U256.(bal < amount) (fail Internal_error) in
    let$ () = staking_account |-- Account.balance := U256.(bal - amount) in
    update_field (account to_ |-- Account.balance) (fun b -> U256.(b + amount))
end

open Type

module Address_flags = struct
  type t = {auth_address : Address.t; flags : U64.t}

  let empty = {auth_address = Address.zero; flags = U64.zero}

  let t =
    let repr = Packed.t (Tuple [Address.t; U64.t]) in
    let encode {auth_address; flags} = Tuple.[auth_address; flags] in
    let decode Tuple.[auth_address; flags] = Ok {auth_address; flags} in
    let name = "address_flags" in
    Map {repr; encode; decode; name}

  let flag (mask_set : U64.t) : (t, bool) Lens.t =
    let get {flags; _} = U64.(mask_set = logand flags mask_set) in
    let set b ({flags; _} as af) =
      let flags = if b then U64.(logor flags mask_set) else U64.(logand flags (lognot mask_set)) in
      {af with flags}
    in
    Lens.{get; set}

  let ok = U64.zero
  let stake_too_low = U64.(shift_left one 0)
  let withdrawn = U64.(shift_left one 1)
  let double_sign = U64.(shift_left one 2)
end

module Keys = struct
  type t = {secp_pubkey : B33.t; bls_pubkey : B48.t}

  let empty = {secp_pubkey = B33.zeros; bls_pubkey = B48.zeros}

  let t =
    let repr = Packed.t (Tuple [B33.t; B48.t]) in
    let encode {secp_pubkey; bls_pubkey} = Tuple.[secp_pubkey; bls_pubkey] in
    let decode Tuple.[secp_pubkey; bls_pubkey] = Ok {secp_pubkey; bls_pubkey} in
    let name = "keys" in
    Map {repr; encode; decode; name}
end

module Val_execution = struct
  type t =
    { stake : U256.t
    ; rewards_per_token : U256.t
    ; commission : U256.t
    ; keys : Keys.t
    ; address_flags : Address_flags.t
    ; unclaimed_rewards : U256.t }
  [@@deriving lens {submodule = true; prefix = true}]
  include TLens

  let empty =
    { stake = U256.zero
    ; rewards_per_token = U256.zero
    ; commission = U256.zero
    ; keys = Keys.empty
    ; address_flags = Address_flags.empty
    ; unclaimed_rewards = U256.zero }

  let t =
    let repr = Tuple [U256.t; U256.t; U256.t; Keys.t; Address_flags.t; U256.t] in
    let encode v =
      Tuple.[v.stake; v.rewards_per_token; v.commission; v.keys; v.address_flags; v.unclaimed_rewards]
    in
    let decode Tuple.[stake; rewards_per_token; commission; keys; address_flags; unclaimed_rewards] =
      Ok {stake; rewards_per_token; commission; keys; address_flags; unclaimed_rewards}
    in
    let name = "val_execution" in
    Map {repr; encode; decode; name}
end

module Consensus_view = struct
  type t = {stake : U256.t; commission : U256.t}

  let empty = {stake = U256.zero; commission = U256.zero}

  let t =
    (* Like Val_execution.t but only the relevant fields are available. *)
    let repr = Packed.t (Tuple [U256.t; U256.t]) in
    let encode v = Tuple.[v.stake; v.commission] in
    let decode Tuple.[stake; commission] = Ok {stake; commission} in
    let name = "consensus_view" in
    Map {repr; encode; decode; name}
end

module Snapshot_view = Consensus_view

module Epochs = struct
  type t = {delta_epoch : Epoch.t; next_delta_epoch : Epoch.t}

  let empty = {delta_epoch = Epoch.zero; next_delta_epoch = Epoch.zero}

  let t =
    let repr = Packed.t (Tuple [Epoch.t; Epoch.t]) in
    let encode {delta_epoch; next_delta_epoch} = Tuple.[delta_epoch; next_delta_epoch] in
    let decode Tuple.[delta_epoch; next_delta_epoch] = Ok {delta_epoch; next_delta_epoch} in
    let name = "epochs" in
    Map {repr; encode; decode; name}
end

module List_node = struct
  type t = {inext : Val_id.t; iprev : Val_id.t; anext : Address.t; aprev : Address.t}
  [@@deriving lens {submodule = true; prefix = true}]
  include TLens

  let empty = {inext = Val_id.zero; iprev = Val_id.zero; anext = Address.zero; aprev = Address.zero}

  let t =
    let repr = Packed.t (Tuple [Val_id.t; Val_id.t; Address.t; Address.t]) in
    let encode v = Tuple.[v.inext; v.iprev; v.anext; v.aprev] in
    let decode Tuple.[inext; iprev; anext; aprev] = Ok {inext; iprev; anext; aprev} in
    let name = "list_node" in
    Map {repr; encode; decode; name}
end

module Delegator = struct
  type t =
    { stake : U256.t
    ; rewards_per_token : U256.t
    ; rewards : U256.t
    ; delta_stake : U256.t
    ; next_delta_stake : U256.t
    ; epochs : Epochs.t
    ; list_node : List_node.t }
  [@@deriving lens {submodule = true; prefix = true}]
  include TLens

  let empty =
    { stake = U256.zero
    ; rewards_per_token = U256.zero
    ; rewards = U256.zero
    ; delta_stake = U256.zero
    ; next_delta_stake = U256.zero
    ; epochs = Epochs.empty
    ; list_node = List_node.empty }

  let t =
    let repr = Tuple [U256.t; U256.t; U256.t; U256.t; U256.t; Epochs.t; List_node.t] in
    let encode d =
      Tuple.[d.stake; d.rewards_per_token; d.rewards; d.delta_stake; d.next_delta_stake; d.epochs; d.list_node]
    in
    let decode Tuple.[stake; rewards_per_token; rewards; delta_stake; next_delta_stake; epochs; list_node] =
      Ok {stake; rewards_per_token; rewards; delta_stake; next_delta_stake; epochs; list_node}
    in
    let name = "delegator" in
    Map {repr; encode; decode; name}

  let next_epoch_stake {stake; delta_stake; next_delta_stake; _} =
    U256.(stake + delta_stake + next_delta_stake)
end

module Withdrawal_request = struct
  type t = {amount : U256.t; acc : U256.t; epoch : Epoch.t}
  let empty = {amount = U256.zero; acc = U256.zero; epoch = Epoch.zero}
  let t =
    let repr = Packed.t (Tuple [U256.t; U256.t; Epoch.t]) in
    let encode {amount; acc; epoch} = Tuple.[amount; acc; epoch] in
    let decode Tuple.[amount; acc; epoch] = Ok {amount; acc; epoch} in
    let name = "withdrawal_request" in
    Map {repr; encode; decode; name}
end

module Ref_counted_accumulator = struct
  type t = {value : U256.t; refcount : U256.t}
  let empty = {value = U256.zero; refcount = U256.zero}
  let t =
    let repr = Packed.t (Tuple [U256.t; U256.t]) in
    let encode {value; refcount} = Tuple.[value; refcount] in
    let decode Tuple.[value; refcount] = Ok {value; refcount} in
    let name = "ref_counted_accumulator" in
    Map {repr; encode; decode; name}
end

module Variables = struct
  open Storage
  let epoch_address = U256.of_string "0x0000000000000000000000000000000000000000000000000000000000000001"
  let in_epoch_delay_period_address =
    U256.of_string "0x0000000000000000000000000000000000000000000000000000000000000002"
  let last_val_id_address =
    U256.of_string "0x0000000000000000000000000000000000000000000000000000000000000003"
  let proposer_val_id_address =
    U256.of_string "0x0000000000000000000000000000000000000000000000000000000000000004"

  (* The staking contract stores numeric types in a packed (left-aligned) representation. However, outside of
     this module, the Solidity ABIs expect them to be right-aligned. *)
  let packed_epoch_t = Type.Packed.t Epoch.t
  let packed_val_id_t = Type.Packed.t Val_id.t
  let packed_val_id_t_option = Type.Packed.t Val_id.t_option
  let packed_bool_t = Type.Packed.t bool

  let epoch = Loc.(packed_epoch_t @ epoch_address)
  let in_epoch_delay_period = Loc.(packed_bool_t @ in_epoch_delay_period_address)
  let last_val_id = Loc.(packed_val_id_t @ last_val_id_address)
  let proposer_val_id = Loc.(packed_val_id_t @ proposer_val_id_address)

  let valset_execution_address =
    U256.of_string "0x0100000000000000000000000000000000000000000000000000000000000000"
  let valset_consensus_address =
    U256.of_string "0x0200000000000000000000000000000000000000000000000000000000000000"
  let valset_snapshot_address =
    U256.of_string "0x0300000000000000000000000000000000000000000000000000000000000000"

  let valset_execution = Array.make valset_execution_address packed_val_id_t
  let valset_consensus = Array.make valset_consensus_address packed_val_id_t
  let valset_snapshot = Array.make valset_snapshot_address packed_val_id_t

  module Ns = struct
    let consensus_stake = "\x04"
    let snapshot_stake = "\x05"
    let val_id_secp = "\x06"
    let val_id_bls = "\x07"
    let val_bitset = "\x08"
    let val_execution = "\x09"
    let accumulator = "\x0A"
    let delegator = "\x0B"
    let withdrawal_request = "\x0C"
  end

  let val_id = Mapping.(make Index.(namespace Ns.val_id_secp address) packed_val_id_t_option)
  let val_id_bls = Mapping.(make Index.(namespace Ns.val_id_bls address) packed_val_id_t_option)

  let val_bitset_bucket =
    Mapping.(
      let val_id_shifted : Val_id.t Index.t = fun (Val_id k) -> Index.u64 U64.(shift_right k 8) in
      make Index.(namespace Ns.val_bitset val_id_shifted) U256.t )

  let val_id_index (Val_id.Val_id i) = Mapping.Index.u64 i
  let val_execution = Mapping.(make Index.(namespace Ns.val_execution val_id_index) Val_execution.t)
  let val_execution_opt =
    Mapping.(
      make Index.(namespace Ns.val_execution val_id_index) (option ~empty:Val_execution.empty Val_execution.t) )

  let consensus_view = Mapping.(make Index.(namespace Ns.consensus_stake val_id_index) Consensus_view.t)
  let snapshot_view = Mapping.(make Index.(namespace Ns.snapshot_stake val_id_index) Snapshot_view.t)

  let delegator = Mapping.(make Index.(namespace Ns.delegator (pair val_id_index address)) Delegator.t)
  let delegator_opt =
    Mapping.(
      make
        Index.(namespace Ns.delegator (pair val_id_index address))
        (option ~empty:Delegator.empty Delegator.t) )

  let withdrawal_request =
    Mapping.(
      make
        Index.(namespace Ns.withdrawal_request (tuple3 val_id_index address u8))
        (option ~empty:Withdrawal_request.empty Withdrawal_request.t) )

  let epoch_index (Epoch.Epoch i) = Mapping.Index.u64 i
  let accumulated_reward_per_token =
    Mapping.(make Index.(namespace Ns.accumulator (pair epoch_index val_id_index)) Ref_counted_accumulator.t)
  let accumulated_reward_per_token_opt =
    Mapping.(
      make
        Index.(namespace Ns.accumulator (pair epoch_index val_id_index))
        (option ~empty:Ref_counted_accumulator.empty Ref_counted_accumulator.t) )
end

let get_this_epoch_valset =
  M.(
    let$ in_epoch_delay_period = !$Variables.in_epoch_delay_period in
    let valset = if in_epoch_delay_period then Variables.valset_snapshot else Variables.valset_consensus in
    lift (Storage.Array.read_to_list valset) )

let get_this_epoch_view val_id =
  M.(
    let$ in_epoch_delay_period = !$Variables.in_epoch_delay_period in
    let view = if in_epoch_delay_period then Variables.snapshot_view else Variables.consensus_view in
    !$(view val_id) )

(* Intrusive linked lists. *)
module Linked_list (N : sig
  type node
  type key
  type ptr
  val sentinel : ptr
  val empty : ptr
  val prev : (node, ptr) Lens.t
  val next : (node, ptr) Lens.t
  val loc : key -> ptr -> node Storage.Loc.t
end) =
struct
  open N
  let insert (key : key) (this_ptr : ptr) =
    M.(
      (* C++ linked_list_insert returns StakingError::InvalidInput here
         (staking_contract.cpp:1984). *)
      let$ () = when_ (this_ptr = empty || this_ptr = sentinel) (fail Invalid_input) in

      let$ this_node = !$(loc key this_ptr) in
      when_
        (this_node.^(prev) = empty)
        (let$ sentinel_node = !$(loc key sentinel) in
         let next_ptr = sentinel_node.^(next) in
         let$ () =
           when_ (next_ptr <> empty)
             (let$ next = !$(loc key next_ptr) in
              let next = next.^(prev) <- this_ptr in
              loc key next_ptr $= next )
         in

         let this_node = this_node.^(prev) <- sentinel in
         let this_node = this_node.^(next) <- next_ptr in
         let sentinel_node = sentinel_node.^(next) <- this_ptr in

         let$ () = loc key this_ptr $= this_node in
         let$ () = loc key sentinel $= sentinel_node in

         return () ) )

  let remove (key : key) (this_ptr : ptr) =
    M.(
      let$ () = when_ (this_ptr = empty || this_ptr = sentinel) (fail Internal_error) in

      let$ this_node = !$(loc key this_ptr) in
      when_
        (this_node.^(prev) <> empty)
        (let prev_ptr = this_node.^(prev) in
         let next_ptr = this_node.^(next) in

         let$ prev_node = !$(loc key prev_ptr) in
         let prev_node = prev_node.^(next) <- next_ptr in
         let$ () = loc key prev_ptr $= prev_node in

         let$ () =
           when_ (next_ptr <> empty)
             (let$ next_node = !$(loc key next_ptr) in
              let next_node = next_node.^(prev) <- prev_ptr in
              loc key next_ptr $= next_node )
         in
         let this_node = this_node.^(prev) <- empty in
         let this_node = this_node.^(next) <- empty in
         let$ () = loc key this_ptr $= this_node in

         return () ) )

  let traverse (key : key) (start : ptr) (limit : int) : (bool * ptr * ptr list) M.t =
    M.(
      let$ start =
        if start = empty then
          let$ node = !$(loc key sentinel) in
          return node.^(next)
        else return start
      in
      let rec loop (ptr : ptr) (acc : ptr list) (count : int) : (bool * ptr * ptr list) M.t =
        if ptr = empty || ptr = sentinel then return (true, empty, List.rev acc)
        else if count = 0 then return (false, ptr, List.rev acc)
        else
          let$ node = !$(loc key ptr) in
          loop node.^(next) List.(ptr :: acc) (count - 1)
      in
      let$ head = !$(loc key start) in
      if head.^(prev) = empty then (* Bogus pointer, not in list. *) return (true, start, List.[])
      else loop start [] limit )
end

module Validators_for_delegator = Linked_list (struct
  open Lens.Infix
  type node = Delegator.t
  type key = Address.t
  type ptr = Val_id.t
  let sentinel = Val_id.sentinel
  let empty = Val_id.zero
  let prev = Delegator.list_node |-- List_node.iprev
  let next = Delegator.list_node |-- List_node.inext
  let loc key ptr = Variables.delegator (ptr, key)
end)

module Delegators_for_validator = Linked_list (struct
  open Lens.Infix
  type node = Delegator.t
  type key = Val_id.t
  type ptr = Address.t
  let sentinel = Address.ones
  let empty = Address.zero
  let prev = Delegator.list_node |-- List_node.aprev
  let next = Delegator.list_node |-- List_node.anext
  let loc key ptr = Variables.delegator (key, ptr)
end)

(* Constants. *)

let mon = U256.of_int 1_000_000_000_000_000_000

let dust_threshold = U256.of_int 1_000_000_000

let max_commission = mon
let active_validator_stake = U256.(~$10_000_000 * mon)
let min_auth_address_stake = U256.(~$100_000 * mon)

let min_external_reward = dust_threshold
let max_external_reward = U256.of_string "10000000000000000000000000"

let max_block_reward = U256.(~$25 * mon)

let unit_bias = U256.of_string "1000000000000000000000000000000000000"

let active_valset_size = 200

let array_pagination = 100

let linked_list_pagination = 50

let withdrawal_delay = 1

(* Helpers. *)

let is_epoch_active ~epoch active_epoch = Epoch.(active_epoch <> zero) && Epoch.(active_epoch <= epoch)

let activation_epoch ~epoch ~in_epoch_delay_period : (Epoch.t, Numeric.arithmetic_error) result =
  if in_epoch_delay_period then Epoch.(epoch + 2) else Epoch.(epoch + 1)

let increment_accumulator_refcount
    ~(val_execution : Val_execution.t) ~(accumulator : Ref_counted_accumulator.t) =
  let reward = val_execution.rewards_per_token in
  Ref_counted_accumulator.{refcount = U256.(accumulator.refcount + one); value = reward}

let decrement_accumulator_refcount ~(accumulator : Ref_counted_accumulator.t) :
    Ref_counted_accumulator.t * U256.t =
  let Ref_counted_accumulator.{refcount; value} = accumulator in
  if U256.(refcount = zero) then (Ref_counted_accumulator.empty, U256.zero)
  else
    let accumulator =
      if U256.(refcount = one) then Ref_counted_accumulator.empty
      else {accumulator with refcount = U256.(refcount - one)}
    in
    (accumulator, value)

let val_id_to_mask (Val_id val_id : Val_id.t) =
  let lower_byte = Char.code (U64.byte ~index_le:0 val_id) in
  U256.(shift_left one lower_byte)

let add_to_valset (val_id : Val_id.t) (val_bitset_bucket : U256.t) =
  let mask = val_id_to_mask val_id in
  let added = U256.(zero = logand val_bitset_bucket mask) in
  (U256.(logor val_bitset_bucket mask), added)

let remove_from_valset (val_id : Val_id.t) (val_bitset_bucket : U256.t) =
  let mask = val_id_to_mask val_id in
  U256.(logand val_bitset_bucket (lognot mask))

let promote_delta (del : Delegator.t) =
  let epochs = Epochs.{delta_epoch = del.epochs.next_delta_epoch; next_delta_epoch = Epoch.zero} in
  {del with delta_stake = del.next_delta_stake; next_delta_stake = U256.zero; epochs}

let calculate_rewards ~(stake : U256.t) ~(current_acc : U256.t) ~(last_checked_acc : U256.t) =
  Result.(
    let open U256.Checked in
    let$ delta = current_acc - last_checked_acc in
    let$ ds = delta * stake in
    ds / unit_bias )

let apply_compound ~(delegator : Delegator.t) ~(accumulator : Ref_counted_accumulator.t) :
    (U256.t * Ref_counted_accumulator.t * Delegator.t, Numeric.arithmetic_error) result =
  Result.(
    let accumulator, epoch_acc = decrement_accumulator_refcount ~accumulator in
    let$ rewards =
      calculate_rewards ~stake:delegator.stake ~current_acc:epoch_acc
        ~last_checked_acc:delegator.rewards_per_token
    in
    let$ stake = U256.Checked.(delegator.stake + delegator.delta_stake) in

    (* Set rewards_per_token to epoch_acc so that the caller's final step computes additional
       rewards from the epoch boundary onward, matching C++ del.accumulated_reward_per_token().store(epoch_acc). *)
    let delegator = {(promote_delta delegator) with rewards_per_token = epoch_acc; stake} in

    return (rewards, accumulator, delegator) )

let reward_invariant ~(validator : Val_execution.t) ~(rewards : U256.t) =
  let is_solvent = U256.(validator.unclaimed_rewards >= rewards) in
  if is_solvent then
    (* This subtraction cannot underflow. *)
    Ok {validator with unclaimed_rewards = U256.(validator.unclaimed_rewards - rewards)}
  else Error Error.Solvency_error

let pull_delegator_up_to_date ((val_id : Val_id.t), (del : Address.t)) : (Val_execution.t * Delegator.t) M.t =
  M.(
    let$ delegator = !$(Variables.delegator (val_id, del)) in
    let$ epoch = !$Variables.epoch in
    let$ next_epoch = checked_arith Epoch.(epoch + 1) in

    let delegator =
      let can_promote_delta =
        Epoch.(delegator.epochs.delta_epoch = zero) && Epoch.(delegator.epochs.next_delta_epoch <= next_epoch)
      in
      if can_promote_delta then promote_delta delegator else delegator
    in
    let$ validator = !$(Variables.val_execution val_id) in

    let can_compound = is_epoch_active ~epoch delegator.epochs.delta_epoch in
    let can_compound_boundary = is_epoch_active ~epoch delegator.epochs.next_delta_epoch in

    let$ validator, delegator =
      if can_compound_boundary then
        let$ () = when_ (not can_compound) (fail Error.Internal_error) in
        let epoch = delegator.epochs.delta_epoch in
        let$ accumulator = !$(Variables.accumulated_reward_per_token (epoch, val_id)) in
        let$ rewards, accumulator, delegator = checked_arith (apply_compound ~accumulator ~delegator) in
        let$ validator = or_fail (reward_invariant ~validator ~rewards) in
        let$ rewards = checked_arith U256.Checked.(delegator.rewards + rewards) in
        let$ () = Variables.accumulated_reward_per_token (epoch, val_id) $= accumulator in
        return (validator, {delegator with rewards})
      else return (validator, delegator)
    in
    let$ validator, delegator =
      if can_compound then
        let epoch = delegator.epochs.delta_epoch in
        let$ accumulator = !$(Variables.accumulated_reward_per_token (epoch, val_id)) in
        let$ rewards, accumulator, delegator = checked_arith (apply_compound ~accumulator ~delegator) in
        let$ validator = or_fail (reward_invariant ~validator ~rewards) in
        let$ rewards = checked_arith U256.Checked.(delegator.rewards + rewards) in
        let$ () = Variables.accumulated_reward_per_token (epoch, val_id) $= accumulator in
        return (validator, {delegator with rewards})
      else return (validator, delegator)
    in

    if U256.(delegator.stake = zero) then return (validator, delegator)
    else
      let$ rewards =
        checked_arith
          (calculate_rewards ~stake:delegator.stake ~current_acc:validator.rewards_per_token
             ~last_checked_acc:delegator.rewards_per_token )
      in
      let$ validator = or_fail (reward_invariant ~validator ~rewards) in
      let$ rewards = checked_arith U256.Checked.(delegator.rewards + rewards) in
      let delegator = {delegator with rewards; rewards_per_token = validator.rewards_per_token} in
      return (validator, delegator) )

let apply_reward ~(val_execution : Val_execution.t) ~(new_rewards : U256.t) ~(active_stake : U256.t) :
    (Val_execution.t, Numeric.arithmetic_error) result =
  Result.(
    let$ reward_acc =
      U256.Checked.(
        let$ product = new_rewards * unit_bias in
        product / active_stake )
    in
    let$ rewards_per_token = U256.Checked.(val_execution.rewards_per_token + reward_acc) in
    let$ unclaimed_rewards = U256.Checked.(val_execution.unclaimed_rewards + new_rewards) in
    return {val_execution with rewards_per_token; unclaimed_rewards} )

(* Events. *)
let check_hash ev hash = assert (B32.(Abi.Event.encode_header ev = ~@hash))

let validator_rewarded_event =
  Abi.Event.
    { name = "ValidatorRewarded"
    ; anonymous = false
    ; indexed_parameter_types = [U64.t; Address.t]
    ; non_indexed_parameter_types = [U256.t; U64.t] }
let () =
  check_hash validator_rewarded_event "3a420a01486b6b28d6ae89c51f5c3bde3e0e74eecbb646a0c481ccba3aae3754"
let emit_validator_rewarded_event ~val_id:(Val_id.Val_id val_id) ~from ~amount : unit M.t =
  M.(
    let$ (Epoch epoch) = !$Variables.epoch in
    emit_event validator_rewarded_event [val_id; from] [amount; epoch] )

let validator_created_event =
  Abi.Event.
    { name = "ValidatorCreated"
    ; anonymous = false
    ; indexed_parameter_types = [U64.t; Address.t]
    ; non_indexed_parameter_types = [U256.t] }
let () = check_hash validator_created_event "6f8045cd38e512b8f12f6f02947c632e5f25af03aad132890ecf50015d97c1b2"
let emit_validator_created_event ~val_id:(Val_id.Val_id val_id) ~auth_delegator ~commission : unit M.t =
  M.emit_event validator_created_event [val_id; auth_delegator] [commission]

let validator_status_changed_event =
  Abi.Event.
    { name = "ValidatorStatusChanged"
    ; anonymous = false
    ; indexed_parameter_types = [U64.t]
    ; non_indexed_parameter_types = [U64.t] }
let () =
  check_hash validator_status_changed_event "c95966754e882e03faffaf164883d98986dda088d09471a35f9e55363daf0c53"
let emit_validator_status_changed_event ~val_id:(Val_id.Val_id val_id) ~flags : unit M.t =
  M.emit_event validator_status_changed_event [val_id] [flags]

let delegation_event =
  Abi.Event.
    { name = "Delegate"
    ; anonymous = false
    ; indexed_parameter_types = [U64.t; Address.t]
    ; non_indexed_parameter_types = [U256.t; U64.t] }
let () = check_hash delegation_event "e4d4df1e1827dd28252fd5c3cd7ebccd3da6e0aa31f74c828f3c8542af49d840"
let emit_delegation_event
    ~val_id:(Val_id.Val_id val_id) ~delegator ~amount ~active_epoch:(Epoch.Epoch active_epoch) : unit M.t =
  M.emit_event delegation_event [val_id; delegator] [amount; active_epoch]

let undelegate_event =
  Abi.Event.
    { name = "Undelegate"
    ; anonymous = false
    ; indexed_parameter_types = [U64.t; Address.t]
    ; non_indexed_parameter_types = [U8.t; U256.t; U64.t] }
let () = check_hash undelegate_event "3e53c8b91747e1b72a44894db10f2a45fa632b161fdcdd3a17bd6be5482bac62"
let emit_undelegate_event
    ~val_id:(Val_id.Val_id val_id)
    ~delegator
    ~withdrawal_id
    ~amount
    ~activation_epoch:(Epoch.Epoch activation_epoch) =
  M.emit_event undelegate_event [val_id; delegator] [withdrawal_id; amount; activation_epoch]

let withdraw_event =
  Abi.Event.
    { name = "Withdraw"
    ; anonymous = false
    ; indexed_parameter_types = [U64.t; Address.t]
    ; non_indexed_parameter_types = [U8.t; U256.t; U64.t] }
let () = check_hash withdraw_event "63030e4238e1146c63f38f4ac81b2b23c8be28882e68b03f0887e50d0e9bb18f"
let emit_withdraw_event ~val_id:(Val_id.Val_id val_id) ~delegator ~withdrawal_id ~amount =
  M.(
    let$ (Epoch withdraw_epoch) = !$Variables.epoch in
    emit_event withdraw_event [val_id; delegator] [withdrawal_id; amount; withdraw_epoch] )

let claim_rewards_event =
  Abi.Event.
    { name = "ClaimRewards"
    ; anonymous = false
    ; indexed_parameter_types = [U64.t; Address.t]
    ; non_indexed_parameter_types = [U256.t; U64.t] }
let () = check_hash claim_rewards_event "cb607e6b63c89c95f6ae24ece9fe0e38a7971aa5ed956254f1df47490921727b"
let emit_claim_rewards_event ~val_id:(Val_id.Val_id val_id) ~delegator ~amount =
  M.(
    let$ (Epoch claim_epoch) = !$Variables.epoch in
    emit_event claim_rewards_event [val_id; delegator] [amount; claim_epoch] )

let commission_changed_event =
  Abi.Event.
    { name = "CommissionChanged"
    ; anonymous = false
    ; indexed_parameter_types = [U64.t]
    ; non_indexed_parameter_types = [U256.t; U256.t] }
let () =
  check_hash commission_changed_event "d1698d3454c5b5384b70aaae33f1704af7c7e055f0c75503ba3146dc28995920"
let emit_commission_changed_event ~val_id:(Val_id.Val_id val_id) ~old_commission ~new_commission =
  M.emit_event commission_changed_event [val_id] [old_commission; new_commission]

let epoch_changed_event =
  Abi.Event.
    { name = "EpochChanged"
    ; anonymous = false
    ; indexed_parameter_types = []
    ; non_indexed_parameter_types = [U64.t; U64.t] }
let () = check_hash epoch_changed_event "4fae4dbe0ed659e8ce6637e3c273cd8e4d3bf029b9379a9e8b3f3f27dbef809b"
let emit_epoch_changed_event ~old_epoch:(Epoch.Epoch old_epoch) ~new_epoch:(Epoch.Epoch new_epoch) =
  M.emit_event epoch_changed_event [] [old_epoch; new_epoch]

let delegate_impl ~(val_id : Val_id.t) ~(stake : U256.t) ~(address : Address.t) : bool M.t =
  M.(
    let$ () =
      let$ v = !$(Variables.val_execution_opt val_id) in
      when_ (Option.is_none v) (fail Unknown_validator)
    in
    let$ () = when_ U256.(stake < dust_threshold) (fail Delegation_too_small) in

    (* Storage reads. *)
    let$ epoch = !$Variables.epoch in
    let$ in_epoch_delay_period = !$Variables.in_epoch_delay_period in
    let$ active_epoch = checked_arith (activation_epoch ~epoch ~in_epoch_delay_period) in

    let$ val_execution, delegator = pull_delegator_up_to_date (val_id, address) in

    (* Pure code. *)
    let$ delegator, need_future_accumulator =
      if in_epoch_delay_period then
        let need_future_accumulator = Epoch.(delegator.epochs.next_delta_epoch = zero) in
        let$ next_delta_stake = checked_arith U256.Checked.(delegator.next_delta_stake + stake) in
        let epochs = {delegator.epochs with next_delta_epoch = active_epoch} in
        return ({delegator with next_delta_stake; epochs}, need_future_accumulator)
      else
        let need_future_accumulator = Epoch.(delegator.epochs.delta_epoch = zero) in
        let$ delta_stake = checked_arith U256.Checked.(delegator.delta_stake + stake) in
        let epochs = {delegator.epochs with delta_epoch = active_epoch} in
        return ({delegator with delta_stake; epochs}, need_future_accumulator)
    in

    let$ future_accumulator = !$(Variables.accumulated_reward_per_token (active_epoch, val_id)) in
    let future_accumulator =
      if need_future_accumulator then
        increment_accumulator_refcount ~val_execution ~accumulator:future_accumulator
      else future_accumulator
    in

    let$ () = emit_delegation_event ~val_id ~delegator:address ~amount:stake ~active_epoch in

    let$ new_stake = checked_arith U256.Checked.(val_execution.stake + stake) in
    let val_execution = {val_execution with stake = new_stake} in

    let old_flags = val_execution.address_flags in
    let val_execution =
      let open Address_flags in
      let flags =
        old_flags
        |> (fun f ->
        if U256.(new_stake >= active_validator_stake) then f.^(flag stake_too_low) <- false else f )
        |> fun f ->
        if
          Address.(val_execution.address_flags.auth_address = address)
          && U256.(Delegator.next_epoch_stake delegator >= min_auth_address_stake)
        then f.^(flag withdrawn) <- false
        else f
      in
      {val_execution with address_flags = flags}
    in

    let$ () =
      when_
        (val_execution.address_flags.flags <> old_flags.flags)
        (emit_validator_status_changed_event ~val_id ~flags:val_execution.address_flags.flags)
    in

    (* Add to execution valset if all flags clear. *)
    let$ () =
      when_
        (val_execution.address_flags.flags = U64.zero)
        (let$ bitset = !$(Variables.val_bitset_bucket val_id) in
         let new_bitset, inserted = add_to_valset val_id bitset in
         let$ () = Variables.val_bitset_bucket val_id $= new_bitset in
         when_ inserted (lift (Storage.Array.push Variables.valset_execution val_id)) )
    in

    (* Storage writes. *)
    let$ () = Variables.val_execution val_id $= val_execution in
    let$ () = Variables.delegator (val_id, address) $= delegator in
    let$ () = Variables.accumulated_reward_per_token (active_epoch, val_id) $= future_accumulator in

    let$ () = Delegators_for_validator.insert val_id address in
    let$ () = Validators_for_delegator.insert address val_id in

    return true )

let delegate ~sender ~value Tuple.[(val_id : Val_id.t)] =
  M.(if U256.(value = zero) then return true else delegate_impl ~val_id ~stake:value ~address:sender)

let add_validator ~sender:_ ~value (input : Bytes.t) : Bytes.t M.t =
  M.(
    (* add_validator does not use standard Solidity ABI decoding. Instead, it takes its parameters as a tuple
       of dynamic byte arrays but ignores the tuple offsets and decodes each parameter directly from offsets
       calculated from their expected length. As a consequence, if the offsets in the tuple header are invalid,
       this function will still succeed. *)
    let decode_bytes_tail ~offset ~length =
      let input_length = Bytes.length input in
      let$ offset =
        let$ () = ensure (offset + U256.byte_width <= input_length) ~or_error:Input_too_short in
        let$ () = ensure U256.(~$length = of_repr (Repr.sub input offset)) ~or_error:Length_mismatch in
        return (offset + U256.byte_width)
      in
      let padded_length = Type.bytes_to_padded_bytes length in
      if offset + padded_length > Bytes.length input then fail Input_too_short
      else return (Bytes.sub input offset length, offset + padded_length)
    in
    let offset =
      (* Skip header size. *)
      B32.byte_width + B32.byte_width + B32.byte_width
    in
    (* Message layout:
       [ B33 secp_pubkey | B48 bls_pubkey | B20 auth_address | B32 signed_stake | B32 commission ] *)
    let message_size = 33 + 48 + Address.byte_width + U256.byte_width + U256.byte_width in
    let$ message, offset = decode_bytes_tail ~offset ~length:message_size in
    let$ secp_sig, offset = decode_bytes_tail ~offset ~length:64 in
    let$ bls_sig, offset = decode_bytes_tail ~offset ~length:96 in
    let$ () = when_ (offset <> Bytes.length input) (fail Invalid_input) in
    let secp_pubkey = B33.sub message 0 in
    let bls_pubkey = B48.sub message 33 in
    let auth_address = Address.sub message 81 in
    let signed_stake = U256.(of_repr (Repr.sub message 101)) in
    let commission = U256.(of_repr (Repr.sub message 133)) in

    let$ () = when_ U256.(signed_stake <> value) (fail Invalid_input) in
    let$ () = when_ U256.(value < min_auth_address_stake) (fail Insufficient_stake) in

    (* Verify SECP signature. *)
    let$ secp_pk = Option.or_fail Invalid_secp_pubkey (Crypto.Secp.pk_of_bytes secp_pubkey) in
    let$ () =
      let$ secp_sig = Option.or_fail Invalid_secp_signature (Crypto.Secp.signature_of_bytes secp_sig) in
      when_
        (not (Crypto.Secp.verify secp_pk ~msg:message ~signature:secp_sig))
        (fail Secp_signature_verification_failed)
    in
    (* Verify BLS signature. *)
    let$ bls_pk = Option.or_fail Invalid_bls_pubkey (Crypto.Bls.pk_of_bytes bls_pubkey) in
    let$ () =
      let$ bls_sig = Option.or_fail Invalid_bls_signature (Crypto.Bls.signature_of_bytes bls_sig) in
      when_
        (not (Crypto.Bls.verify bls_pk ~msg:message ~signature:bls_sig))
        (fail Bls_signature_verification_failed)
    in

    let$ () = when_ U256.(commission > max_commission) (fail Commission_too_high) in

    let secp_eth_address = Crypto.Secp.address_of_pubkey secp_pk in
    let bls_eth_address = Crypto.Bls.address_of_pubkey bls_pk in

    let$ secp_exists = !$(Variables.val_id secp_eth_address) in
    let$ bls_exists = !$(Variables.val_id_bls bls_eth_address) in
    let$ () = when_ (Option.is_some secp_exists || Option.is_some bls_exists) (fail Validator_exists) in

    let$ (Val_id last_val_id) = !$Variables.last_val_id in
    let$ val_id =
      let$ id = checked_arith U64.(Checked.(last_val_id + ~$1)) in
      return (Val_id.Val_id id)
    in

    let$ () = Variables.last_val_id $= val_id in
    let$ () = Variables.val_id secp_eth_address $= Some val_id in
    let$ () = Variables.val_id_bls bls_eth_address $= Some val_id in

    let keys = Keys.{secp_pubkey; bls_pubkey} in
    let address_flags = Address_flags.{auth_address; flags = Address_flags.stake_too_low} in
    let val_execution = {Val_execution.empty with keys; address_flags; commission} in
    let$ () = Variables.val_execution val_id $= val_execution in

    let$ () = emit_validator_created_event ~val_id ~auth_delegator:auth_address ~commission in
    let$ _ = delegate_impl ~val_id ~stake:value ~address:auth_address in

    return (enc_bytes Val_id.t val_id) )

let undelegate ~sender ~value:_ Tuple.[(val_id : Val_id.t); (amount : U256.t); (withdrawal_id : U8.t)] :
    bool M.t =
  M.(
    if U256.(amount = zero) then return true
    else
      let$ () =
        let$ v = !$(Variables.val_execution_opt val_id) in
        when_ (Option.is_none v) (fail Unknown_validator)
      in
      let$ existing = !$(Variables.withdrawal_request (val_id, sender, withdrawal_id)) in
      let$ () = when_ (Option.is_some existing) (fail Withdrawal_id_exists) in

      let$ epoch = !$Variables.epoch in
      let$ in_epoch_delay_period = !$Variables.in_epoch_delay_period in

      let$ val_execution, delegator = pull_delegator_up_to_date (val_id, sender) in

      let$ () = when_ U256.(delegator.stake < amount) (fail Insufficient_stake) in

      let$ val_stake = checked_arith U256.Checked.(val_execution.stake - amount) in
      let$ del_stake = checked_arith U256.Checked.(delegator.stake - amount) in

      (* Dust handling: absorb remainder if what's left is below threshold. *)
      let$ amount, val_stake, del_stake =
        if U256.(del_stake > zero) && U256.(del_stake < dust_threshold) then
          let$ amount = checked_arith U256.Checked.(amount + del_stake) in
          let$ val_stake = checked_arith U256.Checked.(val_stake - del_stake) in
          return (amount, val_stake, U256.zero)
        else return (amount, val_stake, del_stake)
      in

      let$ withdrawal_epoch = checked_arith (activation_epoch ~epoch ~in_epoch_delay_period) in

      let old_flags = val_execution.address_flags in
      let val_execution =
        let next_epoch_stake = Delegator.next_epoch_stake {delegator with stake = del_stake} in
        let flags =
          let open Address_flags in
          old_flags
          |> (fun f ->
          if
            Address.(val_execution.address_flags.auth_address = sender)
            && U256.(next_epoch_stake < min_auth_address_stake)
          then f.^(flag withdrawn) <- true
          else f )
          |> fun f -> if U256.(val_stake < active_validator_stake) then f.^(flag stake_too_low) <- true else f
        in
        {val_execution with stake = val_stake; address_flags = flags}
      in

      let$ () =
        when_
          (val_execution.address_flags.flags <> old_flags.flags)
          (emit_validator_status_changed_event ~val_id ~flags:val_execution.address_flags.flags)
      in

      let$ () =
        emit_undelegate_event ~val_id ~delegator:sender ~withdrawal_id ~amount
          ~activation_epoch:withdrawal_epoch
      in

      let$ () =
        let acc = delegator.rewards_per_token in
        let wr = Withdrawal_request.{amount; acc; epoch = withdrawal_epoch} in
        Variables.withdrawal_request (val_id, sender, withdrawal_id) $= Some wr
      in

      (* Increment accumulator refcount for the new withdrawal. *)
      let$ () =
        let$ acc = !$(Variables.accumulated_reward_per_token (withdrawal_epoch, val_id)) in
        let acc = increment_accumulator_refcount ~val_execution ~accumulator:acc in
        Variables.accumulated_reward_per_token (withdrawal_epoch, val_id) $= acc
      in

      let delegator =
        let rewards_per_token = if U256.(del_stake = zero) then U256.zero else delegator.rewards_per_token in
        {delegator with stake = del_stake; rewards_per_token}
      in

      let$ () = Variables.val_execution val_id $= val_execution in
      let$ () = Variables.delegator (val_id, sender) $= delegator in

      let$ () =
        let need_removal = U256.(Delegator.next_epoch_stake delegator = zero) in
        when_ need_removal
          (let$ () = Delegators_for_validator.remove val_id sender in
           Validators_for_delegator.remove sender val_id )
      in

      return true )

let withdraw ~sender ~value:_ Tuple.[(val_id : Val_id.t); (withdrawal_id : U8.t)] : bool M.t =
  M.(
    let$ wr_opt = !$(Variables.withdrawal_request (val_id, sender, withdrawal_id)) in
    let$ wr = Option.or_fail Unknown_withdrawal_id wr_opt in
    let$ () = Variables.withdrawal_request (val_id, sender, withdrawal_id) $= None in

    let$ epoch = !$Variables.epoch in
    let$ ready =
      let$ epoch_after_wr = checked_arith Epoch.(wr.epoch + withdrawal_delay) in
      return (is_epoch_active ~epoch epoch_after_wr)
    in
    let$ () = when_ (not ready) (fail Withdrawal_not_ready) in

    let$ wr_accumulator = !$(Variables.accumulated_reward_per_token (wr.epoch, val_id)) in
    let wr_accumulator, epoch_acc = decrement_accumulator_refcount ~accumulator:wr_accumulator in
    let$ () = Variables.accumulated_reward_per_token (wr.epoch, val_id) $= wr_accumulator in

    let$ rewards =
      checked_arith (calculate_rewards ~stake:wr.amount ~current_acc:epoch_acc ~last_checked_acc:wr.acc)
    in

    let$ val_execution = !$(Variables.val_execution val_id) in
    let$ val_execution = or_fail (reward_invariant ~validator:val_execution ~rewards) in
    let$ () = Variables.val_execution val_id $= val_execution in

    let$ total = checked_arith U256.Checked.(wr.amount + rewards) in
    let$ () = send_tokens ~to_:sender ~amount:total in
    let$ () = emit_withdraw_event ~val_id ~delegator:sender ~withdrawal_id ~amount:total in

    return true )

let compound ~sender ~value:_ Tuple.[(val_id : Val_id.t)] : bool M.t =
  M.(
    let$ val_execution, delegator = pull_delegator_up_to_date (val_id, sender) in

    let rewards = delegator.rewards in
    let delegator = {delegator with rewards = U256.zero} in

    let$ () = Variables.val_execution val_id $= val_execution in
    let$ () = Variables.delegator (val_id, sender) $= delegator in

    let$ () =
      when_
        U256.(rewards > zero)
        (let$ () = emit_claim_rewards_event ~val_id ~delegator:sender ~amount:rewards in
         delegate_impl ~val_id ~stake:rewards ~address:sender >>= fun _ -> return () )
    in

    return true )

let claim_rewards ~sender ~value:_ Tuple.[(val_id : Val_id.t)] : bool M.t =
  M.(
    let$ val_execution, delegator = pull_delegator_up_to_date (val_id, sender) in

    let rewards = delegator.rewards in
    let delegator = {delegator with rewards = U256.zero} in

    let$ () =
      when_
        U256.(rewards > zero)
        (let$ () = send_tokens ~to_:sender ~amount:rewards in
         emit_claim_rewards_event ~val_id ~delegator:sender ~amount:rewards )
    in

    let$ () = Variables.val_execution val_id $= val_execution in
    let$ () = Variables.delegator (val_id, sender) $= delegator in

    return true )

let change_commission ~sender ~value:_ Tuple.[(val_id : Val_id.t); (new_commission : U256.t)] : bool M.t =
  M.(
    let$ val_execution = !$(Variables.val_execution_opt val_id) >>= Option.or_fail Unknown_validator in

    let$ () =
      when_ (not Address.(val_execution.address_flags.auth_address = sender)) (fail Requires_auth_address)
    in

    let$ () = when_ U256.(new_commission > max_commission) (fail Commission_too_high) in

    let old_commission = val_execution.commission in
    let$ () =
      when_
        U256.(old_commission <> new_commission)
        (let val_execution = {val_execution with commission = new_commission} in
         let$ () = Variables.val_execution val_id $= val_execution in
         emit_commission_changed_event ~val_id ~old_commission ~new_commission )
    in

    return true )

let external_reward ~sender ~value Tuple.[(val_id : Val_id.t)] : bool M.t =
  M.(
    let reward = value in
    let$ val_execution = !$(Variables.val_execution_opt val_id) >>= Option.or_fail Unknown_validator in

    let$ epoch_view = get_this_epoch_view val_id in
    let active_stake = epoch_view.stake in
    let$ () = when_ U256.(active_stake = zero) (fail Not_in_validator_set) in

    let$ () = when_ U256.(reward < min_external_reward) (fail External_reward_too_small) in
    let$ () = when_ U256.(reward > max_external_reward) (fail External_reward_too_large) in

    let$ val_execution = checked_arith (apply_reward ~val_execution ~new_rewards:reward ~active_stake) in
    let$ () = Variables.val_execution val_id $= val_execution in
    let$ () = emit_validator_rewarded_event ~val_id ~from:sender ~amount:reward in

    return true )

let get_validator ~sender:_ ~value:_ Tuple.[(val_id : Val_id.t)] =
  M.(
    let$ val_execution = !$(Variables.val_execution val_id) in
    let$ consensus = !$(Variables.consensus_view val_id) in
    let$ snapshot = !$(Variables.snapshot_view val_id) in
    return
      Tuple.
        [ val_execution.address_flags.auth_address
        ; val_execution.address_flags.flags
        ; val_execution.stake
        ; val_execution.rewards_per_token
        ; val_execution.commission
        ; val_execution.unclaimed_rewards
        ; consensus.stake
        ; consensus.commission
        ; snapshot.stake
        ; snapshot.commission
        ; B33.to_bytes val_execution.keys.secp_pubkey
        ; B48.to_bytes val_execution.keys.bls_pubkey ] )

let get_delegator ~sender:_ ~value:_ Tuple.[(val_id : Val_id.t); (address : Address.t)] =
  M.(
    let$ val_execution, delegator = pull_delegator_up_to_date (val_id, address) in

    let$ () = Variables.val_execution val_id $= val_execution in
    let$ () = Variables.delegator (val_id, address) $= delegator in

    return
      Tuple.
        [ delegator.stake
        ; delegator.rewards_per_token
        ; delegator.rewards
        ; delegator.delta_stake
        ; delegator.next_delta_stake
        ; delegator.epochs.delta_epoch
        ; delegator.epochs.next_delta_epoch ] )

let get_withdrawal_request
    ~sender:_ ~value:_ Tuple.[(val_id : Val_id.t); (address : Address.t); (withdrawal_id : U8.t)] =
  M.(
    let$ wr_opt = !$(Variables.withdrawal_request (val_id, address, withdrawal_id)) in
    let wr = Option.value wr_opt ~default:Withdrawal_request.empty in
    return Tuple.[wr.amount; wr.acc; wr.epoch] )

let get_valset (arr : 'a Storage.Array.t) ~sender:_ ~value:_ Tuple.[(start_index : U32.t)] =
  M.(
    let$ arr_len = !$(arr.length) in

    (* Both consensus set and snapshot set are bounded. The execution set is  theoretically unbounded, but
       to be a candidate, you need to put limits::min_auth_address_stake(). This amount prevents that valset
       from exceeding u32_max in practice. *)
    let$ () = ensure Uint.(U64.to_uint arr_len <= U32.(to_uint max_t)) ~or_error:Internal_error in
    let$ start_index =
      match U64.(of_uint_opt (U32.to_uint start_index)) with
      | Some i -> return i
      | None -> fail Internal_error
    in
    let end_index = U64.(min arr_len (start_index + ~$array_pagination)) in
    let done_ = U64.(arr_len <= start_index + ~$array_pagination) in
    let$ page, index =
      let rec loop (i : U64.t) =
        if U64.(i >= end_index) then return (List.[], i)
        else
          let$ elt = !$Storage.Array.(arr.$(i)) in
          let$ elts, index = loop U64.(i + one) in
          return (List.(elt :: elts), index)
      in
      loop start_index
    in
    let$ next_index =
      match U32.of_uint_opt (U64.to_uint index) with Some i -> return i | None -> fail Internal_error
    in
    return Tuple.[done_; next_index; page] )

let get_delegations ~sender:_ ~value:_ Tuple.[(address : Address.t); (start_val_id : Val_id.t)] =
  M.(
    let$ done_, next, items = Validators_for_delegator.traverse address start_val_id linked_list_pagination in
    return Tuple.[done_; next; items] )

let get_delegators ~sender:_ ~value:_ Tuple.[(val_id : Val_id.t); (start_delegator : Address.t)] =
  M.(
    let$ done_, next, items =
      Delegators_for_validator.traverse val_id start_delegator linked_list_pagination
    in
    return Tuple.[done_; next; items] )

let get_epoch ~sender:_ ~value:_ (_input : Bytes.t) =
  (* get_epoch explicitly ignores any input and does not fail on trailing bytes. *)
  M.(
    let$ epoch = !$Variables.epoch in
    let$ in_epoch_delay_period = !$Variables.in_epoch_delay_period in
    return (enc_bytes (Tuple [Epoch.t; bool]) Tuple.[epoch; in_epoch_delay_period]) )

let get_proposer ~sender:_ ~value:_ (_input : Bytes.t) =
  (* get_proposer explicitly ignores any input and does not fail on trailing bytes. *)
  M.(
    let$ proposer_val_id = !$Variables.proposer_val_id in
    return (enc_bytes Val_id.t proposer_val_id) )

module Function = Contract.Function

let check_signature (fn : (_, _) Function.impl) hash = assert (fn.signature.selector = B4.of_hex_string hash)

let add_validator_function =
  Function.make_raw "addValidator" ~payable:true ~input:[Bytes; Bytes; Bytes] ~output:Val_id.t
    ~gas_cost:(Gas.of_int 505125) add_validator
let () = check_signature add_validator_function "f145204c"

let delegate_function =
  Function.make "delegate" ~payable:true ~input:[Val_id.t] ~output:bool ~gas_cost:Gas.(of_int 260850) delegate
let () = check_signature delegate_function "84994fec"

let undelegate_function =
  Function.make "undelegate" ~input:[Val_id.t; U256.t; U8.t] ~output:bool
    ~gas_cost:Gas.(of_int 147750)
    undelegate
let () = check_signature undelegate_function "5cf41514"

let compound_function =
  Function.make "compound" ~input:[Val_id.t] ~output:bool ~gas_cost:Gas.(of_int 289325) compound
let () = check_signature compound_function "b34fea67"

let withdraw_function =
  Function.make "withdraw" ~input:[Val_id.t; U8.t] ~output:bool ~gas_cost:Gas.(of_int 68675) withdraw
let () = check_signature withdraw_function "aed2ee73"

let claim_rewards_function =
  Function.make "claimRewards" ~input:[Val_id.t] ~output:bool ~gas_cost:Gas.(of_int 155375) claim_rewards
let () = check_signature claim_rewards_function "a76e2ca5"

let change_commission_function =
  Function.make "changeCommission" ~input:[Val_id.t; U256.t] ~output:bool
    ~gas_cost:Gas.(of_int 39475)
    change_commission
let () = check_signature change_commission_function "9bdcc3c8"

let external_reward_function =
  Function.make "externalReward" ~payable:true ~input:[Val_id.t] ~output:bool
    ~gas_cost:Gas.(of_int 66575)
    external_reward
let () = check_signature external_reward_function "e4b3303b"

let get_epoch_function =
  (* get_epoch is a raw function because it will ignore trailing input bytes. *)
  Function.make_raw "getEpoch" ~input:[] ~output:(Tuple [Epoch.t; bool]) ~gas_cost:Gas.(of_int 200) get_epoch
let () = check_signature get_epoch_function "757991a8"

let get_proposer_val_id_function =
  (* get_proposer_val_id is a raw function because it will ignore trailing input bytes. *)
  Function.make_raw "getProposerValId" ~input:[] ~output:Val_id.t ~gas_cost:Gas.(of_int 100) get_proposer
let () = check_signature get_proposer_val_id_function "fbacb0be"

let get_validator_function =
  Function.make "getValidator" ~input:[Val_id.t]
    ~output:
      (Tuple [Address.t; U64.t; U256.t; U256.t; U256.t; U256.t; U256.t; U256.t; U256.t; U256.t; Bytes; Bytes])
    ~gas_cost:Gas.(of_int 97200)
    get_validator
let () = check_signature get_validator_function "2b6d639a"

let get_delegator_function =
  Function.make "getDelegator" ~input:[Val_id.t; Address.t]
    ~output:(Tuple [U256.t; U256.t; U256.t; U256.t; U256.t; Epoch.t; Epoch.t])
    ~gas_cost:Gas.(of_int 184900)
    get_delegator
let () = check_signature get_delegator_function "573c1ce0"

let get_withdrawal_request_function =
  Function.make "getWithdrawalRequest" ~input:[Val_id.t; Address.t; U8.t]
    ~output:(Tuple [U256.t; U256.t; Epoch.t])
    ~gas_cost:Gas.(of_int 24300)
    get_withdrawal_request
let () = check_signature get_withdrawal_request_function "56fa2045"

let get_consensus_validator_set_function =
  Function.make "getConsensusValidatorSet" ~input:[U32.t]
    ~output:(Tuple [bool; U32.t; Array Val_id.t])
    ~gas_cost:Gas.(of_int 814000)
    (get_valset Variables.valset_consensus)
let () = check_signature get_consensus_validator_set_function "fb29b729"

let get_snapshot_validator_set_function =
  Function.make "getSnapshotValidatorSet" ~input:[U32.t]
    ~output:(Tuple [bool; U32.t; Array Val_id.t])
    ~gas_cost:Gas.(of_int 814000)
    (get_valset Variables.valset_snapshot)
let () = check_signature get_snapshot_validator_set_function "de66a368"

let get_execution_validator_set_function =
  Function.make "getExecutionValidatorSet" ~input:[U32.t]
    ~output:(Tuple [bool; U32.t; Array Val_id.t])
    ~gas_cost:Gas.(of_int 814000)
    (get_valset Variables.valset_execution)
let () = check_signature get_execution_validator_set_function "7cb074df"

let get_delegations_function =
  Function.make "getDelegations" ~input:[Address.t; Val_id.t]
    ~output:(Tuple [bool; Val_id.t; Array Val_id.t])
    ~gas_cost:Gas.(of_int 814000)
    get_delegations
let () = check_signature get_delegations_function "4fd66050"

let get_delegators_function =
  Function.make "getDelegators" ~input:[Val_id.t; Address.t]
    ~output:(Tuple [bool; Address.t; Array Address.t])
    ~gas_cost:Gas.(of_int 814000)
    get_delegators
let () = check_signature get_delegators_function "a0843a26"

let fallback_function =
  Function.make "fallback" ~payable:true ~input:[] ~output:unit
    ~gas_cost:Gas.(of_int 40_000)
    (fun ~sender:_ ~value:_ [] -> M.fail Method_not_supported)

let staking_contract =
  let contract =
    Contract.make ~fallback:(Pack fallback_function)
      [ Pack add_validator_function
      ; Pack delegate_function
      ; Pack undelegate_function
      ; Pack compound_function
      ; Pack withdraw_function
      ; Pack claim_rewards_function
      ; Pack change_commission_function
      ; Pack external_reward_function
      ; Pack get_epoch_function
      ; Pack get_proposer_val_id_function
      ; Pack get_validator_function
      ; Pack get_delegator_function
      ; Pack get_withdrawal_request_function
      ; Pack get_consensus_validator_set_function
      ; Pack get_snapshot_validator_set_function
      ; Pack get_execution_validator_set_function
      ; Pack get_delegations_function
      ; Pack get_delegators_function ]
  in
  fun (msg : Evmc.Message.t) ->
    let invoked_via_call = msg.kind = Call && (not msg.static) && not msg.delegated in
    (* TODO: Monad precompiles can only be invoked via a Call instruction. This should be factored out
       once MIP-4 and the staking precompile are both merged. *)
    if not invoked_via_call then TransactionState.M.return Evmc.Result.(failure Rejected)
    else Contract.dispatch contract msg

(* System calls. *)

let clear_valset (val_ids : Val_id.t Storage.Array.t) (validators : (Val_id.t, 'a) Storage.Mapping.t) =
  M.(
    let$ () =
      lift (Storage.Array.iteriM val_ids ~f:(fun _ val_id -> Storage.Loc.clear (validators val_id)))
    in
    lift (Storage.Array.clear val_ids) )

let syscall_snapshot ~sender:_ ~value:_ Tuple.[] =
  M.(
    let$ in_epoch_delay_period = !$Variables.in_epoch_delay_period in
    let$ () = when_ in_epoch_delay_period (fail Snapshot_in_boundary) in

    (* 1. Throw out last epoch's snapshot view. *)
    let$ () = clear_valset Variables.valset_snapshot Variables.snapshot_view in

    (* 2. Copy the consensus view to the snapshot view. *)
    let$ () =
      let$ consensus = lift (Storage.Array.read_to_list Variables.valset_consensus) in
      let$ () = lift (Storage.Array.write_of_list Variables.valset_snapshot consensus) in
      List.iterM consensus ~f:(fun val_id ->
          let$ cv = !$(Variables.consensus_view val_id) in
          Variables.snapshot_view val_id $= {Snapshot_view.stake = cv.stake; commission = cv.commission} )
    in

    (* 3. Throw out the consensus view. *)
    let$ () = clear_valset Variables.valset_consensus Variables.consensus_view in

    (* 4. Find all the candidates in the execution set and load into memory for
       sorting. The only validators selected have OK status. Validators with
       nonzero status are queued up for removal. *)
    let$ candidates, removals =
      let$ len = !$(Variables.valset_execution.length) in
      let rec loop i candidates removals =
        (* Collect candidates to be sorted, and collect removal indices to be erased. These lists are
           constructed in reverse order, which does not matter since candidates is about to be sorted and
           removals will be consumed in reverse order anyways. *)
        if U64.(i >= len) then return (candidates, removals)
        else
          let$ val_id = !$Storage.Array.(Variables.valset_execution.$(i)) in
          let$ val_execution = !$(Variables.val_execution val_id) in
          if val_execution.address_flags.flags = Address_flags.ok then
            loop U64.(i + one) List.((val_id, val_execution) :: candidates) removals
          else loop U64.(i + one) candidates List.(i :: removals)
      in
      loop U64.zero [] []
    in

    (* 5. Construct consensus set from top validators. *)
    let$ () =
      let sorted =
        List.sort
          (fun (id_1, val_1) (id_2, val_2) ->
            (* Sort by stake descending, then by val_id ascending. *)
            let open Val_execution in
            let c = U256.compare val_2.stake val_1.stake in
            if c <> 0 then c else Val_id.compare id_1 id_2 )
          candidates
      in
      let n = min (List.length sorted) active_valset_size in
      let top_n = List.take n sorted in
      List.iterM
        ~f:(fun (val_id, Val_execution.{stake; commission; _}) ->
          let$ () = lift (Storage.Array.push Variables.valset_consensus val_id) in
          Variables.consensus_view val_id $= Consensus_view.{stake; commission} )
        top_n
    in

    (* 6. Process removals from the execution set to prevent state bloat.
       Pop-and-swap from the array, highest indices first (matching the C++ implementation) *)
    let$ () =
      List.iterM
        ~f:(fun i ->
          let slot_to_replace = Storage.Array.(Variables.valset_execution.$(i)) in
          let$ id_to_remove = !$slot_to_replace in
          let$ bitset = !$(Variables.val_bitset_bucket id_to_remove) in
          let$ () = Variables.val_bitset_bucket id_to_remove $= remove_from_valset id_to_remove bitset in
          let$ swapped_id = lift (Storage.Array.pop Variables.valset_execution) in
          slot_to_replace $= swapped_id )
        removals (* removals was constructed in reverse, so there is no need to reverse it again. *)
    in

    Variables.in_epoch_delay_period $= true )
let syscall_snapshot_function =
  Function.make "syscallSnapshot" ~input:[] ~output:unit ~gas_cost:Gas.zero syscall_snapshot
let () = check_signature syscall_snapshot_function "157eeb21"

let syscall_on_epoch_change ~sender:_ ~value:_ Tuple.[(next_epoch : Epoch.t)] =
  M.(
    let$ next_next_epoch = checked_arith Epoch.(next_epoch + 1) in
    let$ last_epoch = !$Variables.epoch in
    let$ () = when_ Epoch.(next_epoch <= last_epoch) (fail Invalid_epoch_change) in

    let$ () = emit_epoch_changed_event ~old_epoch:last_epoch ~new_epoch:next_epoch in

    (* For each validator in the snapshot valset, add validator.rewards_per_token to each of the nonempty
       accumulators for the next two epochs. *)
    let$ valset = lift (Storage.Array.read_to_list Variables.valset_snapshot) in
    let$ () =
      List.iterM
        ~f:(fun val_id ->
          let$ validator = !$(Variables.val_execution val_id) in

          let$ () =
            update_field
              (Storage.Loc.lens (Variables.accumulated_reward_per_token (next_epoch, val_id)))
              (fun acc ->
                if acc <> Ref_counted_accumulator.empty then {acc with value = validator.rewards_per_token}
                else acc )
          in

          let$ () =
            update_field
              (Storage.Loc.lens (Variables.accumulated_reward_per_token (next_next_epoch, val_id)))
              (fun acc ->
                if acc <> Ref_counted_accumulator.empty then {acc with value = validator.rewards_per_token}
                else acc )
          in
          return () )
        valset
    in

    let$ () = Variables.in_epoch_delay_period $= false in
    Variables.epoch $= next_epoch )
let syscall_on_epoch_change_function =
  Function.make "syscallOnEpochChange" ~input:[Epoch.t] ~output:unit ~gas_cost:Gas.zero
    syscall_on_epoch_change
let () = check_signature syscall_on_epoch_change_function "1d4e9f02"

let syscall_reward ~sender:_ ~value Tuple.[(block_author : Address.t)] =
  M.(
    let raw_reward = value in

    (* 1. Get validator information. *)
    let$ val_id = !$(Variables.val_id block_author) >>= Option.or_fail Not_in_validator_set in

    (* 2. Validator must be active. *)
    let$ epoch_view = get_this_epoch_view val_id in
    let active_stake = epoch_view.stake in
    let$ () = when_ U256.(active_stake = zero) (fail Not_in_validator_set) in

    let$ () = update_field (TransactionState.balance staking_address) (fun b -> U256.(b + raw_reward)) in

    (* 3. Subtract commission. *)
    let commission_rate = epoch_view.commission in
    let$ commission =
      checked_arith
        Result.(
          let open U256.Checked in
          let$ product = raw_reward * commission_rate in
          product / mon )
    in

    (* 4. Send commission to the auth address. *)
    let$ val_execution = !$(Variables.val_execution val_id) in
    let auth_address = val_execution.address_flags.auth_address in
    let$ auth_del = !$(Variables.delegator (val_id, auth_address)) in
    let$ auth_rewards = checked_arith U256.Checked.(auth_del.rewards + commission) in
    let$ () = Variables.delegator (val_id, auth_address) $= {auth_del with rewards = auth_rewards} in

    let$ del_reward = checked_arith U256.Checked.(raw_reward - commission) in
    (* 5. Update accumulator and unclaimed rewards for this validator pool. *)
    let$ val_execution = checked_arith (apply_reward ~val_execution ~new_rewards:del_reward ~active_stake) in
    let$ () = Variables.val_execution val_id $= val_execution in
    let$ () = emit_validator_rewarded_event ~val_id ~from:Chain.Monad.system_sender ~amount:del_reward in

    (* 6. Store the proposer validator id for other contracts to query. *)
    Variables.proposer_val_id $= val_id )
let syscall_reward_function =
  Function.make "syscallReward" ~payable:true ~input:[Address.t] ~output:unit ~gas_cost:Gas.zero
    syscall_reward
let () = check_signature syscall_reward_function "791bdcf3"

let staking_syscalls =
  let contract =
    Contract.make ~fallback:(Pack fallback_function)
      [Pack syscall_reward_function; Pack syscall_snapshot_function; Pack syscall_on_epoch_change_function]
  in
  Contract.dispatch contract
