(** EVMC-style host implementation. This module provides a restricted API for the VM to interact with the
    state of the blockchain, including accessing storage and sending messages. *)

open Numeric
open Byte_string
open Chain.Ethereum
open Lens.Infix
open State

(** The division of responsibilities introduced by the EVMC API makes it so that Host and VM modules depend
    on each other, as a host needs access to a VM to implement the {!Evmc.HOST.call} method and a VM needs
    access to a host to interact with the blockchain. This mutual recursion is handled here by the
    {!Instantiate} functor below.
    In addition to the functions required by the {!Evmc.HOST} interface, this module also exposes
    [call_from_eoa] which executes a call or create caused by a user-sent transaction (as opposed to
    a CALL or CREATE opcode in a smart contract). *)
module Make (ChainParams : Chain.Monad.PARAMS) (Vm : Evmc.Vm(TransactionState).SIG) = struct
  open Account.TLens
  open WorldState
  include TransactionState
  open M

  let transfer_ether sender recipient amount =
    let$ sender_balance = !(account sender |-- balance) in
    if U256.(sender_balance >= amount) then
      let$ () = account sender |-- balance := U256.(sender_balance - amount) in
      let$ () = update_field (account recipient |-- balance) (fun eth -> U256.(eth + amount)) in
      return true
    else return false

  (** {!Evmc.HOST.account_exists} *)
  let account_exists addr = Option.is_some <$> !(world_state |-- accounts |-- Accounts.at addr)

  (** {!Evmc.HOST.get_storage} *)
  let get_storage addr key =
    !(account addr |-- Account.storage |-- Storage.at key |-- Option.get_or_default B32.zeros)

  (** {!Evmc.HOST.set_storage} *)
  let set_storage addr key v =
    let$ o =
      !( initial_world_state
       |-- WorldState.account addr
       |-- storage
       |-- Storage.at key
       |-- Option.get_or_default B32.zeros )
    in
    let$ c = !(account addr |-- storage |-- Storage.at key |-- Option.get_or_default B32.zeros) in
    (* In practice there is no way to modify the storage of an account with zero nonce, so there is no
       need to keep empty accounts here. However, for the purpose of unit tests, it is useful to allow storage
       operations to work on empty accounts without clearing them up automatically. *)
    let$ () =
      account ~keep_empty:true addr |-- storage |-- Storage.at key := if B32.(v = zeros) then None else Some v
    in
    let zero u = B32.(u = zeros) in
    let x u = B32.(u <> zeros && u = o) in
    let y u = B32.(u <> zeros && u <> o && u = c) in
    let z u = B32.(u <> zeros && u <> o && u <> c && u = v) in
    let open Evmc.StorageStatus in
    return
      ( match () with
      | () when zero o && zero c && z v -> Added
      | () when x o && x c && zero v -> Deleted
      | () when x o && x c && z v -> Modified
      | () when x o && zero c && z v -> DeletedAdded
      | () when x o && y c && zero v -> ModifiedDeleted
      | () when x o && zero c && x v -> DeletedRestored
      | () when zero o && y c && zero v -> AddedDeleted
      | () when x o && y c && x v -> ModifiedRestored
      | () -> Assigned )

  (** {!Evmc.HOST.get_balance} *)
  let get_balance addr = !(account addr |-- balance)

  (** {!Evmc.HOST.get_code_size} *)
  let get_code_size addr =
    let$ code = !(account addr |-- code) in
    return (Uint64.of_int (Bytes.length code))

  (** {!Evmc.HOST.get_code_hash} *)
  let get_code_hash addr =
    let$ account = !(account addr) in
    return (if Account.is_empty account then None else Some (Crypto.keccak_256 account.code))

  (** {!Evmc.HOST.copy_code} *)
  let copy_code addr ~offset ~size =
    let$ code = !(account addr |-- code) in
    return (Bytes.sub_with_zero_padding code offset size)

  (** {!Evmc.HOST.selfdestruct} *)
  let selfdestruct ~address ~beneficiary =
    let$ account_balance = !(account address |-- balance) in
    let$ transfer_ok = transfer_ether address beneficiary account_balance in
    assert transfer_ok ;

    let$ created_in_current_tx = Address.Set.mem address <$> !accounts_created_in_current_transaction in
    if created_in_current_tx then
      (* Defer deletion to end of transaction as per EIP-6780. *)
      let$ alive_before_selfdestruct = account_exists address in
      let$ () = update_field self_destruct (Address.Set.add address) in
      (* Set selfdestructing account's balance to zero. This is a noop unless address=beneficiary. *)
      let$ () = account address |-- balance := U256.zero in
      return alive_before_selfdestruct
    else return false

  let should_transfer (msg : Evmc.Message.t) =
    match msg.kind with Call | CallCode | Create | Create2 -> not msg.static | DelegateCall -> false

  let increment_nonce (addr : Address.t) =
    update_field
      (account addr |-- nonce)
      (fun nonce ->
        assert (U64.(nonce < max_t)) ;
        U64.(nonce + one) )

  let precompiles = Precompiles.precompiles ChainParams.revision

  (* YP (140) *)
  let try_precompile (address : Address.t) (msg : Evmc.Message.t) ~otherwise =
    match Address.Map.find_opt address precompiles with
    | Some precompile when not msg.delegated -> return (precompile msg)
    | Some _ ->
        (* Delegated calls to precompiles are executed as if the corresponding contract was empty,
           as per EIP-7702. *)
        Vm.execute msg Bytes.empty
    | None -> otherwise

  let touch_account addr = M.update_field accessed_addresses (Address.Set.add addr)

  let touch_storage addr key =
    M.(
      let$ () = touch_account addr in
      update_field accessed_keys (StorageKey.Set.add (addr, key)) )

  (* YP (119) *)
  let process_call (from_tx : Transaction.t option) (msg : Evmc.Message.t) =
    assert (msg.kind = Call || msg.kind = CallCode || msg.kind = DelegateCall) ;
    let$ transfer_ok =
      (* YP (120), YP (121), YP (122), YP (123), YP (124), YP (125), YP (126) *)
      if should_transfer msg then transfer_ether msg.sender msg.recipient msg.value else return true
    in
    if transfer_ok then
      (* YP (131) *)
      try_precompile msg.code_address msg
        ~otherwise:
          (let$ code =
             (* YP (141) does not apply here as the state stores account code directly. *)
             let$ account_code = !(account msg.code_address |-- code) in
             match (from_tx, Delegation.get_delegated_address account_code) with
             | Some _, Some delegated_addr -> !(account delegated_addr |-- code)
             | _ -> return account_code
           in
           (* YP (140), fallthrough case. *)
           Vm.execute msg code )
    else return Evmc.Result.(failure StatusCode.Insufficient_balance)

  let contract_creation_address (msg : Evmc.Message.t) =
    let$ sender_nonce = !(account msg.sender |-- nonce) in
    (* YP (94), subsuming YP (92). *)
    let create2 : Address.create2_params option =
      if msg.kind = Create2 then Some Address.{salt = msg.create2_salt; initcode = msg.input_data} else None
    in
    return (Address.of_contract_creation ~sender:msg.sender ~nonce:sender_nonce ~create2)

  (* YP (93) *)
  let process_create (msg : Evmc.Message.t) =
    let$ create_address = contract_creation_address msg in
    let$ pre_existent_account = !(account create_address) in
    if U64.(pre_existent_account.nonce <> zero) || pre_existent_account.code <> Bytes.empty then
      (* EIP-684, covers YP (118) disjunct 1 *)
      return (Evmc.Result.failure Contract_validation_failure)
    else
      let$ () =
        update_field accounts_created_in_current_transaction (fun addresses ->
            Address.Set.add create_address addresses )
      in
      (* YP (98): σ* is σ except for the two accounts mutated below. *)
      (* YP (99), σ*[a]ₙ and σ*[a]ₛ. The code field of σ*[a] is known to be empty by this point. *)
      let$ () = account create_address |-- storage := Storage.empty in
      let$ () = account create_address |-- nonce := U64.one in
      (* σ*[a]_b as per YP (99), and σ*[s]_b as per YP (100), YP (101). YP (102) v' is implicitly calculated
         by transfer_ether. *)
      let$ transfer_ok = transfer_ether msg.sender create_address msg.value in

      let$ result =
        if transfer_ok then
          let creation_msg =
            Evmc.Message.
              { msg with
                kind = Call
              ; recipient = create_address
              ; input_data = Bytes.empty
              ; create2_salt = B32.zeros
              ; code_address = create_address }
          in
          (* YP (103) *)
          Vm.execute creation_msg msg.input_data
        else return Evmc.Result.(failure StatusCode.Insufficient_balance)
      in

      match result.status_code with
      | Success -> (
          let contract_code = result.output_data in
          let contract_length = Bytes.length contract_code in
          (* YP (113) *)
          let contract_code_gas = Gas.(of_int contract_length * code_deposit_per_byte) in
          (* YP (118), disjuncts 3, 4, 5 *)
          let failure : Evmc.Result.StatusCode.t option =
            if contract_length > 0 && contract_code.[0] = '\xef' then Some Contract_validation_failure
            else if contract_length > Chain.Monad.Constants.max_code_size then
              Some Contract_validation_failure
            else if Gas.(of_uint64 result.gas_left < contract_code_gas) then Some Out_of_gas
            else None
          in
          match failure with
          | Some error -> return (Evmc.Result.failure error)
          | None ->
              (* YP (114), success case. The failure case is covered by Evmc.Result.failure *)
              let gas_left = Gas.(to_uint64 (of_uint64 result.gas_left - contract_code_gas)) in
              (* YP (115), success case. The failure case is covered by the caller. *)
              let$ () = account create_address |-- code := contract_code in
              return {result with create_address; gas_left} )
      | _ ->
          (* YP (118), disjunct 2 *)
          return result

  let call_impl ~(from_tx : Transaction.t option) (msg : Evmc.Message.t) =
    let$ () =
      (* Increment the nonce for non-EOA CREATE/CREATE2 messages . If the message came from an EOA transaction,
         the nonce was already incremented in the irrevocable change. *)
      when_ ((msg.kind = Create || msg.kind = Create2) && Option.is_none from_tx) (increment_nonce msg.sender)
    in
    let$ () =
      match msg.kind with
      | Create | Create2 ->
          let$ create_address = contract_creation_address msg in
          (* YP (97): Touching the address must occur before the initial
             state snapshot below because a failed CREATE/CREATE2
             retains the create address in accessed_addresses, so it
             remains warm for the caller (see EIP-2929 for this specific
             clarification). *)
          touch_account create_address
      | Call | CallCode | DelegateCall -> return ()
    in
    let$ initial_state = get in
    let$ result =
      match msg.kind with
      | Call | DelegateCall | CallCode -> process_call from_tx msg
      | Create | Create2 -> process_create msg
    in
    let$ result =
      match from_tx with
      | None -> return result
      | Some t ->
          (* Check reserve balance condition. Monad §6 Algorithm 2. *)
          let chain_id = ChainParams.chain_id in
          let current_block = initial_state.current_block in
          let delegated_in_state =
            Delegation.is_valid_delegation initial_state.^(TransactionState.account msg.sender).code
          in
          (* Check whether transaction is emptying. Monad §6 Algorithm 4 (IsEmptying).
             The check of [delegated_in_state] is exactly as in the spec. The comparison with the next emptying
             transaction counter subsumes both [auth_condition] and [prior_sender_condition]. Note that
             authority processing bumps the next emptying transaction block counter before the transaction is
             processed, but the transaction itself only bumps its sender's counter after it finishes.
           *)
          let is_emptying =
            (not delegated_in_state)
            && Uint.(
                 initial_state.world_state.^(WorldState.next_emptying_transaction_block_for msg.sender)
                 <= current_block.header.number )
          in
          let base_fee_per_gas = current_block.header.base_fee_per_gas in
          let original_balances = initial_state.initial_world_state.accounts in
          let$ new_state = !(world_state |-- accounts) in
          let reserve_dipped =
            Reserve_balance.dipped_into_reserve ~chain_id ~base_fee_per_gas ~original_balances ~new_state ~t
              ~is_emptying
          in
          return (if reserve_dipped then {result with status_code = Revert; gas_refund = 0L} else result)
    in
    (* YP (115), YP (116), failure cases. YP (117) is implicitly covered by result.status_code. *)
    (* YP (127), YP (129), failure cases. YP (128) is implicitly covered by exceptional halting returning
       Evmc.Result.failure, which sets gas refund to zero. YP (130) is implicitly covered by
       result.status_code. *)
    let$ () = when_ (result.status_code <> Success) (put initial_state) in
    return result

  (** {!Evmc.HOST.call} *)
  let call (msg : Evmc.Message.t) = call_impl ~from_tx:None msg

  (** [call_from_eoa tx msg] processes a message (contract creation or call) created from a transaction sent
      by an EOA, as opposed to a system transaction or a CALL opcode which are handled by {!call} directly. *)
  let call_from_eoa (tx : Transaction.t) (msg : Evmc.Message.t) = call_impl ~from_tx:(Some tx) msg

  (** {!Evmc.HOST.get_tx_context} *)
  let get_tx_context =
    let$ state = get in
    return
      Evmc.TxContext.
        { tx_gas_price = U256.of_uint_exn state.tx_gas_price
        ; tx_origin = state.tx_origin
        ; block_coinbase = state.current_block.header.beneficiary
        ; block_number = Uint.to_uint64 state.current_block.header.number
        ; block_timestamp = U256.to_uint64 state.current_block.header.timestamp
        ; block_gas_limit = Gas.to_uint64 state.current_block.header.gas_limit
        ; block_prev_randao = U256.of_repr state.current_block.header.prev_randao
        ; chain_id = U256.of_uint_exn ChainParams.chain_id
        ; block_base_fee = U256.of_uint_exn state.current_block.header.base_fee_per_gas
        ; blob_base_fee =
            (* The current Monad implementation calculates blob base fee as per EIP-4844, which is
               inconsistent with Prague as it does not implement the blob fee changes in EIP-7691.
               As blob transactions are disallowed in Monad, we set it to one here. This should not
               case an observable difference in the behaviour of the BLOBBASEFEE opcode unless a block
               has non-zero excess_blob_gas. *)
            U256.one
        ; blob_hashes = []
        ; initcodes = [] }

  (** {!Evmc.HOST.get_block_hash} *)
  let get_block_hash (i : Uint64.t) =
    let$ state = get in
    state.world_state.history
    |> List.find_opt (fun (block : Block.t) -> Uint.(block.header.number = of_uint64 i))
    |> Option.map Block.hash
    |> return

  (** {!Evmc.HOST.emit_log} *)
  let emit_log address ~(data : Bytes.t) ~(topics : B32.t list) =
    let log : Log.t = {address; topics; data} in
    update_field logs (fun logs -> log :: logs)

  (** {!Evmc.HOST.access_account} *)
  let access_account addr : [`Warm | `Cold] t =
    let$ accessed = !accessed_addresses in
    if Option.is_some (Address.Set.find_opt addr accessed) then return `Warm
    else
      let$ () = touch_account addr in
      return `Cold

  (** {!Evmc.HOST.access_storage} *)
  let access_storage addr key =
    let$ accessed = !accessed_keys in
    if Option.is_some (StorageKey.Set.find_opt (addr, key) accessed) then return `Warm
    else
      let$ () = touch_storage addr key in
      return `Cold

  let transient_storage addr key =
    transient_storage
    |-- Address.Map.at addr
    |-- Option.get_or_default B32.Map.empty
    |-- B32.Map.at key
    |-- Option.get_or_default B32.zeros

  (** {!Evmc.HOST.get_transient_storage} *)
  let get_transient_storage addr key = !(transient_storage addr key)

  (** {!Evmc.HOST.set_transient_storage} *)
  let set_transient_storage addr key value = transient_storage addr key := value
end

module Instantiate
    (ChainParams : Chain.Monad.PARAMS)
    (Vm : functor (Host : Evmc.HOST with type t = TransactionState.t) -> Evmc.Vm(TransactionState).SIG) =
struct
  include Evmc.Instantiate (TransactionState) (Make (ChainParams)) (Vm)
  module Host = Make (ChainParams) (Vm)
end
