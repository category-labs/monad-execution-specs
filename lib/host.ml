open Numeric
open Byte_string
open Chain.Ethereum
open Lens.Infix
open State

module Make
    (ChainParams : Chain.Monad.PARAMS)
    (Vm : sig
      val execute : Evmc.Message.t -> Bytes.t -> Evmc.Result.t TransactionState.M.t
    end) =
struct
  open Account.TLens
  open WorldState
  include TransactionState
  open M

  let dump_account addr =
    let$ acc = !(account addr) in
    Format.eprintf "%s: %s\n" (Address.to_hex_string addr)
      (Yojson.Safe.pretty_to_string (Account.to_yojson acc)) ;
    return ()

  let transfer_ether sender recipient amount =
    let$ sender_balance = !(account sender |-- balance) in
    if U256.(sender_balance >= amount) then
      let$ () = account sender |-- balance := U256.(sender_balance - amount) in
      let$ () = update_field (account recipient |-- balance) (fun eth -> U256.(eth + amount)) in
      return true
    else return false

  let account_exists addr = Option.is_some <$> !(world_state |-- accounts |-- Address.Map.at addr)

  let get_storage addr key =
    !(account addr |-- Account.storage |-- B32.Map.at key |-- Option.get_or_default B32.zeros)

  let set_storage addr key v =
    let$ o =
      !( initial_world_state
       |-- WorldState.account addr
       |-- storage
       |-- B32.Map.at key
       |-- Option.get_or_default B32.zeros )
    in
    let$ c = !(account addr |-- storage |-- B32.Map.at key |-- Option.get_or_default B32.zeros) in
    (* In practice there is no way to modify the storage of an account with zero nonce, so there is no
       need to keep empty accounts here. However, for the purpose of unit tests, it is useful to allow storage
       operations to work on empty accounts without clearing them up automatically. *)
    let$ () =
      account ~keep_empty:true addr |-- storage |-- B32.Map.at key := if B32.(v = zeros) then None else Some v
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

  let get_balance addr = !(account addr |-- balance)

  let get_code_size addr =
    let$ code = !(account addr |-- code) in
    return (Uint64.of_int (Bytes.length code))

  let get_code_hash addr =
    let$ account = !(account addr) in
    return (if Account.is_empty account then None else Some (Crypto.keccak_256 account.code))

  let copy_code addr ~offset ~size =
    let$ code = !(account addr |-- code) in
    return (Bytes.sub_with_zero_padding code offset size)

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

  let touch_account addr = M.update_field accessed_addresses (Address.Set.add addr)

  let touch_storage addr key =
    M.(
      let$ () = touch_account addr in
      update_field accessed_keys (StorageKey.Set.add (addr, key)) )

  let process_call (from_tx : Transaction.t option) (msg : Evmc.Message.t) =
    assert (msg.kind = Call || msg.kind = CallCode || msg.kind = DelegateCall) ;
    let$ transfer_ok =
      if should_transfer msg then transfer_ether msg.sender msg.recipient msg.value else return true
    in
    if transfer_ok then
      let$ code_address, code =
        let$ account_code = !(account msg.code_address |-- code) in
        (* If the call came from a smart contract, the VM has already resolved the target address. It is not
           necessary to resolve it twice. TODO: simplify this. *)
        match (from_tx, Delegation.get_delegated_address account_code) with
        | Some _, Some delegated_addr ->
            let$ delegated_code = !(account delegated_addr |-- code) in
            return (delegated_addr, delegated_code)
        | _ -> return (msg.code_address, account_code)
      in
      match Address.Map.find_opt code_address (Precompiles.precompiles ChainParams.revision) with
      | Some precompile -> precompile msg
      | None -> Vm.execute msg code
    else return Evmc.Result.(failure StatusCode.Insufficient_balance)

  let process_create (msg : Evmc.Message.t) =
    let$ sender_nonce = !(account msg.sender |-- nonce) in
    let create_address =
      Address.of_contract_creation ~sender:msg.sender ~nonce:sender_nonce
        ~create2:
          (if msg.kind = Create2 then Some {salt = msg.create2_salt; initcode = msg.input_data} else None)
    in
    let$ () = touch_account create_address in
    let$ pre_existent_account = !(account create_address) in
    if U64.(pre_existent_account.nonce <> zero) || pre_existent_account.code <> Bytes.empty then
      (* EIP-684 *)
      return
        Evmc.Result.
          { status_code = StatusCode.Contract_validation_failure
          ; gas_left = 0L
          ; gas_refund = 0L
          ; output_data = Bytes.empty
          ; create_address = Address.zero }
    else
      let$ () =
        update_field accounts_created_in_current_transaction (fun addresses ->
            Address.Set.add create_address addresses )
      in
      let$ () = account create_address |-- storage := B32.Map.empty in
      let$ () = account create_address |-- nonce := U64.one in
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
          Vm.execute creation_msg msg.input_data
        else return Evmc.Result.(failure StatusCode.Insufficient_balance)
      in

      match result.status_code with
      | Success ->
          let contract_code = result.output_data in
          let contract_length = Bytes.length contract_code in
          let contract_code_gas = Gas.(of_int contract_length * code_deposit_per_byte) in
          if
            (contract_length > 0 && contract_code.[0] = '\xef')
            || Gas.(contract_code_gas > of_int64 result.gas_left)
          then
            return
              { result with
                gas_left = Int64.zero
              ; output_data = Bytes.empty
              ; status_code =
                  Evmc.Result.StatusCode.(
                    if contract_code.[0] = '\xef' then Contract_validation_failure else Out_of_gas ) }
          else
            let$ () = account create_address |-- code := contract_code in
            return {result with create_address}
      | _ -> return result

  let call_impl ~(from_tx : Transaction.t option) (msg : Evmc.Message.t) =
    let$ () =
      (* Increment the nonce for non-EOA CREATE/CREATE2 messages . If the message came from an EOA transaction,
         the nonce was already incremented in the irrevocable change. *)
      when_ ((msg.kind = Create || msg.kind = Create2) && Option.is_none from_tx) (increment_nonce msg.sender)
    in
    let$ initial_state = get in
    let$ result =
      match msg.kind with
      | Call | DelegateCall | CallCode -> process_call from_tx msg
      | Create | Create2 -> process_create msg
    in
    let$ result =
      match from_tx with
      | Some _t when result.status_code = Success ->
          (* Check reserve balance condition. Monad §6 Algorithm 2. *)
          let$ reserve_dipped = Reserve_balance.dipped_into_reserve ChainParams.revision in
          return (if reserve_dipped then {result with status_code = Revert; gas_refund = 0L} else result)
      | Some _ | None -> return result
    in
    let$ () = when_ (result.status_code <> Success) (put initial_state) in
    return result

  let call (msg : Evmc.Message.t) = call_impl ~from_tx:None msg

  (* Call from a transaction sent by an EOA, as opposed to a system transaction or a CALL opcode. *)
  let call_from_eoa (tx : Transaction.t) (msg : Evmc.Message.t) = call_impl ~from_tx:(Some tx) msg

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

  let get_block_hash (i : Uint64.t) =
    let$ state = get in
    state.world_state.history
    |> List.find_opt (fun (block : Block.t) -> Uint.(block.header.number = of_uint64 i))
    |> Option.map Block.hash
    |> return

  let emit_log address ~(data : Bytes.t) ~(topics : B32.t list) =
    let log : Log.t = {address; topics; data} in
    update_field logs (fun logs -> log :: logs)

  let access_account addr : [`Warm | `Cold] t =
    let$ accessed = !accessed_addresses in
    if Option.is_some (Address.Set.find_opt addr accessed) then return `Warm
    else
      let$ () = touch_account addr in
      return `Cold

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

  let get_transient_storage addr key = !(transient_storage addr key)

  let set_transient_storage addr key value = transient_storage addr key := value
end

module Instantiate
    (ChainParams : Chain.Monad.PARAMS)
    (Vm : functor (Host : Evmc.HOST with type t = TransactionState.t) -> Evmc.Vm(TransactionState).SIG) =
struct
  include Evmc.Instantiate (TransactionState) (Make (ChainParams)) (Vm)
  module Host = Make (ChainParams) (Vm)
end
