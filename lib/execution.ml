open Chain.Ethereum
open Numeric
open Byte_string
open Host

module Make (Params : Chain.Monad.PARAMS) = struct
  module Error = struct
    type invalid_block =
      | Nonempty_ommers
      | Nonzero_difficulty
      | Nonzero_nonce
      | Wrong_base_fee of {expected : Gas.t}
      | Invalid_gas_limit
      | Gas_above_limit
      | Invalid_timestamp
      | Invalid_number
      | Extra_data_too_long
      | Wrong_parent_hash of {expected : B32.t}
      | Wrong_merkle_root of {kind : [`Transactions | `Withdrawals | `State | `Receipts]; expected : B32.t}
      | Wrong_gas_used of {expected : Gas.t}
      | Wrong_logs_bloom of {expected : Bloom.t}
    [@@deriving to_yojson]

    type invalid_transaction =
      | Wrong_chain_id
      | Invalid_signature
      | Invalid_nonce
      | Nonce_overflow
      | Initcode_too_long
      | Insufficient_balance of {balance : U256.t; required : Gas.t}
      | Invalid_delegation of {code : Bytes.t}
      | Cannot_pay_floor_gas of {floor_gas : Gas.t}
      | Cannot_pay_intrinsic_gas of {intrinsic_gas : Gas.t}
      | Empty_authorization_list
      | Transaction_fee_below_base of {base_fee_per_gas : Gas.t}
    [@@deriving to_yojson]

    type t =
      | Invalid_block of {block : Block.t; reason : invalid_block}
      | Invalid_transaction of {block : Block.t; transaction : Transaction.t; reason : invalid_transaction}
    [@@deriving to_yojson]

    let to_string err = Yojson.Safe.pretty_to_string (to_yojson err)
  end

  let invalid_block block reason = Error Error.(Invalid_block {block; reason})
  let invalid_transaction block transaction reason =
    Error Error.(Invalid_transaction {block; transaction; reason})
  type 'a or_error = ('a, Error.t) result

  let prepare_message (sender : Address.t) (gas : Gas.t) (tx : Transaction.t) =
    let kind, current_target, data, code, code_address =
      match Transaction.call_or_create tx with
      | Call {to_; data} -> (Evmc.Message.CallKind.Call, to_, data, Bytes.empty, to_)
      | Create {initcode} -> (Evmc.Message.CallKind.Create, Address.zero, initcode, Bytes.empty, Address.zero)
    in
    Evmc.Message.
      { kind
      ; sender
      ; recipient = current_target
      ; value = Transaction.value tx
      ; gas = Gas.to_int64 gas
      ; code
      ; code_address
      ; static = false
      ; delegated = Delegation.is_valid_delegation code
      ; input_data = data
      ; depth = 0l
      ; create2_salt = B32.zeros }

  let process_message ~eoa ?(trace = false) (msg : Evmc.Message.t) (transaction_state : TransactionState.t) =
    let module H =
      Host.Instantiate
        (Params)
        (Vm.Make (struct
          let trace = trace
        end))
    in
    H.Host.(run (call_impl ~eoa msg)) transaction_state

  let validate_authorizations (block : Block.t) (tx : Transaction.t) : unit or_error =
    (* Validate transaction list of EIP-7702 SET_CODE transaction. We do not need to check field bounds her
       as these are implicit in the bit widths of the corresponding types. *)
    let open Result in
    match tx with
    | Transaction.SetCode {authorization_list = []; _} ->
        invalid_transaction block tx Empty_authorization_list
    | _ -> return ()

  let process_authorization transaction_state (authorization : Transaction.Authorization.t) :
      TransactionState.t =
    let open TransactionState in
    (* As per EIP-7702, invalid authorizations are skipped. *)
    if
      (U256.(authorization.chain_id <> zero) && Uint.(U256.to_uint authorization.chain_id <> Params.chain_id))
      || U64.(authorization.nonce = max_t)
    then transaction_state
    else
      match Transaction.Authorization.authority authorization with
      | None -> transaction_state
      | Some authority ->
          let transaction_state =
            { transaction_state with
              accessed_addresses = Address.Set.add authority transaction_state.accessed_addresses }
          in
          let (Account.{code; nonce; _} as authority_account) = transaction_state.^(account authority) in
          if (Bytes.(code = empty) || Delegation.is_valid_delegation code) && U64.(authorization.nonce = nonce)
          then
            let code = Delegation.delegation_code authorization.address in
            let code_hash = Crypto.keccak_256 code in
            let nonce = U64.(authority_account.nonce + one) in
            let authority_account = {authority_account with code; code_hash; nonce} in
            transaction_state
            |> (fun s -> s.^(account authority) <- authority_account)
            |> fun s ->
            if not (Account.is_empty authority_account) then
              s.^(refund) <- U256.(s.refund + of_uint_exn Gas.tx_authorization_list_refund_per_nonempty)
            else s
          else transaction_state

  type transaction_validation =
    {sender : Address.t; total_fee : U256.t; effective_gas_price : Uint.t; intrinsic_gas : Gas.t}

  let validate_transaction (block_state : BlockState.t) (tx : Transaction.t) : transaction_validation or_error
      =
    Result.(
      let block = block_state.current_block in

      let$ () =
        match Transaction.chain_id tx with
        | Some chain_id when Uint.(chain_id <> Params.chain_id) -> invalid_transaction block tx Wrong_chain_id
        | _ -> return ()
      in

      (* T_g *)
      let tx_gas_limit = Transaction.gas_limit tx in
      let tx_nonce = Transaction.nonce tx in

      (* Basic validity checks. *)
      (* Nonce *)
      let$ () = when_ U64.(tx_nonce = max_t) (invalid_transaction block tx Nonce_overflow) in
      let$ sender =
        match Transaction.sender Params.chain_id tx with
        | None -> invalid_transaction block tx Invalid_signature
        | Some sender -> return sender
      in
      let sender_account = block_state.world_state.^(WorldState.account sender) in
      let$ () = when_ U64.(sender_account.nonce <> tx_nonce) (invalid_transaction block tx Invalid_nonce) in
      (* Initcode size *)
      let$ () =
        match Transaction.call_or_create tx with
        | Create {initcode} when Bytes.length initcode > 2 * Vm.max_init_code_size ->
            invalid_transaction block tx Initcode_too_long
        | _ -> return ()
      in

      (* YP (64) *)
      let intrinsic_gas = Gas.tx_intrinsic_gas tx in
      let$ () =
        when_
          Gas.(intrinsic_gas > tx_gas_limit)
          (invalid_transaction block tx (Cannot_pay_intrinsic_gas {intrinsic_gas}))
      in

      (* EIP-7623 *)
      let floor_gas = Gas.tx_floor_gas tx in
      let$ () =
        when_ Gas.(floor_gas > tx_gas_limit) (invalid_transaction block tx (Cannot_pay_floor_gas {floor_gas}))
      in

      let block = block_state.current_block in
      let header = block.header in
      let$ () =
        when_
          (Bytes.(sender_account.code <> empty) && not (Delegation.is_valid_delegation sender_account.code))
          (invalid_transaction block tx (Invalid_delegation {code = sender_account.code}))
      in
      (* Validate EIP-7702 authorization list if relevant. *)
      let$ () = validate_authorizations block tx in

      (* Calculate effective gas price and max payable gas fee depending on transaction type. Here we also check
     that the gas fee stipulated by the transaction is at least as large as the base gas fee for this block. *)
      (* TODO: check transaction's suggested gas fee is above the block's base gas fee. *)
      let base_fee_per_gas = header.base_fee_per_gas in
      let$ effective_gas_price =
        match Gas.tx_effective_gas_price base_fee_per_gas tx with
        | Some effective_gas_price -> Ok effective_gas_price
        | None -> invalid_transaction block tx (Transaction_fee_below_base {base_fee_per_gas})
      in
      let total_fee = Gas.(Transaction.gas_limit tx * effective_gas_price) in
      (* Note that in Monad, a transaction only needs to be able to pay the gas fee to be considered valid. If
         the account can pay for the gas fees but not for the value transfer, the transaction will fail but it
         will not be considered invalid. In particular, irrevocable changes (fees paid, nonce incremented) will
         take place. *)
      let$ () =
        when_
          Uint.(total_fee > U256.to_uint sender_account.balance)
          (invalid_transaction block tx
             (Insufficient_balance {balance = sender_account.balance; required = total_fee}) )
      in
      let total_fee =
        U256.of_uint_exn total_fee
        (* Cannot fail as the check above ensures total_fee is bounded by balance. *)
      in

      return {sender; total_fee; effective_gas_price; intrinsic_gas} )

  let process_transaction ?(trace = false) (block_state : BlockState.t) (tx : Transaction.t) :
      BlockState.t or_error =
    let open Result in
    let header = block_state.current_block.header in
    let$ {sender; total_fee; effective_gas_price; intrinsic_gas} = validate_transaction block_state tx in

    (* Execute transaction. *)
    let result, transaction_state =
      let transaction_state = TransactionState.make Params.chain_id block_state tx in

      (* Irrevocable change: pay gas fees. YP (73), YP (74). *)
      let transaction_state =
        transaction_state.^$(TransactionState.account sender) <-
          (fun sender_account -> {sender_account with balance = U256.(sender_account.balance - total_fee)})
      in

      (* Process EIP-7702 authorizations. *)
      let transaction_state =
        List.fold_left process_authorization transaction_state (Transaction.authorization_list tx)
      in

      let available_gas = Gas.(Transaction.gas_limit tx - intrinsic_gas) in
      let message = prepare_message sender available_gas tx in
      process_message ~eoa:true ~trace message transaction_state
    in

    (* Propagate state changes. *)
    let block_state = {block_state with world_state = transaction_state.world_state} in

    (* Monad §2.3: unlike Ethereum, gas is not refunded to the sender. *)
    let tx_gas_used = Transaction.gas_limit tx in

    (* Transfer miner fees. *)
    let priority_fee_per_gas = Gas.(effective_gas_price - header.base_fee_per_gas) in
    let transaction_fee = U256.of_uint_exn Gas.(tx_gas_used * priority_fee_per_gas) in
    let block_state =
      BlockState.transfer_money_and_delete_if_empty block_state transaction_fee header.beneficiary
    in

    (* Destroy deleted accounts. *)
    let block_state =
      transaction_state.self_destruct
      |> Address.Set.to_seq
      |> Seq.fold_left
           (fun block_state touched_account -> block_state.^(BlockState.account_opt touched_account) <- None)
           block_state
    in

    (* Update gas used by the block. *)
    let block_gas_used = Gas.(block_state.gas_used + tx_gas_used) in
    let block_state = {block_state with gas_used = block_gas_used} in

    (* Add receipt and logs. *)
    let block_state =
      let receipt =
        let bloom = Bloom.union (Seq.map Log.to_bloom (List.to_seq transaction_state.logs)) in
        Receipt.
          { tx_type = Transaction.kind_tag tx
          ; cumulative_gas_used = block_state.gas_used
          ; bloom
          ; succeeded = result.status_code = Success
          ; logs = transaction_state.logs }
      in
      { block_state with
        transactions_processed = List.append block_state.transactions_processed [(tx, receipt)] }
    in

    return block_state

  let process_withdrawal (block_state : BlockState.t) (wd : Withdrawal.t) : BlockState.t =
    let block_state =
      BlockState.transfer_money_and_delete_if_empty block_state U256.(wd.amount * exp ~$10 ~$9) wd.recipient
    in
    {block_state with withdrawals_processed = List.append block_state.withdrawals_processed [wd]}

  (* YP (60) *)
  let validate_block (world_state : WorldState.t) (block : Block.t) : unit or_error =
    let open Result in
    let header = block.header in

    let parent = List.hd world_state.history in

    (* YP (47) *)
    let$ () = when_ Uint.(header.number <> parent.header.number + one) (invalid_block block Invalid_number) in

    (* YP (48) *)
    (* TODO: adapt to account for Monad base fee update rules. *)

    (* YP (54) (YP (55) does not apply) *)
    let max_gas_limit_update = Gas.(parent.header.gas_limit / ~$1024) in
    let$ () =
      when_
        ( Gas.(header.gas_limit < ~$5_000)
        || Gas.(header.gas_limit >= parent.header.gas_limit + max_gas_limit_update)
        || Gas.(header.gas_limit <= parent.header.gas_limit - max_gas_limit_update) )
        (invalid_block block Invalid_gas_limit)
    in

    let$ () = when_ Gas.(header.gas_used > header.gas_limit) (invalid_block block Gas_above_limit) in

    (* YP (56) *)
    let$ () =
      when_ U256.(header.timestamp <= parent.header.timestamp) (invalid_block block Invalid_timestamp)
    in

    (* YP (57) *)
    let$ () =
      when_
        (B32.(header.ommers_hash <> Crypto.keccak_256 Rlp.(encode (List []))) || block.ommers <> [])
        (invalid_block block Nonempty_ommers)
    in
    let$ () = when_ Uint.(header.difficulty <> zero) (invalid_block block Nonzero_difficulty) in
    let$ () = when_ B8.(header.nonce <> zeros) (invalid_block block Nonzero_nonce) in

    let$ () = when_ (Bytes.length block.header.extra_data > 32) (invalid_block block Extra_data_too_long) in

    (* TODO validate prevrandao *)
    return ()

  (* Process a system message call as in EIP-2935, EIP-4788. *)
  let process_system_message ?(trace = false) (block_state : BlockState.t) (addr : Address.t) (data : Bytes.t)
      =
    let system_sender_address = Address.of_hex_string "0xfffffffffffffffffffffffffffffffffffffffe" in
    let code = block_state.^(BlockState.account addr).code in
    if code = Bytes.empty then (None, block_state)
    else
      let message =
        Evmc.Message.
          { sender = system_sender_address
          ; kind = Call
          ; static = false
          ; delegated = false
          ; depth = 0l
          ; gas = Gas.(to_uint64 system_transaction_gas)
          ; value = U256.zero
          ; recipient = addr
          ; input_data = data
          ; create2_salt = B32.zeros
          ; code_address = addr
          ; code }
      in
      let transaction_state =
        TransactionState.
          { initial_world_state = block_state.world_state
          ; world_state = block_state.world_state
          ; current_block = block_state.current_block
          ; transient_storage = Address.Map.empty
          ; accounts_created_in_current_transaction = Address.Set.empty
          ; tx_origin = system_sender_address
          ; tx_gas_price = Uint.zero
          ; self_destruct = Address.Set.empty
          ; logs = []
          ; touched = Address.Set.empty
          ; refund = U256.zero
          ; accessed_addresses = Address.Set.empty
          ; accessed_keys = StorageKey.Set.empty }
      in
      let result, transaction_state = process_message ~eoa:false ~trace message transaction_state in
      assert (result.status_code = Success) ;
      (* Update block state with storage changes. As per the relevant EIPs, a system message call
       does not warm up accounts or storage slots, and it does not count towards the block gas
       limit. *)
      (Some result, {block_state with world_state = transaction_state.world_state})

  let beacon_roots_address = Address.of_hex_string "000F3df6D732807Ef1319fB7B8bB8522d0Beac02"
  let history_storage_address = Address.of_hex_string "0000f90827f1c53a10cb7a02335b175320002935"

  let validate_input_block_against_output ~(input_block : Block.t) ~(output_block : Block.t) =
    let open Result in
    let input_header = input_block.header in
    let output_header = output_block.header in

    let$ () =
      when_
        B32.(input_header.state_root <> output_header.state_root)
        (invalid_block input_block (Wrong_merkle_root {kind = `State; expected = output_header.state_root}))
    in
    let$ () =
      when_
        B32.(input_header.receipts_root <> output_header.receipts_root)
        (invalid_block input_block
           (Wrong_merkle_root {kind = `Receipts; expected = output_header.receipts_root}) )
    in
    let$ () =
      when_
        B32.(input_header.withdrawals_root <> output_header.withdrawals_root)
        (invalid_block input_block
           (Wrong_merkle_root {kind = `Withdrawals; expected = output_header.withdrawals_root}) )
    in
    let$ () =
      when_
        B32.(input_header.transactions_root <> output_header.transactions_root)
        (invalid_block input_block
           (Wrong_merkle_root {kind = `Transactions; expected = output_header.transactions_root}) )
    in

    let$ () =
      when_
        Bloom.(input_header.logs_bloom <> output_header.logs_bloom)
        (invalid_block input_block (Wrong_logs_bloom {expected = output_header.logs_bloom}))
    in

    let$ () =
      when_
        Gas.(input_header.gas_used <> output_header.gas_used)
        (invalid_block input_block (Wrong_gas_used {expected = output_header.gas_used}))
    in

    let$ () =
      when_
        B32.(input_header.parent_hash <> output_header.parent_hash)
        (invalid_block input_block (Wrong_parent_hash {expected = output_header.parent_hash}))
    in

    assert (input_block = output_block) ;

    return ()

  let process_block ?(trace = false) ~verify (world_state : WorldState.t) (block : Block.t) :
      WorldState.t or_error =
    let open Result in
    let$ () = validate_block world_state block in

    let block_state = BlockState.make world_state block in

    (* EIP-4788 *)
    let block_state =
      let parent_beacon_block_root = block_state.current_block.header.parent_beacon_block_root in
      (* Ignore call result as per EIP-4788. *)
      let _, block_state =
        process_system_message ~trace block_state beacon_roots_address (B32.to_bytes parent_beacon_block_root)
      in
      block_state
    in

    (* EIP-2935 *)
    let block_state =
      let parent_hash = Block.hash (List.hd world_state.history) in
      (* Ignore call result as per EIP-2935. *)
      let _, block_state =
        process_system_message ~trace block_state history_storage_address (B32.to_bytes parent_hash)
      in
      block_state
    in

    (* Process block transactions. *)
    let$ block_state = List.fold_leftM ~f:(process_transaction ~trace) block_state block.transactions in

    (* Process block withdrawals. *)
    let block_state = List.fold_left process_withdrawal block_state block.withdrawals in

    (* TODO coalesce destructing dead accounts here *)

    (* Compute roots and add the finalized block to the blockchain. *)
    let finalized_block, block_state = BlockState.finalize_current_block block_state in
    let$ () = validate_block world_state finalized_block in

    let$ () =
      if verify then validate_input_block_against_output ~input_block:block ~output_block:finalized_block
      else return ()
    in
    return {block_state.world_state with history = finalized_block :: world_state.history}
end
