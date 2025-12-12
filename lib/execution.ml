open Lens.Infix

open Chain.Ethereum
open Numeric
open Byte_string
open State

let prepare_message (block_state : BlockState.t) (sender : Address.t) (gas : Gas.t) (tx : Transaction.t) =
  let kind, current_target, data, code, code_address =
    match Transaction.call_or_create tx with
    | Call {to_; data} ->
        let code =
          let account_code = block_state.^(BlockState.account to_).code in
          match Delegation.get_delegated_address account_code with
          | None -> account_code
          | Some delegated -> block_state.^(BlockState.account delegated).code
        in
        (Evmc.Message.CallKind.Call, to_, data, code, to_)
    | Create {initcode} ->
        let nonce = block_state.^(BlockState.account sender).nonce in
        let target = Address.of_contract_creation ~sender ~nonce ~create2:None in
        (Evmc.Message.CallKind.Create, target, Bytes.empty, initcode, Address.zero)
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

let process_message ?(trace = false) (msg : Evmc.Message.t) (transaction_state : TransactionState.t) =
  let module H =
    Evmc.Instantiate (TransactionState.M) (Host)
      (Vm.Make (struct
        let trace = trace
      end))
  in
  H.Host.call msg transaction_state

let process_authorization transaction_state (authorization : Transaction.Authorization.t) : TransactionState.t
    =
  let open TransactionState in
  match Transaction.Authorization.authority authorization with
  | None ->
      (* As per EIP-7702, skip invalid authorizations. *)
      transaction_state
  | Some authority ->
      let transaction_state =
        { transaction_state with
          accessed_addresses = Address.Set.add authority transaction_state.accessed_addresses }
      in
      let Account.{code; nonce; _} = transaction_state.^(account authority) in
      if
        (Bytes.(code = empty) || Delegation.is_valid_delegation code)
        && Uint.(U64.to_uint authorization.nonce = U256.to_uint nonce)
      then
        transaction_state.^(account authority |-- Account.code) <-
          Delegation.delegation_code authorization.address
      else transaction_state

let process_transaction (block_state : BlockState.t) (tx : Transaction.t) =
  let open BlockState in
  let tx_gas_limit =
    Transaction.gas_limit tx
    (* T_g *)
  in
  let tx_value = Transaction.value tx in
  let tx_nonce = Transaction.nonce tx in

  (* Basic validity checks. *)
  (* Nonce *)
  if U256.(tx_nonce >= of_uint64 Uint64.max_uint) then failwith "Invalid transaction" ;
  (* Initcode size *)
  ( match Transaction.call_or_create tx with
  | Create {initcode} when Bytes.length initcode > 2 * Vm.max_init_code_size -> failwith "Invalid transaction"
  | _ -> () ) ;

  (* YP (64) *)
  let intrinsic_gas = Gas.tx_intrinsic_gas tx in
  if Gas.(intrinsic_gas > tx_gas_limit) then failwith "Invalid transaction" ;

  (* EIP-7623 *)
  let floor_gas = Gas.tx_floor_gas tx in
  if Gas.(floor_gas > tx_gas_limit) then failwith "Invalid transaction" ;

  let block = block_state.current_block in
  let header = block.header in
  let base_fee_per_gas = header.base_fee_per_gas in
  (* Calculate effective gas price and max payable gas fee depending on transaction type. Here we also check
     that the gas fee stipulated by the transaction is at least as large as the base gas fee for this block. *)
  let effective_gas_price, max_gas_fee =
    match Transaction.fee_mechanism tx with
    | FeeMarketFee {max_fee_per_gas; max_priority_fee_per_gas} ->
        if Gas.(max_fee_per_gas < max_priority_fee_per_gas) then failwith "Invalid transaction" ;
        if Gas.(max_fee_per_gas < base_fee_per_gas) then failwith "Invalid transaction" ;
        let priority_fee_per_gas = Gas.(min max_priority_fee_per_gas (max_fee_per_gas - base_fee_per_gas)) in
        let effective_gas_price = Gas.(priority_fee_per_gas + base_fee_per_gas) in
        let max_gas_fee = Gas.(Transaction.gas_limit tx * max_fee_per_gas) in
        (effective_gas_price, max_gas_fee)
    | LegacyFee {gas_price} ->
        if Gas.(gas_price < base_fee_per_gas) then failwith "Invalid transaction" ;
        (gas_price, Gas.(tx_gas_limit * gas_price))
  in

  let sender = Option.get (Transaction.sender block_state.world_state.chain_id tx) in
  let sender_account = block_state.world_state.^(WorldState.account sender) in
  if U256.(sender_account.nonce <> tx_nonce) then failwith "Invalid transaction" ;
  if Uint.(U256.to_uint sender_account.balance < max_gas_fee + U256.to_uint tx_value) then (
    Format.eprintf "Account %s (%s) cannot afford to pay %s gas fees + %s tx_value\n"
      (Address.to_hex_string sender)
      (U256.to_string sender_account.balance)
      (Gas.to_string max_gas_fee) (U256.to_string tx_value) ;
    failwith "Invalid transaction" ) ;
  if sender_account.code <> Bytes.empty && not (Delegation.is_valid_delegation sender_account.code) then
    failwith "Invalid transaction" ;

  let total_fee =
    let total_fee = Gas.(tx_gas_limit * effective_gas_price) in
    if total_fee > U256.to_uint sender_account.balance then failwith "Invalid transaction" ;
    U256.of_uint_exn total_fee
  in

  (* Pay gas fees, increase nonce *)
  let block_state =
    (* The yellow paper does not specify a behaviour for nonce overflows. *)
    assert (U256.(sender_account.nonce < max_t)) ;
    block_state.^(account sender) <-
      { sender_account with
        balance = U256.(sender_account.balance - total_fee)
      ; nonce = U256.(sender_account.nonce + one) }
  in

  (* Execute transaction. *)
  let result, transaction_state =
    let transaction_state = TransactionState.make block_state tx in

    (* Process EIP-7702 authorizations. *)
    let transaction_state =
      List.fold_left process_authorization transaction_state (Transaction.authorization_list tx)
    in

    let available_gas = Gas.(tx_gas_limit - intrinsic_gas) in
    let message = prepare_message block_state sender available_gas tx in
    process_message message transaction_state
  in

  (* Propagate state changes. *)
  let block_state = {block_state with world_state = transaction_state.world_state} in

  (* Monad §2.3: unlike Ethereum, gas is not refunded to the sender. *)
  let tx_gas_used = tx_gas_limit in

  (* Transfer miner fees. *)
  let priority_fee_per_gas = Gas.(effective_gas_price - base_fee_per_gas) in
  let transaction_fee = U256.of_uint_exn Gas.(tx_gas_used * priority_fee_per_gas) in
  let block_state = transfer_money_and_delete_if_empty block_state transaction_fee header.beneficiary in

  (* Destroy deleted accounts. *)
  let block_state =
    transaction_state.self_destruct
    |> Address.Set.to_seq
    |> Seq.fold_left
         (fun block_state touched_account -> block_state.^(account_opt touched_account) <- None)
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
    {block_state with transactions_processed = List.append block_state.transactions_processed [(tx, receipt)]}
  in

  block_state

let process_withdrawal (block_state : BlockState.t) (wd : Withdrawal.t) =
  BlockState.transfer_money_and_delete_if_empty block_state U256.(wd.amount * exp ~$10 ~$9) wd.recipient

let validate_header (_world_state : WorldState.t) (_header : Block.Header.t) =
  (* TODO *)
  ()

(* Process a system message call as in EIP-2935, EIP-4788. *)
let process_system_message (block_state : BlockState.t) (addr : Address.t) (data : Bytes.t) =
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
    let result, transaction_state = process_message message transaction_state in
    assert (result.status_code = Success) ;
    (* Update block state with storage changes. As per the relevant EIPs, a system message call
     does not warm up accounts or storage slots, and it does not count towards the block gas
     limit. *)
    (Some result, {block_state with world_state = transaction_state.world_state})

let beacon_roots_address = Address.of_hex_string "000F3df6D732807Ef1319fB7B8bB8522d0Beac02"
let history_storage_address = Address.of_hex_string "0000f90827f1c53a10cb7a02335b175320002935"

let process_block ~verify (world_state : WorldState.t) (block : Block.t) =
  validate_header world_state block.header ;
  if block.ommers <> [] then failwith "Invalid block" ;

  let block_state = BlockState.make world_state block in

  (* EIP-4788 *)
  let block_state =
    let parent_beacon_block_root = block_state.current_block.header.parent_beacon_block_root in
    (* Ignore call result as per EIP-4788. *)
    let _, block_state =
      process_system_message block_state beacon_roots_address (B32.to_bytes parent_beacon_block_root)
    in
    block_state
  in

  (* EIP-2935 *)
  let block_state =
    let parent_hash = block_state.current_block.header.parent_hash in
    (* Ignore call result as per EIP-2935. *)
    let _, block_state =
      process_system_message block_state history_storage_address (B32.to_bytes parent_hash)
    in
    block_state
  in

  (* Process block transactions. *)
  let block_state = List.fold_left process_transaction block_state block.transactions in

  (* Process block withdrawals. *)
  let block_state = List.fold_left process_withdrawal block_state block.withdrawals in

  (* TODO coalesce destructing dead accounts here *)

  (* Compute roots and add the finalized block to the blockchain. *)
  let finalized_block = BlockState.finalize_current_block block_state in
  if verify && block.header <> finalized_block.header then (
    Format.eprintf "Block verification failed\n" ;
    Format.eprintf "Expected: %s\n" (Yojson.Safe.pretty_to_string (Block.Header.to_yojson block.header)) ;
    Format.eprintf "Actual: %s\n"
      (Yojson.Safe.pretty_to_string (Block.Header.to_yojson finalized_block.header)) ;
    failwith "Block verification failed" ) ;
  {block_state.world_state with history = finalized_block :: world_state.history}
