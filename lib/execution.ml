open Lens.Infix

open Chain.Ethereum
open Numeric
open Byte_string
open Host

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
  | Invalid_nonce
  | Nonce_overflow
  | Initcode_too_long
  | Insufficient_balance of {balance : U256.t; required : Gas.t}
  | Invalid_delegation of {code : Bytes.t}
  | Cannot_pay_floor_gas of {floor_gas : Gas.t}
  | Cannot_pay_intrinsic_gas of {intrinsic_gas : Gas.t}
[@@deriving to_yojson]

exception Invalid_block of (Block.t * invalid_block)
exception Invalid_transaction of (Transaction.t * invalid_transaction)

let invalid_block block reason = raise (Invalid_block (block, reason))
let invalid_transaction tx reason = raise (Invalid_transaction (tx, reason))

let () =
  Printexc.register_printer (function
    | Invalid_block (block, reason) ->
        Some
          (Format.sprintf "Block %s: %s\n" (Uint.to_string block.header.number)
             (Yojson.Safe.pretty_to_string (invalid_block_to_yojson reason)) )
    | Invalid_transaction (_, reason) ->
        Some (Yojson.Safe.pretty_to_string (invalid_transaction_to_yojson reason))
    | _ -> None )

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
  let module H = Host.Instantiate (Vm.Make (struct
    let trace = trace
  end)) in
  H.Host.call_impl ~eoa msg transaction_state

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

let process_transaction ?(trace = false) (block_state : BlockState.t) (tx : Transaction.t) =
  let open BlockState in
  (* T_g *)
  let tx_gas_limit = Transaction.gas_limit tx in
  let tx_value = Transaction.value tx in
  let tx_nonce = Transaction.nonce tx in

  (* Basic validity checks. *)
  (* Nonce *)
  if U256.(tx_nonce >= of_uint64 Uint64.max_uint) then invalid_transaction tx Nonce_overflow ;
  (* Initcode size *)
  ( match Transaction.call_or_create tx with
  | Create {initcode} when Bytes.length initcode > 2 * Vm.max_init_code_size ->
      invalid_transaction tx Initcode_too_long
  | _ -> () ) ;

  (* YP (64) *)
  let intrinsic_gas = Gas.tx_intrinsic_gas tx in
  if Gas.(intrinsic_gas > tx_gas_limit) then invalid_transaction tx (Cannot_pay_intrinsic_gas {intrinsic_gas}) ;

  (* EIP-7623 *)
  let floor_gas = Gas.tx_floor_gas tx in
  if Gas.(floor_gas > tx_gas_limit) then invalid_transaction tx (Cannot_pay_floor_gas {floor_gas}) ;

  let block = block_state.current_block in
  let header = block.header in
  let base_fee_per_gas = header.base_fee_per_gas in
  (* Calculate effective gas price and max payable gas fee depending on transaction type. Here we also check
     that the gas fee stipulated by the transaction is at least as large as the base gas fee for this block. *)
  (* TODO: check transaction's suggested gas fee is above the block's base gas fee. This should go in
     validate_header. *)
  let effective_gas_price = Gas.tx_effective_gas_price base_fee_per_gas tx in
  let max_gas_fee = Gas.tx_max_gas_fee tx in

  let sender = Option.get (Transaction.sender block_state.world_state.chain_id tx) in
  let sender_account = block_state.world_state.^(WorldState.account sender) in
  if U256.(sender_account.nonce <> tx_nonce) then invalid_transaction tx Invalid_nonce ;
  if Uint.(U256.to_uint sender_account.balance < max_gas_fee + U256.to_uint tx_value) then
    invalid_transaction tx
      (Insufficient_balance
         {balance = sender_account.balance; required = Uint.(max_gas_fee + U256.to_uint tx_value)} ) ;
  if sender_account.code <> Bytes.empty && not (Delegation.is_valid_delegation sender_account.code) then
    invalid_transaction tx (Invalid_delegation {code = sender_account.code}) ;

  let total_fee =
    let total_fee = Gas.(tx_gas_limit * effective_gas_price) in
    if total_fee > U256.to_uint sender_account.balance then
      invalid_transaction tx (Insufficient_balance {balance = sender_account.balance; required = total_fee}) ;
    U256.of_uint_exn total_fee
  in

  (* Irrevocable change: pay gas fees. YP (73), YP (74). *)
  let block_state =
    (* The yellow paper does not specify a behaviour for nonce overflows. *)
    if U256.(sender_account.nonce = max_t) then invalid_transaction tx Nonce_overflow ;

    block_state.^(account sender) <- {sender_account with balance = U256.(sender_account.balance - total_fee)}
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
    process_message ~eoa:true ~trace message transaction_state
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

(* YP (60) *)
let validate_block (world_state : WorldState.t) (block : Block.t) =
  let header = block.header in

  let parent = List.hd world_state.history in

  (* YP (47) *)
  if Uint.(header.number <> parent.header.number + one) then invalid_block block Invalid_number ;

  (* YP (48) *)
  (* TODO: adapt to account for Monad base fee update rules. *)

  (* YP (54) (YP (55) does not apply) *)
  let max_gas_limit_update = Gas.(parent.header.gas_limit / ~$1024) in
  if
    Gas.(header.gas_limit < ~$5_000)
    || Gas.(header.gas_limit >= parent.header.gas_limit + max_gas_limit_update)
    || Gas.(header.gas_limit <= parent.header.gas_limit - max_gas_limit_update)
  then invalid_block block Invalid_gas_limit ;

  if Gas.(header.gas_used > header.gas_limit) then invalid_block block Gas_above_limit ;

  (* YP (56) *)
  if U256.(header.timestamp <= parent.header.timestamp) then invalid_block block Invalid_timestamp ;

  (* YP (57) *)
  if B32.(header.ommers_hash <> Crypto.keccak_256 Rlp.(encode (List []))) || block.ommers <> [] then
    invalid_block block Nonempty_ommers ;
  if Uint.(header.difficulty <> zero) then invalid_block block Nonzero_difficulty ;
  if B8.(header.nonce <> zeros) then invalid_block block Nonzero_nonce ;

  if Bytes.length block.header.extra_data > 32 then invalid_block block Extra_data_too_long ;

  (* TODO validate prevrandao *)
  ()

(* Process a system message call as in EIP-2935, EIP-4788. *)
let process_system_message ?(trace = false) (block_state : BlockState.t) (addr : Address.t) (data : Bytes.t) =
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
  let input_header = input_block.header in
  let output_header = output_block.header in

  if B32.(input_header.state_root <> output_header.state_root) then
    invalid_block input_block (Wrong_merkle_root {kind = `State; expected = output_header.state_root}) ;
  if B32.(input_header.receipts_root <> output_header.receipts_root) then
    invalid_block input_block (Wrong_merkle_root {kind = `Receipts; expected = output_header.receipts_root}) ;
  if B32.(input_header.withdrawals_root <> output_header.withdrawals_root) then
    invalid_block input_block
      (Wrong_merkle_root {kind = `Withdrawals; expected = output_header.withdrawals_root}) ;
  if B32.(input_header.transactions_root <> output_header.transactions_root) then
    invalid_block input_block
      (Wrong_merkle_root {kind = `Transactions; expected = output_header.transactions_root}) ;

  if Bloom.(input_header.logs_bloom <> output_header.logs_bloom) then
    invalid_block input_block (Wrong_logs_bloom {expected = output_header.logs_bloom}) ;

  if Gas.(input_header.gas_used <> output_header.gas_used) then
    invalid_block input_block (Wrong_gas_used {expected = output_header.gas_used}) ;

  if B32.(input_header.parent_hash <> output_header.parent_hash) then
    invalid_block input_block (Wrong_parent_hash {expected = output_header.parent_hash}) ;

  assert (input_block = output_block) ;

  ()

let process_block ?(trace = false) ~verify (world_state : WorldState.t) (block : Block.t) =
  validate_block world_state block ;

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
  let block_state = List.fold_left (process_transaction ~trace) block_state block.transactions in

  (* Process block withdrawals. *)
  let block_state = List.fold_left process_withdrawal block_state block.withdrawals in

  (* TODO coalesce destructing dead accounts here *)

  (* Compute roots and add the finalized block to the blockchain. *)
  let finalized_block = BlockState.finalize_current_block block_state in
  validate_block world_state finalized_block ;

  if verify then validate_input_block_against_output ~input_block:block ~output_block:finalized_block ;
  {block_state.world_state with history = finalized_block :: world_state.history}
