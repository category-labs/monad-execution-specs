open Numeric
open Byte_string
open Chain.Ethereum
open Lens.Infix

let ( .^() ) x lens = lens.Lens.get x
let ( .^()<- ) x lens v' = lens.Lens.set v' x

module WorldState = struct
  (** State across multiple blocks. Tracks accounts, storage, and all previously validated blocks. This
      includes the world state as per YP 4.1. *)
  type t = {history : Block.t list; accounts : Account.t Address.Map.t (* σ[a] *); chain_id : Uint.t (* β *)}
  [@@deriving lens {submodule = true; prefix = true}]

  include TLens

  let make chain_id = {history = []; accounts = Address.Map.empty; chain_id}

  let account addr = accounts |-- Address.Map.at addr |-- Option.get_or_default Account.empty
  let account_opt addr = accounts |-- Address.Map.at addr

  let state_root state =
    let mpt =
      state.accounts
      |> Address.Map.to_seq
      |> Seq.filter_map (fun (addr, acc) ->
          if Account.is_empty acc then None
          else
            (* YP (11) *)
            let address_hash = Crypto.keccak_256 (Address.to_bytes addr) in
            Some (B32.to_bytes address_hash, Rlp.encode (Account.to_rlp acc)) )
      |> Mpt.of_seq
    in
    mpt.root_hash

  let dump_accounts ws =
    Address.Map.iter
      (fun addr acc ->
        Format.eprintf "%s: %s\n" (Address.to_hex_string addr)
          (Yojson.Safe.pretty_to_string (Account.to_yojson acc)) )
      ws.accounts
end

module BlockState = struct
  (** State across multiple transactions in a single block. Tracks the world state, the gas that has been
      consumed so far by transactions in the block, logs and receipts. *)
  type t =
    { world_state : WorldState.t
    ; current_block : Block.t
    ; gas_used : Gas.t
    ; transactions_processed : (Transaction.t * Receipt.t) list
    ; withdrawals_processed : Withdrawal.t list
    ; requests : Bytes.t list (* EIP-7685 execution layer requests *) }
  [@@deriving lens {submodule = true; prefix = true}]

  include TLens
  let make (world_state : WorldState.t) (current_block : Block.t) =
    { world_state
    ; current_block
    ; gas_used = Gas.zero
    ; transactions_processed = []
    ; withdrawals_processed = []
    ; requests = [] }

  let account addr = world_state |-- WorldState.account addr
  let account_opt addr = world_state |-- WorldState.account_opt addr

  let transfer_money_and_delete_if_empty (block_state : t) (amount : U256.t) (recipient : Address.t) =
    let updated_balance = U256.(block_state.^(account recipient).balance + amount) in
    if U256.(updated_balance = zero) then block_state.^(account_opt recipient) <- None
    else block_state.^(account recipient |-- Account.balance) <- updated_balance

  (** {!finalize_current_block bs} returns {!bs.current_block} with the roots updated to reflect the
      new state after block execution. If the block already carries its MPT roots are already calculated,
      they are overwritten. *)
  let finalize_current_block (block_state : t) : Block.t =
    (* YP (35) *)
    let state_root = WorldState.state_root block_state.world_state in
    let transactions_root =
      ( block_state.transactions_processed
      |> List.to_seq
      |> Seq.map (fun (tx, _) -> Transaction.encode tx)
      |> Mpt.of_seq_i )
        .root_hash
    in
    let receipts_root =
      ( block_state.transactions_processed
      |> List.to_seq
      |> Seq.map (fun (_, receipt) -> Receipt.encode receipt)
      |> Mpt.of_seq_i )
        .root_hash
    in
    let withdrawals_root =
      ( block_state.withdrawals_processed
      |> List.to_seq
      |> Seq.map (fun w -> Withdrawal.encode w)
      |> Mpt.of_seq_i )
        .root_hash
    in
    let logs_bloom =
      block_state.transactions_processed
      |> List.to_seq
      |> Seq.map (fun (_, receipt) -> receipt.Receipt.bloom)
      |> Bloom.union
    in

    (* See https://eips.ethereum.org/EIPS/eip-7685#block-header *)
    let requests_hash =
      block_state.requests
      |> List.filter (fun req -> Bytes.length req > 1)
      |> List.stable_sort (fun r_a r_b -> Char.compare r_a.[0] r_b.[0])
      |> Bytes.concat Bytes.empty
      |> Crypto.keccak_256
    in

    let gas_used = block_state.gas_used in
    (* Monad does not support Blob transactions. *)
    let blob_gas_used = U64.zero in

    let header =
      { block_state.current_block.header with
        state_root
      ; transactions_root
      ; receipts_root
      ; logs_bloom
      ; withdrawals_root
      ; requests_hash
      ; gas_used
      ; blob_gas_used }
    in
    {block_state.current_block with header}
end

module TransactionState = struct
  module StorageKey = struct
    module Impl = struct
      type t = Address.t * B32.t
      let compare (a1, w1) (a2, w2) =
        let c1 = Address.compare a1 a2 in
        if c1 = 0 then B32.compare w1 w2 else c1
    end
    include Impl
    module Set = Set.Make (Impl)
  end

  (** State within a single transaction. Tracks the initial world state, any changes to its storage,
      and variables that are internal to the transaction such as the accrued substate (YP 6.1). *)
  type t =
    { initial_world_state : WorldState.t
    ; world_state : WorldState.t
    ; current_block : Block.t
    ; transient_storage : B32.t B32.Map.t Address.Map.t
    ; accounts_created_in_current_transaction : Address.Set.t
    ; tx_origin : Address.t
    ; tx_gas_price : Gas.t
    ; self_destruct : Address.Set.t  (** A_s *)
    ; logs : Log.t list  (** A_l *)
    ; touched : Address.Set.t  (** A_t *)
    ; refund : U256.t  (** A_r *)
    ; accessed_addresses : Address.Set.t  (** A_a *)
    ; accessed_keys : StorageKey.Set.t  (** A_K *) }
  [@@deriving lens {submodule = true; prefix = true}]

  include TLens

  let pre_compiled_contract_addresses = Address.Set.of_list [] (* TODO *)

  let make (block_state : BlockState.t) sender tx access_list =
    let open BlockState in
    let open Transaction.Access in
    let access_list_addresses =
      List.to_seq access_list |> Seq.map (fun acc -> acc.address) |> Address.Set.of_seq
    in
    let target_addresses =
      match Transaction.call_or_create tx with
      | Call {to_; _} -> (
        match Delegation.get_delegated_address block_state.^(account sender).code with
        | None -> Address.Set.singleton to_
        | Some delegated -> Address.Set.of_list [to_; delegated] )
      | Create _ ->
          let nonce = block_state.^(account sender).nonce in
          Address.Set.singleton (Address.of_contract_creation ~sender ~nonce ~create2:None)
    in
    let accessed_addresses =
      List.fold_left Address.Set.union Address.Set.empty
        [ access_list_addresses
        ; pre_compiled_contract_addresses
        ; Address.Set.singleton sender
        ; target_addresses ]
    in
    let accessed_keys =
      List.to_seq access_list
      |> Seq.flat_map (fun acc -> List.to_seq acc.storage_keys |> Seq.map (fun k -> (acc.address, k)))
      |> StorageKey.Set.of_seq
    in
    { initial_world_state = block_state.world_state
    ; world_state = block_state.world_state
    ; current_block = block_state.current_block
    ; transient_storage = Address.Map.empty
    ; accounts_created_in_current_transaction = Address.Set.empty
    ; tx_origin = sender
    ; tx_gas_price = block_state.current_block.header.base_fee_per_gas
    ; self_destruct = Address.Set.empty
    ; logs = []
    ; touched = Address.Set.empty
    ; refund = U256.zero
    ; accessed_addresses
    ; accessed_keys }

  let account addr = world_state |-- WorldState.account addr

  module M = Monad.State (struct
    type nonrec t = t
  end)
end

module BlockOutput = struct
  type t
end

type validation_error = Invalid_block of Block.t | Invalid_transaction of Transaction.t
module Validation = Monad.Result (struct
  type t = validation_error
end)

let versioned_hash_version_kzg = '\x01'

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

module Host (Vm : sig
  val execute : Evmc.Message.t -> Bytes.t -> Evmc.Result.t TransactionState.M.t
end) =
struct
  open Account
  open WorldState
  open TransactionState
  include TransactionState.M

  let dump_account addr =
    let$ acc = !(account addr) in
    Format.eprintf "%s: %s\n" (Address.to_hex_string addr)
      (Yojson.Safe.pretty_to_string (Account.to_yojson acc)) ;
    return ()

  let move_ether sender recipient amount =
    let$ () =
      update_field
        (account sender |-- balance)
        (fun eth ->
          assert (U256.(eth >= amount)) ;
          U256.(eth - amount) )
    in
    let$ () = update_field (account recipient |-- balance) (fun eth -> U256.(eth + amount)) in
    return ()

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
    let$ () = account addr |-- storage |-- B32.Map.at key := Some v in
    let zero u = B32.(u = zeros) in
    let x u = B32.(u <> zeros && u = o) in
    let y u = B32.(u <> zeros && u = c) in
    let z u = B32.(u <> zeros && u = v) in
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
    let$ code = !(account addr |-- code) in
    return (Crypto.keccak_256 code)

  let copy_code addr ~offset ~size =
    let$ code = !(account addr |-- code) in
    return (Bytes.sub_with_zero_padding code offset size)

  let selfdestruct ~address ~beneficiary =
    let$ account_balance = !(account address |-- balance) in
    let$ () = move_ether address beneficiary account_balance in

    let$ created_in_current_tx = Address.Set.mem address <$> !accounts_created_in_current_transaction in
    if created_in_current_tx then
      (* Delete the account as per EIP-6780 *)
      let$ alive_before_selfdestruct = account_exists address in
      let$ () = world_state |-- accounts |-- Address.Map.at address := None in
      return alive_before_selfdestruct
    else return false

  let should_transfer (msg : Evmc.Message.t) =
    U256.(msg.value > zero)
    && (match msg.kind with Call | CallCode | Create | Create2 -> true | DelegateCall -> false)
    && not msg.static

  let process_call (msg : Evmc.Message.t) =
    let$ () = when_ (should_transfer msg) (move_ether msg.sender msg.recipient msg.value) in
    (* TODO: check whether it's a precompile *)
    Vm.execute msg msg.code

  let process_create (msg : Evmc.Message.t) =
    let$ sender_nonce = !(account msg.sender |-- nonce) in
    let create_address =
      (* Note that we use the sender nonce _before_ increasing it *)
      Address.of_contract_creation ~sender:msg.sender ~nonce:sender_nonce
        ~create2:(if msg.kind = Create2 then Some {salt = msg.create2_salt; code = msg.code} else None)
    in
    let$ pre_existent_account = !(account create_address) in
    if U256.(pre_existent_account.nonce <> zero) || pre_existent_account.code <> Bytes.empty then
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
      let$ () = account create_address |-- nonce := U256.one in

      (* Ether, if any, is transferred by process_call *)
      let$ result : Evmc.Result.t = process_call msg in
      match result.status_code with
      | Success ->
          let contract_code = result.output_data in
          let contract_length = Bytes.length contract_code in
          let contract_code_gas = Uint.(of_int contract_length * Gas.code_deposit_per_byte) in
          if
            (contract_length = 0 && contract_code.[0] = '\xef')
            || Uint.(contract_code_gas > of_int64 result.gas_left)
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

  let call (msg : Evmc.Message.t) =
    let$ initial_state = get in
    let$ result =
      match msg.kind with
      | Call | DelegateCall | CallCode -> process_call msg
      | Create | Create2 -> process_create msg
    in
    let$ () = when_ (result.status_code <> Success) (put initial_state) in
    return result

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
        ; chain_id = U256.of_uint_exn state.world_state.chain_id
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

  let get_block_hash i =
    (* This host is not backed by an actual block database, so we return the hash of i which is enough for
         testing *)
    return (Crypto.keccak_256 U256.(to_repr_bytes (of_uint64 i)))

  let emit_log address ~(data : Bytes.t) ~(topics : B32.t list) =
    let log : Log.t = {address; topics; data} in
    update_field logs (fun logs -> log :: logs)

  let touch_account addr = M.update_field accessed_addresses (Address.Set.add addr)

  let touch_storage addr key =
    M.(
      let$ () = touch_account addr in
      update_field accessed_keys (StorageKey.Set.add (addr, key)) )

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

let process_message (msg : Evmc.Message.t) (transaction_state : TransactionState.t) =
  let module H =
    Evmc.Instantiate (TransactionState.M) (Host)
      (Vm.Make (struct
        let trace = true
      end))
  in
  H.Host.call msg transaction_state

let process_authorization transaction_state (authorization : Transaction.Authorization.t) : TransactionState.t
    =
  let open TransactionState in
  let authority = Transaction.Authorization.authority authorization in
  let transaction_state =
    { transaction_state with
      accessed_addresses = Address.Set.add authority transaction_state.accessed_addresses }
  in
  let Account.{code; nonce; _} = transaction_state.^(account authority) in
  (* If the authorization is valid, update the code of the authority to the delegation indicator. *)
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

  let sender = Transaction.sender block_state.world_state.chain_id tx in
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
    let transaction_state = TransactionState.make block_state sender tx (Transaction.access_list tx) in

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
