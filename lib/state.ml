open Numeric
open Chain.Ethereum
open Lens.Infix

let ( .^() ) x lens = lens.Lens.get x
let ( .^()<- ) x lens v' = lens.Lens.set v' x

module Account = struct
  type t =
    { nonce : Uint.t (* σ[a]_n *)
    ; balance : U256.t (* σ[a]_b *)
    ; storage : U256.t U256.Map.t (* σ[a]_s *)
    ; code : Bytes.t (* σ[a]_c *) }
  [@@deriving lens {submodule = true; prefix = true}]
  include TLens

  let empty = {balance = U256.zero; storage = U256.Map.empty; code = Bytes.empty; nonce = Uint.zero}
end
open Account

module StorageKey = struct
  module Impl = struct
    type t = Address.t * U256.t
    let compare (a1, w1) (a2, w2) =
      let c1 = Address.compare a1 a2 in
      if c1 = 0 then U256.compare w1 w2 else c1
  end
  include Impl
  module Set = Set.Make (Impl)
end

module Log = struct
  type t = {address : Address.t; topics : U256.t list; data : Bytes.t}
  [@@deriving lens {submodule = true; prefix = true}]

  include TLens
end

module WorldState = struct
  (** State across multiple blocks. Tracks accounts, storage, and all previously validated blocks. This
        includes the world state as per YP 4.1. *)
  type t = {history : Block.t list; accounts : Account.t Address.Map.t (* σ[a] *); chain_id : Uint.t (* β *)}
  [@@deriving lens {submodule = true; prefix = true}]

  include TLens

  let make chain_id = {history = []; accounts = Address.Map.empty; chain_id}
  type error = Invalid_transaction of Transaction.t | Invalid_block of Block.t

  let account addr = accounts |-- Address.Map.at addr |-- Option.get_or_default Account.empty

  module M = Monad.State (struct
    type nonrec t = t
  end)
end

module BlockState = struct
  (** State across multiple transactions in a single block. Tracks the world state, the gas that has been
        consumed so far by transactions in the block, logs and receipts. *)
  type t =
    { world_state : WorldState.t
    ; current_block : Block.t
    ; gas_used : Gas.t
    ; blob_gas_used : Gas.t
    ; transactions_processed : (Transaction.t * Receipt.t) list
    ; logs_bloom : Bytes256.t }
  [@@deriving lens {submodule = true; prefix = true}]

  include TLens
  let make (world_state : WorldState.t) (current_block : Block.t) =
    { world_state
    ; current_block
    ; gas_used = Gas.zero
    ; blob_gas_used = Gas.zero
    ; transactions_processed = []
    ; logs_bloom = Bytes256.zeros }

  let merge (_state : t) : unit WorldState.M.t = failwith "TODO"

  let account addr = world_state |-- WorldState.account addr

  module M = Monad.State (struct
    type nonrec t = t
  end)
end

module TransactionState = struct
  (** State within a single transaction. Tracks the initial world state, any changes to its storage,
        and variables that are internal to the transaction such as the accrued substate (YP 6.1). *)
  type t =
    { initial_world_state : WorldState.t
    ; world_state : WorldState.t
    ; current_block : Block.t
    ; current_transaction : Transaction.t
    ; transient_storage : U256.t U256.Map.t Address.Map.t
    ; accounts_created_in_current_transaction : Address.Set.t
    ; self_destruct : Address.Set.t  (** A_s *)
    ; logs : Log.t list  (** A_l *)
    ; touched : Address.Set.t  (** A_t *)
    ; refund : U256.t  (** A_r *)
    ; accessed_addresses : Address.Set.t  (** A_a *)
    ; accessed_keys : StorageKey.Set.t  (** A_K *) }
  [@@deriving lens {submodule = true; prefix = true}]

  include TLens

  let make (block_state : BlockState.t) current_transaction =
    { initial_world_state = block_state.world_state
    ; world_state = block_state.world_state
    ; current_block = block_state.current_block
    ; current_transaction
    ; transient_storage = Address.Map.empty
    ; accounts_created_in_current_transaction = Address.Set.empty
    ; self_destruct = Address.Set.empty
    ; logs = []
    ; touched = Address.Set.empty
    ; refund = U256.zero
    ; accessed_addresses = Address.Set.empty
    ; accessed_keys = StorageKey.Set.empty }

  let merge (_result : t) : unit BlockState.M.t = failwith "TODO"

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

let process_transaction (block_state : BlockState.t) (txn : Transaction.t) =
  (* Basic validity checks. *)
  (* Nonce *)
  if U256.(txn.nonce >= of_uint64 Uint64.max_uint) then failwith "Invalid transaction" ;
  (* Initcode size *)
  ( match Transaction.call_or_create txn with
  | Create {init} when Bytes.length init > 2 * Vm.max_init_code_size -> failwith "Invalid transaction"
  | _ -> () ) ;
  (* Blob hash length and versioning *)
  ( match txn.kind with
  | Blob {blob_versioned_hashes; _} ->
      if blob_versioned_hashes = [] then failwith "Invalid transaction" ;
      let check_blob_hash_version hash =
        if not (U256.byte ~index_le:31 hash = versioned_hash_version_kzg) then failwith "Invalid transaction"
      in
      List.iter check_blob_hash_version blob_versioned_hashes
  | _ -> () ) ;

  (* YP (64) *)
  let intrinsic_gas = Gas.tx_intrinsic_gas txn in
  if Gas.(intrinsic_gas > txn.gas_limit) then failwith "Invalid transaction" ;

  (* EIP-7623 *)
  let floor_gas = Gas.tx_floor_gas txn in
  if Gas.(floor_gas > txn.gas_limit) then failwith "Invalid transaction" ;

  let block = block_state.current_block in
  let header = block.header in
  let base_fee_per_gas = header.base_fee_per_gas in
  (* Calculate effective gas price and max payable gas fee depending on transaction type. Here we also check
     that the gas fee stipulated by the transaction is at least as large as the base gas fee for this block. *)
  let effective_gas_price, max_gas_fee, blob_gas_fee =
    match Transaction.fee_mechanism txn with
    | FeeMarket {max_fee_per_gas; max_priority_fee_per_gas} -> (
        if Gas.(max_fee_per_gas < max_priority_fee_per_gas) then failwith "Invalid transaction" ;
        if Gas.(max_fee_per_gas < base_fee_per_gas) then failwith "Invalid transaction" ;
        let priority_fee_per_gas = Gas.(min max_priority_fee_per_gas (max_fee_per_gas - base_fee_per_gas)) in
        let effective_gas_price = Gas.(priority_fee_per_gas + base_fee_per_gas) in
        let max_gas_fee = Gas.(txn.gas_limit * max_fee_per_gas) in
        match txn.kind with
        | Blob {max_fee_per_blob_gas; blob_versioned_hashes; _} ->
            let max_fee_per_blob_gas = U256.to_unbounded max_fee_per_blob_gas in
            let blob_gas_price = Gas.block_blob_gas_price (U64.to_unbounded header.excess_blob_gas) in
            if Gas.(max_fee_per_blob_gas < blob_gas_price) then failwith "Invalid transaction" ;
            let total_blob_gas = Gas.(gas_per_blob * ~$(List.length blob_versioned_hashes)) in
            let max_blob_gas_fee = Gas.(total_blob_gas * max_fee_per_blob_gas) in
            let blob_gas_fee = Gas.(total_blob_gas * blob_gas_price) in
            (effective_gas_price, Gas.(max_gas_fee + max_blob_gas_fee), blob_gas_fee)
        | _ -> (effective_gas_price, max_gas_fee, Gas.zero) )
    | Legacy {gas_price} ->
        if Gas.(gas_price < base_fee_per_gas) then failwith "Invalid transaction" ;
        (gas_price, Gas.(txn.gas_limit * gas_price), Gas.zero)
  in

  let sender = Transaction.sender block_state.world_state.chain_id txn in
  let sender_account = block_state.world_state |. WorldState.account sender in
  if Uint.(sender_account.nonce <> U256.to_unbounded txn.nonce) then failwith "Invalid transaction" ;
  if Uint.(U256.to_unbounded sender_account.balance < max_gas_fee + U256.to_unbounded txn.value) then
    failwith "Invalid transaction" ;
  if sender_account.code <> Bytes.empty && not (Delegation.is_valid_delegation sender_account.code) then
    failwith "Invalid transaction" ;

  let effective_gas_fee = Gas.(txn.gas_limit * effective_gas_price) in
  let total_fee = Gas.(effective_gas_fee + blob_gas_fee) in
  if total_fee > U256.to_unbounded sender_account.balance then failwith "Invalid transaction" ;
  let total_fee = U256.of_unbounded_exn total_fee in

  (* pay gas and blob fees, increase nonce *)
  let block_state =
    block_state.^(BlockState.account sender) <-
      { sender_account with
        balance = U256.(sender_account.balance - total_fee)
      ; nonce = Uint.(sender_account.nonce + one) }
  in

  let available_gas = Gas.(txn.gas_limit - intrinsic_gas) in

  failwith "TODO"

module Host (Vm : sig
  val execute : Evmc.Message.t -> Bytes.t -> Evmc.Result.t TransactionState.M.t
end) =
struct
  open Account
  open WorldState
  open TransactionState
  include TransactionState.M

  let move_ether sender recipient amount =
    let$ () =
      update_field
        (account sender |-- balance)
        (fun eth ->
          (* TODO: check this assertion on the host side. *)
          assert (U256.(eth >= amount)) ;
          U256.(eth - amount) )
    in
    update_field (account recipient |-- balance) (fun eth -> U256.(eth + amount))

  let account_exists addr = Option.is_some <$> !(world_state |-- accounts |-- Address.Map.at addr)

  let get_storage addr key =
    !(account addr |-- Account.storage |-- U256.Map.at key |-- Option.get_or_default U256.zero)

  let set_storage addr key v =
    let$ () = account addr |-- storage |-- U256.Map.at key := Some v in
    (* TODO: make this accurate. *)
    return Evmc.StorageStatus.Assigned

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

  (* YP (95) *)
  let address_for ~sender ~create2_salt ~code =
    let$ nonce = !(account sender |-- nonce) in
    return
      (Address.of_u256_truncating
         (Crypto.keccak_256
            ( match create2_salt with
            | None -> Rlp.(encode (List [Address.to_rlp sender; Uint.to_rlp nonce]))
            | Some salt ->
                Bytes.make 1 '\xff'
                ^ Address.to_bytes_be sender
                ^ U256.to_bytes_be salt
                ^ U256.to_bytes_be (Crypto.keccak_256 code) ) ) )

  let process_create (msg : Evmc.Message.t) =
    let$ create_address =
      (* Note that we use the sender nonce _before_ increasing it *)
      address_for ~sender:msg.sender
        ~create2_salt:(if msg.kind = Create2 then Some msg.create2_salt else None)
        ~code:msg.code
    in
    let$ pre_existent_account = !(account create_address) in
    if Uint.(pre_existent_account.nonce <> zero) || pre_existent_account.code <> Bytes.empty then
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
      let$ () = account create_address |-- storage := U256.Map.empty in
      let$ () = account create_address |-- nonce := Uint.one in

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
    return
      Evmc.TxContext.
        { tx_gas_price = U256.zero
        ; tx_origin = Address.zero
        ; block_coinbase = Address.zero
        ; block_number = 0L
        ; block_timestamp = 0L
        ; block_gas_limit = 99999L
        ; block_prev_randao = U256.zero
        ; chain_id = U256.zero
        ; block_base_fee = U256.zero
        ; blob_base_fee = U256.zero
        ; blob_hashes = []
        ; initcodes = [] }

  let get_block_hash i =
    (* This host is not backed by an actual block database, so we return the hash of i which is enough for
         testing *)
    return (Crypto.keccak_256 U256.(to_bytes_be (of_uint64 i)))

  let emit_log address ~(data : Bytes.t) ~(topics : U256.t list) =
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
    |-- Option.get_or_default U256.Map.empty
    |-- U256.Map.at key
    |-- Option.get_or_default U256.zero

  let get_transient_storage addr key = !(transient_storage addr key)

  let set_transient_storage addr key value = transient_storage addr key := value
end
