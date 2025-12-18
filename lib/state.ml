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

  let pre_compiled_contract_addresses = Address.Map.keys Precompiles.precompiles

  (* Empty transaction state, useful for running EVM tests against it. *)
  let empty =
    let world_state = WorldState.make Uint.zero in
    let current_block = Block.{header = Header.empty; transactions = []; withdrawals = []; ommers = []} in
    { initial_world_state = world_state
    ; world_state
    ; current_block
    ; transient_storage = Address.Map.empty
    ; accounts_created_in_current_transaction = Address.Set.empty
    ; tx_origin = Address.zero
    ; tx_gas_price = Gas.zero
    ; self_destruct = Address.Set.empty
    ; logs = []
    ; touched = Address.Set.empty
    ; refund = U256.zero
    ; accessed_addresses = Address.Set.empty
    ; accessed_keys = StorageKey.Set.empty }

  let make (block_state : BlockState.t) tx =
    let open BlockState in
    let open Transaction.Access in
    let sender = Option.get (Transaction.sender block_state.world_state.chain_id tx) in
    let access_list = Transaction.access_list tx in
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
          let sender_nonce = block_state.^(account sender).nonce in
          Address.Set.singleton (Address.of_contract_creation ~sender ~nonce:sender_nonce ~create2:None)
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
    ; tx_gas_price = Gas.tx_effective_gas_price block_state.current_block.header.base_fee_per_gas tx
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

module Host (Vm : sig
  val execute : Evmc.Message.t -> Bytes.t -> Evmc.Result.t TransactionState.M.t
end) =
struct
  open Account.TLens
  open WorldState
  open TransactionState
  include M

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
    let$ () = account addr |-- storage |-- B32.Map.at key := if B32.(v = zeros) then None else Some v in
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

  let increase_nonce (addr : Address.t) =
    update_field (account addr |-- nonce) (fun nonce -> U256.(nonce + one))

  let process_call (msg : Evmc.Message.t) =
    assert (msg.kind = Call || msg.kind = CallCode || msg.kind = DelegateCall) ;
    let$ () = when_ (should_transfer msg) (move_ether msg.sender msg.recipient msg.value) in
    match Address.Map.find_opt msg.recipient Precompiles.precompiles with
    | Some precompile when not msg.delegated -> return (precompile msg)
    | Some _ ->
        (* Delegated calls to precompiles are executed as if the corresponding contract was empty, as per EIP-7702. *)
        Vm.execute msg Bytes.empty
    | None ->
        let$ code =
          (* If the message provides the code to be called then it's executed, otherwise it's fetched from
             the provided code_address. *)
          if Bytes.(msg.code = empty) then !(account msg.code_address |-- code) else return msg.code
        in
        Vm.execute msg code

  let process_create (msg : Evmc.Message.t) =
    let$ is_eoa_transaction =
      let$ code = !(account msg.sender |-- code) in
      return (code = Bytes.empty || (Delegation.is_valid_delegation code && not msg.delegated))
    in
    let$ () =
      (* The execution loop is responsible for updating the nonce when executing a transaction. It is only
         incremented here if contract creation was triggered by CREATE or CREATE2. *)
      when_ (not is_eoa_transaction)
        (update_field (account msg.sender |-- nonce) (fun nonce -> U256.(nonce + one)))
    in
    let$ sender_nonce = !(account msg.sender |-- nonce) in
    let create_address =
      Address.of_contract_creation ~sender:msg.sender ~nonce:sender_nonce
        ~create2:(if msg.kind = Create2 then Some {salt = msg.create2_salt; initcode = msg.input_data} else None)
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
      let$ () = move_ether msg.sender create_address msg.value in

      let$ result = Vm.execute msg msg.input_data in

      match result.status_code with
      | Success ->
          let contract_code = result.output_data in
          let contract_length = Bytes.length contract_code in
          let contract_code_gas = Uint.(of_int contract_length * Gas.code_deposit_per_byte) in
          if
            (contract_length > 0 && contract_code.[0] = '\xef')
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
      | _ ->
         return result

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
