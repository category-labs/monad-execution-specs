open Numeric
open Byte_string
open Chain.Ethereum
open Lens.Infix

let ( .^() ) x lens = lens.Lens.get x
let ( .^()<- ) x lens v' = lens.Lens.set v' x
let ( .^$()<- ) x lens f = Lens.modify lens f x

module WorldState = struct
  (** State across multiple blocks. Tracks accounts, storage, and all previously validated blocks. This
      includes the world state as per YP 4.1. *)
  type t =
    { history : Block.t list
    ; accounts : Account.t Address.Map.t (* σ[a], implicitly realizes YP (12) *)
    ; next_emptying_transaction_block : Uint.t Address.Map.t
          (** [next_emptying_transaction_block] maps every address to the next block number in which a
              transaction from it would be emptying. The counter for an account is bumped by
              {!Reserve_balance.execution_consensus_delay} every time the account submits a transaction or
              appears in a valid delegation. *)
    }
  [@@deriving lens {submodule = true; prefix = true}]

  include TLens

  let empty = {history = []; accounts = Address.Map.empty; next_emptying_transaction_block = Address.Map.empty}

  (* EIP-161 deletion of touched empty accounts is done here, which frees the implementation from keeping
     track of touched accounts. Note that the Ethereum executable spec uses a similar approach by intercepting
     any state updates to an account and deleting it if it is empty after the update. *)
  let account_opt ?(keep_empty = false) addr =
    let Lens.{get; set} = accounts |-- Address.Map.at addr in
    let set =
      if keep_empty then set
      else fun acct state ->
        let acct = match acct with Some acct when Account.is_empty acct -> None | _ -> acct in
        set acct state
    in
    Lens.{get; set}

  (** [account addr] provides a lens into the current state of the account for [addr]. Addresses that do not
      correspond to entries in the underlying map are considered to correspond to empty accounts. Conversely,
      setting the account of an address to the empty account deletes it from the underlying map. Since
      non-existent accounts are treated as empty, we do not make a distinction between empty (YP (14)) and
      dead (YP (15)) accounts. *)
  let account ?(keep_empty = false) addr =
    account_opt ~keep_empty addr |-- Option.get_or_default Account.empty

  let next_emptying_transaction_block_for addr =
    next_emptying_transaction_block |-- Address.Map.at addr |-- Option.get_or_default Uint.zero

  let state_root state =
    let mpt =
      state.accounts
      |> Address.Map.to_seq
      (* YP (10) *)
      |> Seq.map (fun (addr, acc) ->
          (* YP (11) *)
          let address_hash = Crypto.keccak_256 (Address.to_bytes addr) in
          (B32.to_bytes address_hash, Rlp.encode (Account.to_rlp acc)) )
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

  let account ?(keep_empty = false) addr = world_state |-- WorldState.account ~keep_empty addr
  let account_opt ?(keep_empty = false) addr = world_state |-- WorldState.account_opt ~keep_empty addr

  (** [finalize_current_block bs] returns [bs.current_block] with its header updated to reflect the new state
      after block execution. This will overwrite header fields [parent_hash], [state_root], [transactions_root],
      [receipts_root], [withdrawals_root], [logs_bloom], [requests_hash], [gas_used] and [blob_gas_used]. *)
  let finalize_current_block (block_state : t) : Block.t =
    (* YP (46) *)
    let parent_hash = Block.hash (List.hd block_state.world_state.history) in

    (* The equations in YP (35) are enforced by the assignments below. *)

    (* YP (183), YP (184). This also enforces the condition in YP (39) for the subsequent block, that is,
       this block header's state root will be equal to the root of the initial state when processing the next
       block.
       Note that YP (39) is only enforced by this assignment, therefore any state changes that are
       triggered by an external call (test frameworks, fuzzer harness, loading a genesis state) may break
       this invariant. *)
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

    (* Monad does not implement EIP-6110 or EIP-7002, therefore the requests list will always be empty. The
       requests hash is computed here as per https://eips.ethereum.org/EIPS/eip-7685#block-header for
       completeness. *)
    let requests_hash =
      block_state.requests
      |> List.filter (fun req -> Bytes.length req > 1)
      |> List.stable_sort (fun r_a r_b -> Char.compare r_a.[0] r_b.[0])
      |> Bytes.concat Bytes.empty
      |> Crypto.sha_256
    in

    (* Gas used was tracked incrementally, instead of being computed from the last transaction receipt as
       it is in YP (181) *)
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
      ; blob_gas_used
      ; parent_hash }
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
      and variables that are internal to the transaction such as the accrued substate (YP (62)). *)
  type t =
    { initial_world_state : WorldState.t
    ; world_state : WorldState.t
    ; current_block : Block.t
    ; transient_storage : B32.t B32.Map.t Address.Map.t
    ; accounts_created_in_current_transaction : Address.Set.t
    ; tx_origin : Address.t
    ; tx_gas_price : Gas.t
    ; self_destruct : Address.Set.t  (** A_s *)
    ; logs : Log.t list  (** A_l, in reverse order *)
    ; refund : U256.t  (** A_r *)
    ; accessed_addresses : Address.Set.t  (** A_a *)
    ; accessed_keys : StorageKey.Set.t  (** A_K *) }
  [@@deriving lens {submodule = true; prefix = true}]

  include TLens

  (* Empty transaction state, useful for running EVM tests against it. *)
  let empty =
    let world_state = WorldState.empty in
    let current_block = Block.{header = Header.empty; transactions = []; withdrawals = []; ommers = []} in
    (* YP (63), except for the accessed address set Aₐ = π, which is initialized by initialize_access_sets. *)
    { initial_world_state = world_state
    ; world_state
    ; current_block
    ; transient_storage = Address.Map.empty
    ; accounts_created_in_current_transaction = Address.Set.empty
    ; tx_origin = Address.zero
    ; tx_gas_price = Gas.zero
    ; self_destruct = Address.Set.empty
    ; logs = []
    ; refund = U256.zero
    ; accessed_addresses = Address.Set.empty
    ; accessed_keys = StorageKey.Set.empty }

  let make (block_state : BlockState.t) (sender : Address.t) tx =
    let tx_gas_price =
      (* If this option was None, the transaction would have already been discarded as invalid. *)
      Option.get (Gas.tx_effective_gas_price block_state.current_block.header.base_fee_per_gas tx)
    in
    { empty with
      initial_world_state = block_state.world_state
    ; world_state = block_state.world_state
    ; current_block = block_state.current_block
    ; transient_storage = Address.Map.empty
    ; accounts_created_in_current_transaction = Address.Set.empty
    ; tx_origin = sender
    ; tx_gas_price }

  let account ?(keep_empty = false) addr = world_state |-- WorldState.account ~keep_empty addr

  let initialize_access_sets
      (tx : Transaction.t) (transaction_state : t) (precompile_addresses : Address.Set.t) =
    let open Transaction.Access in
    let sender = transaction_state.tx_origin in
    let access_list = Transaction.access_list tx in
    (* YP (78). *)
    let accessed_keys =
      List.to_seq access_list
      |> Seq.flat_map (fun acc -> List.to_seq acc.storage_keys |> Seq.map (fun k -> (acc.address, k)))
      |> StorageKey.Set.of_seq
    in
    (* The Eₐ terms in YP (80) *)
    let access_list_addresses =
      List.to_seq access_list |> Seq.map (fun acc -> acc.address) |> Address.Set.of_seq
    in
    (* The Tₜ term in YP (79), expanded to warm any delegation target as per EIP-7702. *)
    let target_addresses =
      match Transaction.call_or_create tx with
      | Create _ -> Address.Set.empty
      | Call {to_; _} -> (
        match Delegation.get_delegated_address transaction_state.^(account to_).code with
        | None -> Address.Set.singleton to_
        | Some delegated -> Address.Set.of_list [to_; delegated] )
    in
    (* YP (80), joined with Tₜ and the pre-existing access set containing any already-processed EIP-7702
       authorizations. *)
    let accessed_addresses =
      List.fold_left Address.Set.union Address.Set.empty
        [ access_list_addresses
        ; precompile_addresses
        ; Address.Set.singleton sender
        ; Address.Set.singleton transaction_state.current_block.header.beneficiary
        ; target_addresses
        ; transaction_state.accessed_addresses ]
    in
    {transaction_state with accessed_addresses; accessed_keys}

  module M = Monad.State (struct
    type nonrec t = t
  end)
end

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

  (* YP (93) *)
  let process_create (msg : Evmc.Message.t) =
    let$ sender_nonce = !(account msg.sender |-- nonce) in
    (* YP (94) *)
    let create_address =
      (* Subsumes YP (92) *)
      let create2 : Address.create2_params option =
        if msg.kind = Create2 then Some Address.{salt = msg.create2_salt; initcode = msg.input_data} else None
      in
      Address.of_contract_creation ~sender:msg.sender ~nonce:sender_nonce ~create2
    in
    (* YP (97) *)
    let$ () = touch_account create_address in
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
      let$ () = account create_address |-- storage := B32.Map.empty in
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
