open Numeric
open Byte_string
open Chain.Ethereum
open Lens.Infix

let ( .^() ) x lens = lens.Lens.get x
let ( .^()<- ) x lens v' = lens.Lens.set v' x
let ( .^$()<- ) x lens f = Lens.modify lens f x

module WorldState = struct
  (** State across multiple blocks. Tracks accounts, storage, and all previously validated blocks. This
      includes the world state as per YP 4.1.
   *)
  type t =
    { history : Block.t list
    ; accounts : Account.t Address.Map.t (* σ[a] *)
    ; next_emptying_transaction_block : Uint.t Address.Map.t
          (** [next_emptying_transaction_block] maps every address to the next block number in which a
        transaction from it would be emptying. The counter for an account is bumped by
        {!Reserve_balance.execution_consensus_delay} every time the account submits a transaction or appears
        in a valid delegation. *)
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
  let account ?(keep_empty = false) addr =
    account_opt ~keep_empty addr |-- Option.get_or_default Account.empty

  let next_emptying_transaction_block_for addr =
    next_emptying_transaction_block |-- Address.Map.at addr |-- Option.get_or_default Uint.zero

  let state_root state =
    let mpt =
      state.accounts
      |> Address.Map.to_seq
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

  (** [finalize_current_block bs] returns [bs.current_block] with the roots updated to reflect the
      new state after block execution. If the block already carries its MPT roots are already calculated,
      they are overwritten. *)
  let finalize_current_block (block_state : t) : Block.t =
    (* YP (46) *)
    let parent_hash = Block.hash (List.hd block_state.world_state.history) in

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
      |> Crypto.sha_256
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
    ; logs : Log.t list  (** A_l, in reverse order *)
    ; refund : U256.t  (** A_r *)
    ; accessed_addresses : Address.Set.t  (** A_a *)
    ; accessed_keys : StorageKey.Set.t  (** A_K *) }
  [@@deriving lens {submodule = true; prefix = true}]

  include TLens

  let pre_compiled_contract_addresses = Address.Map.keys Precompiles.precompiles

  (* Empty transaction state, useful for running EVM tests against it. *)
  let empty =
    let world_state = WorldState.empty in
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
    ; tx_gas_price
    ; self_destruct = Address.Set.empty
    ; logs = []
    ; refund = U256.zero }

  let account ?(keep_empty = false) addr = world_state |-- WorldState.account ~keep_empty addr

  (* YP (77). *)
  let initialize_access_sets (tx : Transaction.t) (transaction_state : t) =
    let open Transaction.Access in
    let sender = transaction_state.tx_origin in
    let access_list = Transaction.access_list tx in
    (* YP (78). *)
    let accessed_keys =
      List.to_seq access_list
      |> Seq.flat_map (fun acc -> List.to_seq acc.storage_keys |> Seq.map (fun k -> (acc.address, k)))
      |> StorageKey.Set.of_seq
    in
    (* YP (79), YP (80). *)
    let access_list_addresses =
      List.to_seq access_list |> Seq.map (fun acc -> acc.address) |> Address.Set.of_seq
    in
    let target_addresses =
      match Transaction.call_or_create tx with
      | Call {to_; _} -> (
        match Delegation.get_delegated_address transaction_state.^(account to_).code with
        | None -> Address.Set.singleton to_
        | Some delegated -> Address.Set.of_list [to_; delegated] )
      | Create _ ->
          let sender_nonce = transaction_state.^(account sender).nonce in
          Address.Set.singleton (Address.of_contract_creation ~sender ~nonce:sender_nonce ~create2:None)
    in
    let accessed_addresses =
      List.fold_left Address.Set.union Address.Set.empty
        [ access_list_addresses
        ; pre_compiled_contract_addresses
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
