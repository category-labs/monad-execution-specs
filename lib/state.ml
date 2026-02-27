(** The state model used by the interpreter and block executor, as three record types nested by lifetime:
    + {!WorldState.t} represents the blockchain state across multiple blocks, and includes the account
    state σ as well as block history and the emptying transaction counter.
    + {!BlockState.t} represents the state across multiple transactions within a block, and accumulates
    gas used and transaction results.
    + {!TransactionState.t} represents the state within a single transaction, and manages the values
    that are internal to the transaction such as accrued substate and transient storage.
 *)

open Numeric
open Byte_string
open Chain.Ethereum
open Lens.Infix

let ( .^() ) x lens = lens.Lens.get x
let ( .^()<- ) x lens v' = lens.Lens.set v' x
let ( .^$()<- ) x lens f = Lens.modify lens f x

module Accounts =
  Mpt.Make
    (struct
      let hash_keys = true
    end)
    (Address)
    (struct
      include Account
      let commit acc = merkleized acc
      let to_bytes acc = Rlp.encode (to_rlp acc)
    end)

module WorldState = struct
  (** State across multiple blocks. Tracks accounts, storage, and all previously validated blocks. This
      includes the world state as per YP 4.1. *)
  type t =
    { history : Block.t list
    ; accounts : Accounts.t (* σ[a], implicitly realizes YP (12) *)
    ; next_emptying_transaction_block : Uint.t Address.Map.t
          (** [next_emptying_transaction_block] maps every address to the next block number in which a
              transaction from it would be emptying. The counter for an account is bumped by
              {!Reserve_balance.execution_consensus_delay} every time the account submits a transaction or
              appears in a valid delegation. *)
    }
  [@@deriving lens {submodule = true; prefix = true}]

  include TLens

  let empty = {history = []; accounts = Accounts.empty; next_emptying_transaction_block = Address.Map.empty}

  (** [account_opt addr] provides a lens into the current state of the account for [addr]. Addresses that do
      not correspond to entries in the underlying map correspond to [None].
      EIP-161 deletion of touched empty accounts is done here, which frees the implementation from keeping
     track of touched accounts. Note that the Ethereum executable spec uses a similar approach by intercepting
     any state updates to an account and deleting it if it is empty after the update. *)
  let account_opt ?(keep_empty = false) addr =
    let Lens.{get; set} = accounts |-- Accounts.at addr in
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
      dead (YP (15)) accounts.
      As with {!account_opt}, updating an account to be empty removes it from the underlying map. *)
  let account ?(keep_empty = false) addr =
    account_opt ~keep_empty addr |-- Option.get_or_default Account.empty

  (** [next_emptying_transaction_block_for addr] returns the block number of the next block in which a
      transaction from account [addr] would be considered emptying. *)
  let next_emptying_transaction_block_for addr =
    next_emptying_transaction_block |-- Address.Map.at addr |-- Option.get_or_default Uint.zero

  (** [state_root state] computes the state root of the current account map. This involves computing the
      storage roots of every account in the state, which is very expensive. *)
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

  (** [initialize_access_sets tx state p_addr] extends the set of accessed addresses and keys of [state] with
      the transaction sender and recipient (if any), the addresses and keys in the transaction's access list,
      the delegation target of the recipient (if any), the block's beneficiary and the given list of precompiled
      contract addresses.
      The state's accessed addresses are not overwritten but extended, so any addresses that were accessed before
      this call will remain accessed. *)
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
       authorizations. TODO: it might be cleaner to pass the authorities to this function and have a single
       source for access initialization. *)
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
