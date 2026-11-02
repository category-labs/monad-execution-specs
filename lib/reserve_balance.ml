(** Definitions for reserve balance checks.
    Reserve balance is a Monad-specific mechanism that allows the network to support asynchronous execution
    of transactions in the presence of EIP-7702 account delegations. It ensures that the consensus layer may
    assume that account balances don't drop below a specific amount (the reserve balance) except for the case
    of sporadic "emptying transactions" which can be statically accounted for. *)

open Chain.Ethereum
open Chain.Monad
open Byte_string
open Numeric
open State
open Lens.Infix

(** Monad §3: default_reserve_balance *)
let default_reserve_balance = mon_to_wei U256.(~$10)

(** Monad §3: k, the block delay between consensus and execution. *)
let execution_consensus_delay = Uint.of_int 3

let precompile_address = Address.of_hex_string "0x1001"

(** These slots live in the precompile account, so the existing Host journal
    rolls them back with the enclosing call or transaction. *)
let config_slot (addr : Address.t) =
  let key = B32.to_bytes (Address.to_bytes32 addr) ^ B32.to_bytes B32.zeros in
  let slot_hash = U256.of_repr (Crypto.keccak_256 key) in
  U256.(logand slot_hash (lognot ~$127))

let stored_config (world : WorldState.t) (addr : Address.t) : Reserve_config.t =
  let storage = world.^(WorldState.account precompile_address).Account.storage in
  let base = config_slot addr in
  let slot offset =
    let key = U256.(to_repr (base + of_int offset)) in
    B32.Map.find_opt key storage |> Option.value ~default:B32.zeros |> U256.of_repr |> U256.to_uint
  in
  {settled = slot 0; pending = slot 1; valid_from = slot 2}

let user_reserve_balance (world : WorldState.t) (block : Uint.t) (addr : Address.t) =
  Reserve_config.active (stored_config world addr) block |> U256.of_uint_exn

(** Activate the native account without overwriting its balance, code or storage. *)
let activate_precompile (world : WorldState.t) =
  let lens = WorldState.account precompile_address |-- Account.nonce in
  world.^$(lens) <- (fun nonce -> U64.max nonce U64.one)

let set_reserve_balance (world : WorldState.t) (block : Uint.t) (addr : Address.t) (value : U256.t) =
  match
    Reserve_config.set ~delay:execution_consensus_delay ~block (U256.to_uint value) (stored_config world addr)
  with
  | None -> None
  | Some record ->
      let base = config_slot addr in
      let lens = WorldState.account precompile_address |-- Account.storage in
      let set_slot storage offset value =
        let key = U256.(to_repr (base + of_int offset)) in
        let value = U256.(to_repr (of_uint_exn value)) in
        if B32.(value = zeros) then B32.Map.remove key storage else B32.Map.add key value storage
      in
      let world = activate_precompile world in
      let storage = world.^(lens) in
      let storage = set_slot storage 0 record.settled in
      let storage = set_slot storage 1 record.pending in
      let storage = set_slot storage 2 record.valid_from in
      Some (world.^(lens) <- storage)

(** Monad §6 Algorithm 4 (IsEmptying). Check whether the current transaction is emptying.
    The check of [delegated_in_state] is exactly as in the spec. The comparison with the next emptying
    transaction counter subsumes both [auth_condition] and [prior_sender_condition].
    This function must be called after processing the transaction's authorization list.
    Note that authority processing bumps the next emptying transaction block counter before the transaction
    is processed, but the transaction itself only bumps its sender's counter after it finishes, so while
    processing it this function will return [true]. *)
let is_emptying_tx : bool TransactionState.M.t =
  let open TransactionState in
  M.(
    let$ state = get in
    let sender = state.tx_origin in
    let delegated_in_state = Delegation.is_valid_delegation state.^(account sender).Account.code in
    return
      ( (not delegated_in_state)
      && Uint.(
           state.world_state.^(WorldState.next_emptying_transaction_block_for sender)
           <= state.current_block.header.number ) ) )

(** Monad §6 Algorithm 3 (DippedIntoReserve). *)
let dipped_into_reserve (revision : Chain.Monad.Revision.active) : bool TransactionState.M.t =
  let open TransactionState in
  M.(
    let$ tx_sender = !tx_origin in
    let$ tx_gas_limit = !tx_gas_limit in
    let$ tx_effective_gas_price = !tx_gas_price in
    let$ is_emptying = is_emptying_tx in
    let$ original_world = !initial_world_state in
    let$ block = !(current_block |-- Block.header |-- Block.Header.number) in
    let original_balances = original_world.accounts in
    let$ new_state = !(world_state |-- WorldState.accounts) in
    let$ self_destruct = !self_destruct in
    let account_reserve_violated (addr : Address.t) (orig_account : Account.t) (new_account : Account.t) =
      let configured =
        match revision with
        | `Eleven -> user_reserve_balance original_world block addr
        | _ -> default_reserve_balance
      in
      let reserve = U256.(min configured orig_account.balance) in
      let current_balance = new_account.balance in
      let tx_gas_fees = Uint.(tx_gas_limit * tx_effective_gas_price) in
      let violation_threshold =
        if Address.(addr = tx_sender) then
          if Uint.(U256.to_uint reserve >= tx_gas_fees) then U256.(reserve - of_uint_exn tx_gas_fees)
          else
            (* Avoid unsigned underflow; the fee guard below rejects this case
               for non-emptying senders in every revision. *)
            U256.zero
        else reserve
      in
      (Address.(addr <> tx_sender) || not is_emptying)
      && ( (Address.(addr = tx_sender) && Uint.(tx_gas_fees > U256.to_uint reserve))
         || U256.(current_balance < violation_threshold) )
    in
    let original_balances = Address.Map.to_seq original_balances in
    let balances_to_check =
      match revision with
      | `Eight -> original_balances
      | `Nine | `Eleven ->
          original_balances
          |> Seq.filter (fun (addr, _) ->
              (* Monad §TODO: Accounts that are created and self-destructed in this transaction are allowed
                 to violate reserve balance conditions. *)
              not (Address.Set.mem addr self_destruct) )
    in
    balances_to_check
    (* TODO: filter out the staking precompile once that is merged. *)
    |> Seq.filter_map (fun (addr, orig_account) ->
        let new_account = Address.Map.find_opt addr new_state |> Option.value ~default:Account.empty in
        if Account.is_smart_contract new_account then None else Some (addr, orig_account, new_account) )
    |> Seq.exists (fun (addr, orig_account, new_account) ->
        account_reserve_violated addr orig_account new_account )
    |> return )
