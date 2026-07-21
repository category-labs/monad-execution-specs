(** Definitions for reserve balance checks. *)

open Chain.Ethereum
open Chain.Monad
open Numeric
open State
open Lens.Infix

(** Monad §3: default_reserve_balance *)
let default_reserve_balance = mon_to_wei U256.(~$10)

let user_reserve_balance (account : Account.t) = ignore account ; default_reserve_balance

(** Monad §3: k *)
let execution_consensus_delay = Uint.of_int 3

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
    let$ original_balances = !(initial_world_state |-- WorldState.accounts) in
    let$ new_state = !(world_state |-- WorldState.accounts) in
    let$ self_destruct = !self_destruct in
    let account_reserve_violated (addr : Address.t) (orig_account : Account.t) (new_account : Account.t) =
      let reserve = U256.(min (user_reserve_balance orig_account) orig_account.balance) in
      let current_balance = new_account.balance in
      let violation_threshold =
        if Address.(addr = tx_sender) then
          let tx_gas_fees = Uint.(tx_gas_limit * tx_effective_gas_price) in
          if Uint.(U256.to_uint reserve >= tx_gas_fees) then U256.(reserve - of_uint_exn tx_gas_fees)
          else
            (* The behavior here is consistent with Monad §6 Algorithm 3 Eqn (28), but it differs from both
               the execution client and the Monad Foundation specs.
               * The execution client will always fail the reserve balance check if gas_fees > reserve.
               * The Monad Foundation implementation will crash with an overflow.
               This difference in behavior is considered acceptable as consensus will not include a transaction
               where gas fees exceed reserve. *)
            U256.zero
        else reserve
      in
      (Address.(addr <> tx_sender) || not is_emptying) && U256.(current_balance < violation_threshold)
    in
    Address.Map.to_seq original_balances
    |> ( match revision with
      | `Eight -> Fun.id
      | `Nine ->
          Seq.filter (fun (addr, _) ->
              (* Accounts that are created and self-destructed in this transaction are allowed to violate
                 reserve balance conditions. *)
              not (Address.Set.mem addr self_destruct) ) )
    (* TODO: filter out the staking precompile once that is merged. *)
    |> Seq.filter_map (fun (addr, orig_account) ->
        let new_account = Address.Map.find_opt addr new_state |> Option.value ~default:Account.empty in
        if Account.is_smart_contract new_account then None else Some (addr, orig_account, new_account) )
    |> Seq.exists (fun (addr, orig_account, new_account) ->
        account_reserve_violated addr orig_account new_account )
    |> return )
