(** Definitions for reserve balance checks. *)
open Chain.Ethereum

open Chain.Monad
open Numeric

(** Monad §3: default_reserve_balance *)
let default_reserve_balance = mon_to_wei U256.(~$10)

let user_reserve_balance (account : Account.t) = ignore account ; default_reserve_balance

(** Monad §3: k *)
let execution_consensus_delay = Uint.of_int 3

(** Monad §6 Algorithm 3 (DippedIntoReserve) *)
let dipped_into_reserve
    ~(chain_id : Uint.t)
    ~(base_fee_per_gas : Uint.t)
    ~(original_balances : Accounts.t)
    ~(new_state : Accounts.t)
    ~(t : Transaction.t)
    ~(is_emptying : bool) : bool =
  let t_sender = Option.get (Transaction.sender chain_id t) in
  let account_reserve_violated (addr : Address.t) (orig_account : Account.t) (new_account : Account.t) =
    let reserve = U256.(min (user_reserve_balance orig_account) orig_account.balance) in
    let current_balance = new_account.balance in
    let violation_threshold =
      if Address.(addr = t_sender) then
        let tx_gas_fees =
          Uint.(Transaction.gas_limit t * Option.get (Gas.tx_effective_gas_price base_fee_per_gas t))
        in
        if Uint.(U256.to_uint reserve >= tx_gas_fees) then U256.(reserve - of_uint_exn tx_gas_fees)
        else
          (* The behavior here is consistent with Monad §6 Algorithm 3 Eqn (28), but it differs from both
             the execution client and the Monad Foundation specs.
             The execution client will always fail the reserve balance check if gas_fees > reserve.
             The Monad Foundation implementation will crash with an overflow.
             This difference in behavior is considered acceptable as consensus will not include a transaction
             where gas fees exceed reserve.
           *)
          U256.zero
      else reserve
    in
    (Address.(addr <> t_sender) || not is_emptying) && U256.(current_balance < violation_threshold)
  in
  Accounts.to_seq original_balances
  |> Seq.exists (fun (addr, orig_account) ->
      let new_account = Accounts.find_opt addr new_state |> Option.value ~default:Account.empty in
      (not (Account.is_smart_contract new_account)) && account_reserve_violated addr orig_account new_account )
