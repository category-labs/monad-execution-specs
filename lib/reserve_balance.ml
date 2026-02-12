(** Definitions for reserve balance checks. *)
open Chain.Ethereum

open Chain.Monad
open Numeric

(* Monad §3: default_reserve_balance *)
let default_reserve_balance = mon_to_wei U256.(~$10)

let user_reserve_balance (account : Account.t) = ignore account ; default_reserve_balance

(* Monad §3: k *)
let execution_consensus_delay = Uint.of_int 3

(** Monad §6 Algorithm 4 (IsEmptying) *)
let is_tx_emptying
    ~(chain_id : Uint.t)
    ~(t : Transaction.t)
    ~(current_block : Block.t)
    ~(previous_blocks : Block.t list)
    ~(delegated_in_state : bool) =
  (* This implementation follows the definition of IsEmptying in the spec as closely as possible. It has not
     been optimized for performance. *)
  let starting_block_number =
    Integer.(
      as_unsigned_exn
        (max
           (Uint.as_signed current_block.header.number - Uint.as_signed execution_consensus_delay + one)
           zero ) )
  in
  let sender = Option.get (Transaction.sender chain_id t) in
  let transactions_before_t =
    List.to_seq previous_blocks
    |> Seq.take_while (fun (block : Block.t) -> Uint.(block.header.number >= starting_block_number))
    |> Seq.concat_map (fun (block : Block.t) -> List.to_seq block.transactions)
    |> List.of_seq
    |> List.append (List.take_while (fun tx -> tx <> t) current_block.transactions)
  in
  let delegation_condition = delegated_in_state in
  let auth_condition =
    let has_delegation_auth (sender : Address.t) (tx : Transaction.t) =
      List.exists
        (fun auth ->
          match Transaction.Authorization.authority auth with
          | None -> false
          | Some authority -> Address.(authority = sender) )
        (Transaction.authorization_list tx)
    in
    has_delegation_auth sender t || List.exists (has_delegation_auth sender) transactions_before_t
  in
  let prior_sender_condition =
    List.exists
      (fun tx -> Address.(Option.get (Transaction.sender chain_id tx) = sender))
      transactions_before_t
  in
  (not delegation_condition) && (not auth_condition) && not prior_sender_condition

(** Monad §6 Algorithm 3 (DippedIntoReserve) *)
let dipped_into_reserve
    ~(chain_id : Uint.t)
    ~(base_fee_per_gas : Uint.t)
    ~(original_balances : Account.t Address.Map.t)
    ~(new_state : Account.t Address.Map.t)
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
        else U256.zero
      else reserve
    in
    (Address.(addr <> t_sender) || not is_emptying) && U256.(current_balance < violation_threshold)
  in
  Address.Map.to_seq original_balances
  |> Seq.exists (fun (addr, orig_account) ->
      let new_account = Address.Map.find_opt addr new_state |> Option.value ~default:Account.empty in
      (not (Account.is_smart_contract new_account)) && account_reserve_violated addr orig_account new_account )
