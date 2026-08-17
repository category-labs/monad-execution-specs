(** Constants and functions involved in computing gas costs. All gas costs are computed as arbitrary-precision
    unsigned integers [Uint.t]. *)

open Numeric
open Byte_string
open Chain.Ethereum

(* Bring Uint into scope so the operators are all available to users. *)
include Uint

(* YP (48) *)
let updated_base_fee_per_gas (parent_header : Block.Header.t) =
  (* TODO: implement Monad Spec 2.6, obsoletes YP (48), YP (49), YP (50), YP (51), YP (52), YP (53) *)
  let elasticity_multiplier (* YP (50) *) = ~$2 in
  let base_fee_max_change_denominator (* YP (53) *) = ~$8 in
  let base_fee = parent_header.base_fee_per_gas in
  let gas_used = parent_header.gas_used in
  let gas_target (* YP (49) *) = parent_header.gas_limit / elasticity_multiplier in
  match () with
  | () when gas_used = gas_target -> base_fee
  | () when gas_used < gas_target ->
      let base_fee_decrease_star (* YP (51) *) = base_fee * (gas_target - gas_used) / gas_target in
      let base_fee_decrease (* YP (52) *) = base_fee_decrease_star / base_fee_max_change_denominator in
      base_fee - base_fee_decrease
  | () when gas_used > gas_target ->
      let base_fee_increase_star (* YP (51) *) = base_fee * (gas_used - gas_target) / gas_target in
      let base_fee_increase (* YP (52) *) =
        max (base_fee_increase_star / base_fee_max_change_denominator) one
      in
      base_fee + base_fee_increase
  | () -> assert false (* Unreachable. *)

(** The amount of gas provided for the execution of a system transaction. See EIP-2935, EIP-4788. *)
let system_transaction_gas = ~$30_000_000

(** Gas cost per zero byte of the calldata. Non-zero bytes consume 4 times this amount. See G_txdatazero and
    G_txdatanonzero in YP (64). *)
let tx_calldata_token_gas = ~$4

(** The minimum amount of gas consumed by a transaction for each zero byte of the calldata. Non-zero bytes
    consume 4 times this amount. See EIP-7623. *)
let tx_calldata_floor_token_gas = ~$10

(** Additional gas cost for contract creation transactions. See G_create in YP Appendix G. *)
let tx_create_gas = ~$32_000

(** Gas cost per 32-byte word of initcode in a deploy transaction or a CREATE or CREATE2 operation.
    See G_initcodeword in YP Appendix G. *)
let tx_initcode_gas_per_word = ~$2

(** Gas cost per address in a transaction's access list. *)
let tx_access_list_address = ~$2_400

(** Gas cost per storage key in a transaction's access list. *)
let tx_access_list_storage = ~$1_900

(** Base gas cost of a transaction. *)
let tx_base_gas = ~$21_000

(** Compute the amount of tokens in a transaction's calldata. A zero byte is counted as one token, a
    non-zero byte is counted as 4 tokens. *)
let tokens_in_calldata (tx : Transaction.t) =
  let Bytes.{zero_bytes; nonzero_bytes} = Bytes.count_zero_and_nonzero_bytes Transaction.(data tx) in
  Stdlib.(zero_bytes + (4 * nonzero_bytes))

(** EIP-7702: Cost of processing an authorization when the code of the authority is empty. *)
let tx_authorization_list_gas_per_address = Delegation.per_empty_account_cost

(** EIP-7702: Gas refund when processing an authorization when the code of the authority is empty.
    As per the EIP, the full cost is subtracted first, as if the code was empty, and this amount is then
    added to the refund counter. *)
let tx_authorization_list_refund_per_nonempty = Delegation.(per_empty_account_cost - per_auth_base_cost)

(** [tx_intrinsic_gas tx] computes the intrinsic gas cost of [tx], that is, the amount of gas that is charged
    before execution starts. YP (64) *)
let tx_intrinsic_gas (tx : Transaction.t) =
  let calldata_gas = ~$(tokens_in_calldata tx) * tx_calldata_token_gas in
  let create_gas =
    match Transaction.call_or_create tx with
    | Call _ -> zero
    | Create {initcode} ->
        (* YP (65) *)
        tx_create_gas + (tx_initcode_gas_per_word * bytes_to_whole_words ~$(Bytes.length initcode))
  in
  let transaction_gas = tx_base_gas in
  let access_list_gas =
    List.fold_left
      (fun g (access : Transaction.Access.t) ->
        g + tx_access_list_address + (tx_access_list_storage * ~$(List.length access.storage_keys)) )
      zero (Transaction.access_list tx)
  in
  let authorization_list_gas =
    tx_authorization_list_gas_per_address * ~$(List.length (Transaction.authorization_list tx))
  in
  calldata_gas + create_gas + transaction_gas + access_list_gas + authorization_list_gas

(** [tx_floor_gas tx] computes the floor gas cost of [tx], as per EIP-7623. A transaction must provide enough
    gas to cover this amount (before subtracting the intrinsic gas), but it is not charged. Instead, it is
    used as a lower bound to the post-execution gas used counter. Monad transactions always use the full
    amount of gas provided, so the floor gas is only used as a pre-execution check. *)
let tx_floor_gas (tx : Transaction.t) =
  (~$(tokens_in_calldata tx) * tx_calldata_floor_token_gas) + tx_base_gas

(** [tx_effective_gas_price b tx] is the price in MON-wei that the sender of [tx] will pay per unit of gas.
    YP (66), gas_bid in Monad §2 *)
let tx_effective_gas_price (base_fee_per_gas : t) (tx : Transaction.t) =
  (* YP (67) and YP (70) are folded into this definition. *)
  match Transaction.fee_mechanism tx with
  | FeeMarketFee {max_fee_per_gas; max_priority_fee_per_gas} ->
      (* YP (72) *)
      if max_fee_per_gas < max_priority_fee_per_gas then None
      else
        (* f + H_f, computed as min(T_f + H_f, Tₘ) as per Monad §2, which is equivalent to folding YP (67)
           into YP (66) *)
        Some (min (max_priority_fee_per_gas + base_fee_per_gas) max_fee_per_gas)
  | LegacyFee {gas_price} -> Some gas_price

(** Maximum amount of gas a transaction is allowed to provide. If a transaction's gas limit exceeds this
    amount, it is considered invalid. EIP-7825, adjusted for Monad §3 max_tx_gas_limit. *)
let tx_max_gas_limit = ~$30_000_000

(* Per-instruction gas costs as per YP (326), adjusted for Monad §4.1 *)
let jumpdest = ~$1

let base = ~$2

let very_low = ~$3
let low = ~$5
let mid = ~$8
let high = ~$10

let exp_base_cost = ~$10
let exp_cost_per_byte = ~$50

let keccak256_base_cost = ~$30
let keccak256_cost_per_word = ~$6

let log_cost = ~$375
let log_cost_per_byte = ~$8
let log_cost_per_topic = ~$375

let self_destruct_cost = ~$5_000
let self_destruct_new_account_cost = ~$25_000

let new_account_cost = ~$25_000

let call_value = ~$9_000
let call_stipend = ~$2_300

(* Different from Ethereum, see Monad §4.1 *)
let cold_sload_cost = ~$8_100
let cold_account_access_cost = ~$10_100

let warm_access_cost = ~$100

(* YP (329) *)
let account_access_cost = function `Warm -> warm_access_cost | `Cold -> cold_account_access_cost

let memory_cost (revision : Chain.Monad.Revision.active) =
  match revision with
  | `Eight ->
      (* YP (328) *)
      let memory_cost_per_word = ~$3 in
      fun (active_memory_words : Uint.t) ->
        Uint.(((active_memory_words ** 2) / ~$512) + (memory_cost_per_word * active_memory_words))
  | `Nine ->
      (* MIP-3 *)
      fun (active_memory_words : Uint.t) -> Uint.(active_memory_words / ~$2)

let copy_cost_per_word = ~$3

let block_hash_cost = ~$20

let sset_cost = ~$20_000
let sclear_refund = ~$4_800
let sreset_cost = ~$2_900 (* Equal to GAS_STORAGE_UPDATE - GAS_COLD_SLOAD in the executable EVM spec *)

let create_cost = ~$32_000
let create_cost_per_initcode_word = ~$2
let code_deposit_per_byte = ~$200

(* YP C_gascap *)
let c_gascap ~gas ~gas_left ~memory_cost ~extra_cost =
  if Uint.(gas_left >= memory_cost + extra_cost) then
    let available_gas = Uint.(gas_left - memory_cost - extra_cost) in
    Uint.(min gas (minus_1_64th available_gas))
  else gas

type call_gas = {caller_spent_gas : Uint.t (* YP C_call *); callee_available_gas : Uint.t (* YP C_callgas *)}

(** Before a call instruction, [call_gas] computes the gas that will be spent by the caller (excluding the
    cost of memory expansion, which is paid separately) and the gas that will be available for the callee. *)
let call_gas ~transfer_value ~gas ~gas_left ~memory_cost ~extra_cost =
  let c_gascap = c_gascap ~gas ~gas_left ~memory_cost ~extra_cost in
  let caller_spent_gas = Uint.(c_gascap + extra_cost) in
  let callee_available_gas = if transfer_value then Uint.(c_gascap + call_stipend) else c_gascap in
  {caller_spent_gas; callee_available_gas}
