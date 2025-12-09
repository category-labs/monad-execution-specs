(** Constants and functions involved in computing gas costs. All gas costs are computed as arbitrary-precision
    unsigned integers [Uint.t]. *)

open Numeric
open Byte_string
open Chain.Ethereum

(* Bring Uint into scope so the operators are all available to users. *)
include Uint

(* See EIP-2935, EIP-4788. *)
let system_transaction_gas = ~$30_000_000

let gas_per_blob = exp ~$2 ~$17
let max_blob_gas_per_block = ~$1_179_648

let taylor_approximation_exponential ~factor ~numerator ~denominator =
  let i = ref one in
  let output = ref zero in
  let numerator_accumulated = ref (factor * denominator) in
  while !numerator_accumulated > zero do
    output := !output + !numerator_accumulated ;
    numerator_accumulated := !numerator_accumulated * numerator / (denominator * !i) ;
    i := !i + one
  done ;
  !output / denominator

let min_blob_gas_price = one
let blob_base_fee_update_fraction = ~$5_007_716

let block_blob_gas_price (excess_blob_gas : t) =
  taylor_approximation_exponential ~factor:min_blob_gas_price ~numerator:excess_blob_gas
    ~denominator:blob_base_fee_update_fraction

let tx_calldata_token_gas = ~$4
let tx_calldata_floor_token_gas = ~$10

let tx_create_gas = ~$32_000
let tx_initcode_gas_per_word = ~$2

let tx_access_list_address = ~$2_400
let tx_access_list_storage = ~$1_900

let tx_base_gas = ~$21_000

let tokens_in_calldata (tx : Transaction.t) =
  let Bytes.{zero_bytes; nonzero_bytes} = Bytes.count_zero_and_nonzero_bytes Transaction.(data tx) in
  Stdlib.(zero_bytes + (4 * nonzero_bytes))

(* YP (64) *)
let tx_intrinsic_gas (tx : Transaction.t) =
  let calldata_gas = ~$(tokens_in_calldata tx) * tx_calldata_token_gas in
  let create_gas =
    match Transaction.call_or_create tx with
    | Call _ -> zero
    | Create {initcode} ->
        tx_create_gas + (tx_initcode_gas_per_word * bytes_to_whole_words ~$(Bytes.length initcode))
  in
  let transaction_gas = tx_base_gas in
  let access_list_gas =
    List.fold_left
      (fun g (access : Transaction.Access.t) ->
        g + tx_access_list_address + (tx_access_list_storage * ~$(List.length access.storage_keys)) )
      zero (Transaction.access_list tx)
  in
  calldata_gas + create_gas + transaction_gas + access_list_gas

(* EIP-7623 *)
let tx_floor_gas (tx : Transaction.t) =
  (~$(tokens_in_calldata tx) * tx_calldata_floor_token_gas) + tx_base_gas

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

(* Different from Ethereum, see Monad Spec 4.1 *)
let cold_sload_cost = ~$8_100
let cold_account_access_cost = ~$10_100

let warm_access_cost = ~$100
let account_access_cost = function `Warm -> warm_access_cost | `Cold -> cold_account_access_cost

let memory_cost_per_word = ~$3
let memory_cost (active_memory_words : Uint.t) =
  Uint.(((active_memory_words ** 2) / ~$512) + (memory_cost_per_word * active_memory_words))

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

let call_gas ~value ~gas ~gas_left ~memory_cost ~extra_cost =
  let c_gascap = c_gascap ~gas ~gas_left ~memory_cost ~extra_cost in
  let caller_spent_gas = Uint.(c_gascap + extra_cost) in
  let callee_available_gas = if U256.(value <> zero) then Uint.(c_gascap + call_stipend) else c_gascap in
  {caller_spent_gas; callee_available_gas}
