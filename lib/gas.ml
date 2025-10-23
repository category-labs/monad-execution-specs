open Numeric

(* Bring Uint into scope so the operators are all available to users *)
include Uint

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

let cold_sload_cost = ~$2_100
let cold_account_access_cost = ~$2_600
let warm_access_cost = ~$100
let account_access_cost = function `Warm -> warm_access_cost | `Cold -> cold_account_access_cost

let memory_cost_per_word = ~$3
let memory_cost (active_memory_words : U256.t) =
  let active_memory_words = U256.to_unbounded active_memory_words in
  Uint.(((active_memory_words ** 2) / ~$512) + (memory_cost_per_word * active_memory_words))

let copy_cost_per_word = ~$3

let block_hash_cost = ~$20

let sset_cost = ~$20_000
let sclear_refund = ~$4_800
let sreset_cost = ~$2_900 (* Equal to GAS_STORAGE_UPDATE - GAS_COLD_SLOAD in the executable EVM spec *)

(* As of Monad 5, the only difference with Ethereum is create_cost *)
let create_cost = ~$160_000
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
