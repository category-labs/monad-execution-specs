module Revision = struct
  type t = Zero | One | Two | Three | Four
  module type SIG = sig
    val rev : t
  end
end

module Traits (Rev : Revision.SIG) = struct
  let monad_rev = Rev.rev
  let evm_rev =
    if Revision.(monad_rev >= Four) then Ethereum.Revision.Prague else Ethereum.Revision.Cancun

  let monad_pricing_version = if Revision.(monad_rev >= Four) then 1 else 0

  type cold_costs = {cold_account_cost : Uint64.t; cold_storage_cost : Uint64.t}
  let cold_costs =
    if monad_pricing_version >= 1 then {cold_account_cost = 10000L; cold_storage_cost = 8000L}
    else {cold_account_cost = 2500L; cold_storage_cost = 2000L}

  let chain_id = 10143 (* testnet *)
end
