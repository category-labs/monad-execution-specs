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

  let chain_id = 10143 (* testnet *)
end
