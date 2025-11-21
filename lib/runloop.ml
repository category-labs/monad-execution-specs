(*
open Numeric
module Address = Chain.Ethereum.Address

module Account = struct
  (* YP 4.1 *)
  type t = {nonce : Uint.t (* σ[a]_n *); balance : U256.t (* σ[a]_b *); code_hash : U256.t (* σ[a]_c *)}

  let is_empty acc =
    Uint.(acc.nonce = zero) && U256.(acc.balance = zero) && U256.(acc.code_hash = Crypto.keccak_256_empty)
end

module TrieDb = struct
  module type SIG = sig
    include Monad.SIG

    val read_account : Address.t -> Account.t option t
    val read_storage : Address.t -> U256.t -> U256.t t
    val read_code : Address.t -> Bytes.t option

    val commit : block_id:Uint.t -> unit
  end
end
 *)
