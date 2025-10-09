open Utils

module Address : sig
  type t = private Word.t
  val max_t : t
  val to_word : t -> Word.t
  val of_word : Word.t -> t option
  val of_word_masking : Word.t -> t

  val compare : t -> t -> int

  val zero : t

  module Map : Map.S with type key = t
  module Set : Set.S with type elt = t
end = struct
  include Word

  let max_t : Word.t = Word.of_string "0xffffffffffffffffffffffffffffffffffffffff"

  let to_word (x : t) = x
  let of_word (x : Word.t) : t option = if Word.(x > max_t) then None else Some x
  let of_word_masking (x : Word.t) : t = Word.(logand max_t x)

  let compare = Word.compare

  module Map = Word.Map
  module Set = Word.Set
end

module Revision = struct
  type t =
    (*
     * The Frontier revision.
     *
     * The one Ethereum launched with.
     *)
    | Frontier
    (*
     * The Homestead revision.
     *
     * https://eips.ethereum.org/EIPS/eip-606
     *)
    | Homestead
    (*
     * The Tangerine Whistle revision.
     *
     * https://eips.ethereum.org/EIPS/eip-608
     *)
    | TangerineWhistle
    (*
     * The Spurious Dragon revision.
     *
     * https://eips.ethereum.org/EIPS/eip-607
     *)
    | SpuriousDragon
    (*
     * The Byzantium revision.
     *
     * https://eips.ethereum.org/EIPS/eip-609
     *)
    | Byzantium
    (*
     * The Constantinople revision.
     *
     * https://eips.ethereum.org/EIPS/eip-1013
     *)
    | Constantinople
    (*
     * The Petersburg revision.
     *
     * Other names: Constantinople2, ConstantinopleFix.
     *
     * https://eips.ethereum.org/EIPS/eip-1716
     *)
    | Petersburg
    (*
     * The Istanbul revision.
     *
     * https://eips.ethereum.org/EIPS/eip-1679
     *)
    | Istanbul
    (*
     * The Berlin revision.
     *
     * https://github.com/ethereum/execution-specs/blob/master/network-upgrades/mainnet-upgrades/berlin.md
     *)
    | Berlin
    (*
     * The London revision.
     *
     * https://github.com/ethereum/execution-specs/blob/master/network-upgrades/mainnet-upgrades/london.md
     *)
    | London
    (*
     * The Paris revision (aka The Merge).
     *
     * https://github.com/ethereum/execution-specs/blob/master/network-upgrades/mainnet-upgrades/paris.md
     *)
    | Paris
    (*
     * The Shanghai revision.
     *
     * https://github.com/ethereum/execution-specs/blob/master/network-upgrades/mainnet-upgrades/shanghai.md
     *)
    | Shanghai
    (*
     * The Cancun revision.
     *
     * https://github.com/ethereum/execution-specs/blob/master/network-upgrades/mainnet-upgrades/cancun.md
     *)
    | Cancun
    (*
     * The Prague / Pectra revision.
     *
     * https://eips.ethereum.org/EIPS/eip-7600
     *)
    | Prague
    (*
     * The Osaka / Fusaka revision.
     *
     * https://eips.ethereum.org/EIPS/eip-7607
     *)
    | Osaka
    (*
     * The unspecified EVM revision used for EVM implementations to expose
     * experimental features.
     *)
    | Experimental
end

module Block = struct
  module Header = struct
    type t
  end
end
