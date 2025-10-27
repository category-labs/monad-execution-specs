open Numeric

module Address = U160

module Revision = struct
  type t =
    (* The Frontier revision.
       The one Ethereum launched with. *)
    | Frontier
    (* The Homestead revision.
       https://eips.ethereum.org/EIPS/eip-606 *)
    | Homestead
    (* The Tangerine Whistle revision.
       https://eips.ethereum.org/EIPS/eip-608 *)
    | TangerineWhistle
    (*       The Spurious Dragon revision.
       https://eips.ethereum.org/EIPS/eip-607 *)
    | SpuriousDragon
    (* The Byzantium revision.
       https://eips.ethereum.org/EIPS/eip-609 *)
    | Byzantium
    (* The Constantinople revision.
       https://eips.ethereum.org/EIPS/eip-1013 *)
    | Constantinople
    (* The Petersburg revision.
       Other names: Constantinople2, ConstantinopleFix.
       https://eips.ethereum.org/EIPS/eip-1716 *)
    | Petersburg
    (* The Istanbul revision.
       https://eips.ethereum.org/EIPS/eip-1679 *)
    | Istanbul
    (* The Berlin revision.
       https://github.com/ethereum/execution-specs/blob/master/network-upgrades/mainnet-upgrades/berlin.md *)
    | Berlin
    (* The London revision.
       https://github.com/ethereum/execution-specs/blob/master/network-upgrades/mainnet-upgrades/london.md *)
    | London
    (* The Paris revision (aka The Merge).
       https://github.com/ethereum/execution-specs/blob/master/network-upgrades/mainnet-upgrades/paris.md *)
    | Paris
    (* The Shanghai revision.
       https://github.com/ethereum/execution-specs/blob/master/network-upgrades/mainnet-upgrades/shanghai.md *)
    | Shanghai
    (* The Cancun revision.
       https://github.com/ethereum/execution-specs/blob/master/network-upgrades/mainnet-upgrades/cancun.md *)
    | Cancun
    (* The Prague / Pectra revision.
       https://eips.ethereum.org/EIPS/eip-7600 *)
    | Prague
    (* The Osaka / Fusaka revision.
       https://eips.ethereum.org/EIPS/eip-7607 *)
    | Osaka
    (* The unspecified EVM revision used for EVM implementations to expose
       experimental features. *)
    | Experimental
end

module Block = struct
  module Header = struct
    type t
  end
end
