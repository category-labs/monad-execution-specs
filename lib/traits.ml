module Byte_width = struct
  module type SIG = sig
    val byte_width : [`Variable | `Fixed of int]
  end

  (* 2048 bits, used for Bloom filters *)
  module Bytes256 = struct
    let byte_width : [> `Fixed of int] = `Fixed 256
  end

  (* 768 bits, used for reading compressed BLS G2 points. *)
  module Bytes96 = struct
    let byte_width : [> `Fixed of int] = `Fixed 96
  end

  (* 512 bits, used for decoding points in BLS12-381. *)
  module Bytes64 = struct
    let byte_width : [> `Fixed of int] = `Fixed 64
  end

  (* 384 bits, used to represent BLS public keys. *)
  module Bytes48 = struct
    let byte_width : [> `Fixed of int] = `Fixed 48
  end

  (* 264 bits, used to represent compressed secp256k1 public keys. *)
  module Bytes33 = struct
    let byte_width : [> `Fixed of int] = `Fixed 33
  end

  (* 256 bits *)
  module Bytes32 = struct
    let byte_width : [> `Fixed of int] = `Fixed 32
  end

  (* 160 bits *)
  module Bytes20 = struct
    let byte_width : [> `Fixed of int] = `Fixed 20
  end

  (* 64 bits *)
  module Bytes8 = struct
    let byte_width : [> `Fixed of int] = `Fixed 8
  end

  (* 32 bits, used for Solidity method selectors *)
  module Bytes4 = struct
    let byte_width : [> `Fixed of int] = `Fixed 4
  end

  (* 8 bits *)
  module Bytes1 = struct
    let byte_width : [> `Fixed of int] = `Fixed 1
  end

  module Variable = struct
    let byte_width : [> `Variable] = `Variable
  end
end

module Signedness = struct
  module type SIG = sig
    val signedness : [`Signed | `Unsigned]
  end

  module Unsigned = struct
    let signedness = `Unsigned
  end
  module Signed = struct
    let signedness = `Signed
  end
end
