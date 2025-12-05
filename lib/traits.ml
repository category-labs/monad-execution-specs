module Byte_width = struct
  module type SIG = sig
    val byte_width : [`Variable | `Fixed of int]
  end

  (* 2048 bits, used for Bloom filters *)
  module Bytes256 = struct
    let byte_width : [>`Fixed of int] = `Fixed 256
  end

  (* 256 bits *)
  module Bytes32 = struct
    let byte_width : [>`Fixed of int] = `Fixed 32
  end

  (* 160 bits *)
  module Bytes20 = struct
    let byte_width : [>`Fixed of int] = `Fixed 20
  end

  (* 64 bits *)
  module Bytes8 = struct
    let byte_width : [>`Fixed of int] = `Fixed 8
  end

  module Variable = struct
    let byte_width : [>`Variable] = `Variable
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
