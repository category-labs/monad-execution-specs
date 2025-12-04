module Byte_width = struct
  module type SIG = sig
    val byte_width : int option
  end

  (* 2048 bits, used for Bloom filters *)
  module Bytes256 = struct
    let byte_width = Some 256
  end

  (* 256 bits *)
  module Bytes32 = struct
    let byte_width = Some 32
  end

  (* 160 bits *)
  module Bytes20 = struct
    let byte_width = Some 160
  end

  (* 64 bits *)
  module Bytes8 = struct
    let byte_width = Some 8
  end

  module Unbounded = struct
    let byte_width = None
  end
end

module Signedness = struct
  module type SIG = sig
    val signed : bool
  end
  module Signed : SIG = struct
    let signed = true
  end
  module Unsigned : SIG = struct
    let signed = false
  end
end
