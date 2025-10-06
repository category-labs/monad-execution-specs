module Address : sig
  type t
  val max_t : t
  val to_word : t -> Word.t
  val of_word : Word.t -> t option
  val of_word_masking : Word.t -> t
end = struct
  type t = Word.t
  let max_t : Word.t = Word.of_string "0xffffffffffffffffffffffffffffffffffffffff"
  let to_word (x : t) = x
  let of_word (x : Word.t) : t option = if Word.(x > max_t) then None else Some x
  let of_word_masking (x : Word.t) : t = Word.(logand max_t x)
end
module Revision = struct
  type t = Berlin | Cancun | Prague (* | etc *)
end

module Block = struct
  module Header = struct
    type t
  end
end
