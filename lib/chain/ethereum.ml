open Utils

module Address : sig
  type t = private Word.t
  val max_t : t
  val to_word : t -> Word.t
  val of_word : Word.t -> t option
  val of_word_masking : Word.t -> t

  val compare: t -> t -> int

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
  type t = Berlin | Cancun | Prague (* | etc *)
end

module Block = struct
  module Header = struct
    type t
  end
end
