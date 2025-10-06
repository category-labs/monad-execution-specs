module Make (T : sig
  type t
  val compare : t -> t -> int
end) =
struct
  let comparison_op (int_cmp : int -> int -> bool) (x : T.t) (y : T.t) = int_cmp (T.compare x y) 0
  let ( < ) = comparison_op Stdlib.( < )
  let ( <= ) = comparison_op Stdlib.( <= )
  let ( = ) = comparison_op Stdlib.( = )
  let ( >= ) = comparison_op Stdlib.( >= )
  let ( > ) = comparison_op Stdlib.( > )
  let ( <> ) = comparison_op Stdlib.( <> )

  module Set = Set.Make (T)
  module Map = Map.Make (T)
end
