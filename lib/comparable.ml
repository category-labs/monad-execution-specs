(** Automatically derived monomorphic comparison operators on types implementing [compare]. *)

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

  let max x y = if x < y then y else x
  let min x y = if x < y then x else y

  module Set = Set.Make (T)
  module Map = struct
    include Map.Make (T)
    let keys (map : 'a t) : Set.t = to_seq map |> Seq.map (fun (k, _) -> k) |> Set.of_seq
  end
end
