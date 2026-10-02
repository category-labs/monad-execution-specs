(** [Stdlib.String] extended with monomorphic comparisons, maps and sets. *)

include Stdlib.String

include Comparable.Make (Stdlib.String)
