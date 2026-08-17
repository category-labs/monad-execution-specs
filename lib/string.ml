(** [Stdlib.String] extended with some utility functions. *)

include Stdlib.String

(* TODO: this will be provided by OCaml 5.5 *)
let find_substring ~substring str =
  let substr_len = length substring in
  let str_len = length str in
  let rec matches_at (i : int) (j : int) =
    if j >= substr_len then Some i
    else if i + j >= str_len then None
    else if Stdlib.(str.[i + j] = substring.[j]) then matches_at i (j + 1)
    else matches_at (i + 1) 0
  in
  matches_at 0 0

include Comparable.Make (Stdlib.String)
