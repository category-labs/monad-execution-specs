(** As [Int64] but all operations are unsigned *)

include Int64

let div = unsigned_div
let rem = unsigned_rem
let ( / ) = unsigned_div

let ( ~$ ) = of_int

include Comparable.Make (struct
  type nonrec t = t
  let compare = unsigned_compare
end)

let shift_right = shift_right_logical

let max_uint = 0xffffffffffffffffL

module Hashtbl = Stdlib.Hashtbl.Make (Stdlib.Int64)
