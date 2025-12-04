(** As [Int64] but all operations are unsigned *)

include Int64

let div = Stdlib.Int64.unsigned_div
let rem = Stdlib.Int64.unsigned_rem
let ( / ) = Stdlib.Int64.unsigned_div

let ( ~$ ) = Stdlib.Int64.of_int

include Comparable.Make (struct
  type t = Stdlib.Int64.t
  let compare = Stdlib.Int64.unsigned_compare
end)

let max_uint = 0xffffffffffffffffL

module Hashtbl = Stdlib.Hashtbl.Make (Stdlib.Int64)
