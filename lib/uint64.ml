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

let to_yojson (i : t) : Yojson.Safe.t = `Int (to_int i)
let of_yojson (i : Yojson.Safe.t) : (t, string) result =
  match i with `Int i -> Ok (of_int i) | _ -> Error "Uint64.t"
