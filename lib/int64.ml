include Stdlib.Int64
let ( + ) = Stdlib.Int64.add
let ( - ) = Stdlib.Int64.sub
let ( * ) = Stdlib.Int64.mul
let ( / ) = Stdlib.Int64.div

include Comparable.Make (struct
  type t = Stdlib.Int64.t
  let compare = Stdlib.Int64.compare
end)

module Hashtbl = Stdlib.Hashtbl.Make (Stdlib.Int64)
