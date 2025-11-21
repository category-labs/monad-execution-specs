(** As [Stdlib.Result] but exposing additional operations. *)

include Stdlib.Result

(* Lightweight monadic operations for Result, when instantiating the monomorphic version is not worth it. *)
let (let$) = bind
let return x = Ok x

let fail err = Error err
