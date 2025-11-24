(** As [Stdlib.Result] but exposing additional operations. *)

include Stdlib.Result

include Monad.Make2 (struct
  type nonrec ('a, 'err) t = ('a, 'err) t
  let return x = Ok x
  let ( >>= ) x f = match x with Ok x -> f x | Error err -> Error err
end)
