(** As [Stdlib.Result] but exposing additional operations. *)

include Stdlib.Result

include Monad.Make2 (struct
  type nonrec ('a, 'err) t = ('a, 'err) t
  let return x = Ok x
  let ( >>= ) x f = match x with Ok x -> f x | Error err -> Error err
end)

let fail err = Error err

let ensure (predicate : bool) ~or_error = if predicate then Ok () else Error or_error

module Option = struct
  include Option

  let or_fail (err : 'err) = function None -> Error err | Some x -> Ok x
end
