(** QEDK's three persistent reserve slots. [valid_from = 0] means unconfigured;
    a matured record is read logically, without clearing its stored slots. *)
open Numeric

type t = {settled : Uint.t; pending : Uint.t; valid_from : Uint.t}

let default = Uint.of_string "10000000000000000000"
let limit = Uint.shift_left Uint.one 256

let active (record : t) (block : Uint.t) =
  if Uint.(record.valid_from = zero) then default
  else if Uint.(block < record.valid_from) then record.settled
  else record.pending

let read (record : t) (block : Uint.t) =
  let settled = active record block in
  if Uint.(record.valid_from = zero || record.valid_from <= block) then
    {settled; pending = settled; valid_from = Uint.zero}
  else record

(** Reject a still-pending request from a different block. Repeated settings
    in the requesting block replace its pending value, not its active value. *)
let set ~(delay : Uint.t) ~(block : Uint.t) (requested : Uint.t) (record : t) =
  let valid_from = Uint.(block + delay) in
  if Uint.(delay = zero || valid_from >= limit || requested >= limit) then None
  else if Uint.(record.valid_from > block && record.valid_from <> valid_from) then None
  else Some {settled = active record block; pending = requested; valid_from}
