(** [Stdlib.Option] extended with lens operations and monadic operators. *)
include Stdlib.Option

let get_or_create (create : unit -> 'a) : ('a option, 'a) Lens.t =
  {get = (function None -> create () | Some v -> v); set = (fun x _ -> Some x)}

let get_or_default (default : 'a) : ('a option, 'a) Lens.t =
  {get = (function None -> default | Some v -> v); set = (fun x _ -> Some x)}

let get_or_throw : ('a option, 'a) Lens.t = {get; set = (fun x _ -> Some x)}

let ( >>= ) = bind
let ( let$ ) = bind
let return x = Some x

(* TODO: better monad API for options in general *)
let rec sequence (ls : 'a option list) : 'a list option =
  match ls with [] -> Some [] | Some hd :: tl -> map (fun tl -> hd :: tl) (sequence tl) | None :: _ -> None

let ensure (predicate : bool) : unit option = if predicate then Some () else None
