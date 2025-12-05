(** [Stdlib.Option] extended with lens operations and monadic operators. *)
include Stdlib.Option

let get_or_create (create : unit -> 'a) : ('a option, 'a) Lens.t =
  {get = (function None -> create () | Some v -> v); set = (fun x _ -> Some x)}

let get_or_default (default : 'a) : ('a option, 'a) Lens.t =
  {get = (function None -> default | Some v -> v); set = (fun x _ -> Some x)}

let get_or_throw : ('a option, 'a) Lens.t = {get; set = (fun x _ -> Some x)}

let ( >>= ) = bind
let ( let$ ) = bind
