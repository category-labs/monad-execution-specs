(** [Stdlib.Map] extended with lens operations. *)
include Stdlib.Map

module type S = sig
  include Stdlib.Map.S
  val at : key -> ('v t, 'v option) Lens.t
end
module Make (Ord : OrderedType) = struct
  include Stdlib.Map.Make (Ord)
  let at (k : key) : ('v t, 'v option) Lens.t =
    {get = (fun m -> find_opt k m); set = (fun v m -> update k (fun _ -> v) m)}
end
