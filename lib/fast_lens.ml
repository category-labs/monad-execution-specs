(** More efficient implementations of lens operators. *)

type ('a, 'b) t = ('a, 'b) Lens.t


let[@inline] (.^()) obj (lens : ('a, 'b) t) = (lens.get[@inlined]) obj
let[@inline] (.^()<-) obj (lens : ('a, 'b) t) v = (lens.set[@inlined]) v obj

let[@inline] ( |- ) f g x = (g [@inlined]) ((f [@inlined]) x)

let[@inline] ( |-- ) l1 l2 =
  Lens.
    { get = ((fun s -> (l2.get [@inlined]) ((l1.get [@inlined]) s)) [@inline])
    ; set = ((fun f s -> (l1.set [@inlined]) ((l2.set [@inlined]) f ((l1.get [@inlined]) s)) s) [@inline]) }
