open Numeric
open Algebra

module type SIG = sig
  module Underlying : FIELD

  module Params : sig
    val a : Underlying.t
    val b : Underlying.t
  end

  (* g(x) = x³ + a x + b *)
  val g : Underlying.t -> Underlying.t

  type t

  val zero : t
  val ( + ) : t -> t -> t
  val ( * ) : Uint.t -> t -> t
  val of_coords : Underlying.t -> Underlying.t -> t option
  val coords : t -> Underlying.t * Underlying.t
end

(* Elliptic curves over a field. *)
module Make
    (F : FIELD)
    (P : sig
      (* y^2 = x^3 + ax + b *)
      val a : F.t
      val b : F.t
    end) =
struct
  module Underlying = F

  module Params = P

  let g x = F.((x * ((x * x) + Params.a)) + Params.b)

  type t = Point of F.t * F.t | Infinity

  let zero = Infinity

  let three = F.(~$3)
  let two = F.(~$2)

  let in_curve x y = F.(y * y = (x * x * x) + (P.a * x) + P.b)

  let ( + ) (p_1 : t) (p_2 : t) =
    match (p_1, p_2) with
    | Infinity, _ -> p_2
    | _, Infinity -> p_1
    | Point (x_1, y_1), Point (x_2, y_2) when F.(x_1 <> x_2) ->
        (* YP (250), case x_1 <> x_2 *)
        let lambda = F.((y_2 - y_1) / (x_2 - x_1)) in
        let x = F.((lambda * lambda) - x_1 - x_2) in
        let y = F.((lambda * (x_1 - x)) - y_1) in
        (* assert (in_curve x y) ; *)
        Point (x, y)
    | Point (_, y_1), Point (_, y_2) when F.(y_1 <> y_2) ->
        (* YP (250), case x_1 = x_2 *)
        Infinity
    | Point (x_1, y_1), Point (_, _) when F.(y_1 <> zero) ->
        (* YP (251), case y_1 = y_2 <> zero *)
        let lambda = F.(((three * x_1 * x_1) + P.a) / (two * y_1)) in
        let x = F.((lambda * lambda) - x_1 - x_1) in
        let y = F.((lambda * (x_1 - x)) - y_1) in
        (* assert (in_curve x y) ;*)
        Point (x, y)
    | _ ->
        (* YP (251), case y_1 = y_2 = zero *)
        Infinity

  let neg = function Infinity -> Infinity | Point (x, y) -> Point (x, F.(zero - y))

  (* YP (252) *)
  let ( * ) (n : Uint.t) (p : t) =
    let n_bits = Uint.significant_bits n in
    let rec loop i p acc =
      if Stdlib.(i >= n_bits) then acc
      else
        let acc = if Uint.(testbit n i) then acc + p else acc in
        loop Stdlib.(i + 1) (p + p) acc
    in
    loop 0 p Infinity

  let of_coords (x : F.t) (y : F.t) =
    if F.(x = zero && y = zero) then Some Infinity else if in_curve x y then Some (Point (x, y)) else None

  let coords = function Infinity -> (F.zero, F.zero) | Point (x, y) -> (x, y)

  (* Cyclic subgroup of an elliptic curve. We assume the order to be a prime number and the subgroup to be
     the only one of that order. *)
  module Subgroup (O : sig
    val order : Uint.t

    (* Not used, but re-exported for a nicer API. *)
    val generator : t
  end) =
  struct
    include O
    module Underlying = Underlying
    module Params = Params
    let g = g
    type curve = t
    module Impl : sig
      type nonrec t = private t
      val ( + ) : t -> t -> t
      val ( * ) : Uint.t -> t -> t
      val neg : t -> t
      val zero : t
      val in_subgroup : curve -> t option
    end = struct
      type nonrec t = t
      let ( + ) (u : t) (v : t) : t = u + v
      let ( * ) (n : Uint.t) (v : t) : t = n * v
      let neg = neg
      let zero = zero
      let in_subgroup p = if p = zero || order * p = zero then Some p else None
    end
    include Impl

    let coords (p : t) = coords (p :> curve)
    let of_coords (x : F.t) (y : F.t) = Option.bind (of_coords x y) in_subgroup

    let generator = Option.get (in_subgroup generator)
  end
end

(* Simplified Shallue-van de Woestijne-Ulas method. See RFC-9380 §6.6 and Appendix F.1. *)
module SWU_method
    (C : SIG)
    (P : sig
      val z : C.Underlying.t

      (* We require the field F to be equipped with squre root and sign operators as defined in RFC-9380
         Appendix I  and §4.1. A generic implementation of this would require us to abstract across Fₚ and
         Fₚ₂ which is unwieldy. *)
      val sqrt : C.Underlying.t -> C.Underlying.t option
      val sgn0 : C.Underlying.t -> bool
    end) =
struct
  module Curve = C
  module F = C.Underlying

  open P

  let a = C.Params.a
  let b = C.Params.b
  let g = C.g
  let g_z = g z

  (* We require the equation in RFC-9380 §6.6 to hold:
       4 a³ + 27 b² ≠ 0

     Additionally, we require the four conditions in §6.6.2 to hold:
       1. z is not a square
       2. z ≠ -1
       3. g(x) - z is irreducible
       4. g(b / (z a)) is a square
   *)
  let () =
    assert (F.((~$4 * a * a * a) + (~$27 * b * b) <> zero)) ;
    assert (Option.is_none (sqrt z)) ;
    assert (F.(z <> zero - one)) ;
    (* We cannot check 3 easily. *)
    assert (Option.is_some (sqrt F.(g (b / (z * a)))))

  (* As RFC-9380 Appendix F.2.1, but we require the underlying F to provide sqrt for us. *)
  let sqrt_ratio u v =
    let q = F.(u / v) in
    match sqrt q with
    | Some root -> (true, root)
    | None ->
        (* Here z * q must be a square.
           Observe that x is a square modulo p if Legendre(x, p) ≠ -1. But since neither z nor q are squares,
           we must have Legendre(z * q, p) = Legendre(z, p) * Legendre(z, q) = -1 * -1 = 1.
           Hence z * q is a square. *)
        (false, Option.get F.(sqrt (z * q)))

  (* RFC-9380, Appendix F.2. *)
  let map_to_curve_simple_swu (u : F.t) =
    let open F in
    let tv1 = u * u in
    let tv1 = z * tv1 in
    let tv2 = tv1 * tv1 in
    let tv2 = tv2 + tv1 in
    let tv3 = tv2 + one in
    let tv3 = b * tv3 in
    let tv4 = if tv2 = zero then z else zero - tv2 in
    let tv4 = a * tv4 in
    let tv2 = tv3 * tv3 in
    let tv6 = tv4 * tv4 in
    let tv5 = a * tv6 in
    let tv2 = tv2 + tv5 in
    let tv2 = tv2 * tv3 in
    let tv6 = tv6 * tv4 in
    let tv5 = b * tv6 in
    let tv2 = tv2 + tv5 in
    let x = tv1 * tv3 in
    let is_gx1_square, y1 = sqrt_ratio tv2 tv6 in
    let y = tv1 * u in
    let y = y * y1 in
    let x = if is_gx1_square then tv3 else x in
    let y = if is_gx1_square then y1 else y in
    let e1 = Stdlib.(sgn0 u = sgn0 y) in
    let y = if e1 then y else zero - y in
    let x = x / tv4 in
    Option.get (C.of_coords x y)
end
