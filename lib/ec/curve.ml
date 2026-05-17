open Numeric
open Algebra

module type SIG = sig
  module Underlying : FIELD

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

  type t = Point of F.t * F.t | Infinity

  let zero = Infinity

  let three = F.(~@"3")
  let two = F.(~@"2")

  let eqn_l y = F.(y * y)
  let eqn_r x = F.((x * x * x) + (P.a * x) + P.b)
  let in_curve ?tracer x y =
    let l = eqn_l y in
    let r = eqn_r x in
    Option.iter
      (fun to_string ->
        Format.printf "x: %s\n" (to_string x) ;
        Format.printf "y: %s\n" (to_string y) ;
        Format.printf "l: %s\n" (to_string l) ;
        Format.printf "r: %s\n" (to_string r) )
      tracer ;
    F.(l = r)

  let ( + ) (p_1 : t) (p_2 : t) =
    match (p_1, p_2) with
    | Infinity, _ -> p_2
    | _, Infinity -> p_1
    | Point (x_1, y_1), Point (x_2, y_2) when F.(x_1 <> x_2) ->
        (* YP (250), case x_1 <> x_2 *)
        let lambda = F.((y_2 - y_1) / (x_2 - x_1)) in
        let x = F.((lambda * lambda) - x_1 - x_2) in
        let y = F.((lambda * (x_1 - x)) - y_1) in
        assert (in_curve x y) ;
        Point (x, y)
    | Point (_, y_1), Point (_, y_2) when F.(y_1 <> y_2) ->
        (* YP (250), case x_1 = x_2 *)
        Infinity
    | Point (x_1, y_1), Point (_, _) when F.(y_1 <> zero) ->
        (* YP (251), case y_1 = y_2 <> zero *)
        let lambda = F.(((three * x_1 * x_1) + P.a) / (two * y_1)) in
        let x = F.((lambda * lambda) - x_1 - x_1) in
        let y = F.((lambda * (x_1 - x)) - y_1) in
        assert (in_curve x y) ;
        Point (x, y)
    | _ ->
        (* YP (251), case y_1 = y_2 = zero *)
        Infinity

  let neg = function Infinity -> Infinity | Point (x, y) -> Point (x, F.(zero - y))

  (* YP (252) *)
  let ( * ) (n : Uint.t) (p : t) =
    let rec loop n p acc =
      if Uint.(n = zero) then acc
      else
        let n, remainder = Uint.(div_rem n ~$2) in
        let acc = if Uint.(remainder = one) then acc + p else acc in
        loop n (p + p) acc
    in
    loop n p Infinity

  let of_coords (x : F.t) (y : F.t) = if in_curve x y then Some (Point (x, y)) else None

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
