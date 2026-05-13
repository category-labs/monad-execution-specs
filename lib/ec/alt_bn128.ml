open Numeric
open Algebra

module Elliptic_curve
    (F : FIELD)
    (P : sig
      (* y^2 = x^3 + ax + b *)
      val a : F.t
      val b : F.t
    end) =
struct
  type t = Point of F.t * F.t | Infinity

  let of_coords (x : F.t) (y : F.t) =
    if F.(x = zero) && F.(y = zero) then Some Infinity
    else if F.(y * y = (x * x * x) + (P.a * x) + P.b) then Some (Point (x, y))
    else None

  let three = F.(~@"3")
  let two = F.(~@"2")

  let ( + ) (p_1 : t) (p_2 : t) =
    match (p_1, p_2) with
    | Infinity, _ -> p_2
    | _, Infinity -> p_1
    | Point (x_1, y_1), Point (x_2, y_2) when F.(x_1 <> x_2) ->
        (* YP (250), case x_1 <> x_2 *)
        let lambda = F.((y_2 - y_1) / (x_2 - x_1)) in
        let x = F.((lambda * lambda) - x_1 - x_2) in
        let y = F.((lambda * (x_1 - x)) - y_1) in
        assert (Option.is_some (of_coords x y)) ;
        Point (x, y)
    | Point (_, y_1), Point (_, y_2) when F.(y_1 <> y_2) ->
        (* YP (250), case x_1 = x_2 *)
        Infinity
    | Point (x_1, y_1), Point (_, _) when F.(y_1 <> zero) ->
        (* YP (251), case y_1 = y_2 <> zero *)
        let lambda = F.(((three * x_1 * x_1) + P.a) / (two * y_1)) in
        let x = F.((lambda * lambda) - x_1 - x_1) in
        let y = F.((lambda * (x_1 - x)) - y_1) in
        assert (Option.is_some (of_coords x y)) ;
        Point (x, y)
    | _ ->
        (* YP (251), case y_1 = y_2 = zero *)
        Infinity

  (* YP (252) *)
  let ( * ) (n : Uint.t) (p : t) =
    let rec loop n acc = if Uint.(n = zero) then acc else loop Uint.(n - one) (acc + p) in
    loop n Infinity
end

(* YP (247) *)
(* field_modulus in py_ecc *)
let p = Uint.of_string "21888242871839275222246405745257275088696311157297823662689037894645226208583"

(* YP (248) *)
(* curve_order in py_ecc *)
let q = Uint.of_string "21888242871839275222246405745257275088548364400416034343698204186575808495617"

module F_p = Prime_field (struct
  let modulus = Uint.as_signed p
end)

(* YP (249) *)
(* Curve equation: y² = x³ + 3 *)
module C_1 =
  Elliptic_curve
    (F_p)
    (struct
      let a = F_p.zero
      let b = F_p.(one + one + one)
    end)

(* p₁ = (1, 2) ∈ C₁ *)
let p_1 = Option.get (C_1.of_coords F_p.(one) F_p.(one + one))

(* Fₚ₂ = Fₚ[x]/(x²+1) *)
module F_p2 = struct
  include
    Polynomial_extension
      (F_p)
      (struct
        let modulus =
          let open Polynomial_ring (F_p) in
          (x * x) + one
      end)
  let i = x
end

(* YP (253) *)
module C_2 =
  Elliptic_curve
    (F_p2)
    (struct
      let a = F_p2.zero
      let b = F_p2.(~@"3" / (i + ~@"9"))
    end)

let p_2 =
  Option.get
    (C_2.of_coords
       F_p2.(
         ~@"8495653923123431417604973247489272438418190587263600148770280649306958101930"
         + (i * ~@"4082367875863433681332203403145435568316851327593401208105741076214120093531") )
       F_p2.(
         ~@"10857046999023057135944570762232829481370756359578518086990519993285655852781"
         + (i * ~@"11559732032986387107991004021392285783925812861821192530917403151452391805634") ) )
