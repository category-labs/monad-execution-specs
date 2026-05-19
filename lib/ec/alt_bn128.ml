open Numeric
open Algebra

(* YP (247) *)
(* field_modulus in py_ecc *)
let p = Uint.of_string "21888242871839275222246405745257275088696311157297823662689037894645226208583"

(* YP (248) *)
(* curve_order in py_ecc *)
let q = Uint.of_string "21888242871839275222246405745257275088548364400416034343698204186575808495617"
let curve_order = q

module F_p = Prime_field (struct
  let modulus = Uint.as_signed p
end)

(* YP (249) *)
(* Curve equation: y² = x³ + 3 *)
module C_1 =
  Curve.Make
    (F_p)
    (struct
      let a = F_p.zero
      let b = F_p.(one + one + one)
    end)
module G_1 = C_1.Subgroup (struct
  let order = curve_order
  let generator = Option.get (C_1.of_coords F_p.one F_p.(one + one))
end)

(* Fₚ₂ = Fₚ[i]/(i²+1) *)
module F_p2 = struct
  include
    Polynomial_extension
      (F_p)
      (struct
        let modulus =
          let open Polynomial_ring (F_p) in
          (monomial_x * monomial_x) + one
      end)

  let i = monomial_x
end

(* YP (253) *)
module C_2 =
  Curve.Make
    (F_p2)
    (struct
      let a = F_p2.zero
      let b = F_p2.(~$3 / (i + ~$9))
    end)
module G_2 = C_2.Subgroup (struct
  let order = curve_order
  let generator =
    Option.get
      (C_2.of_coords
         F_p2.(
           ~@"10857046999023057135944570762232829481370756359578518086990519993285655852781"
           + (i * ~@"11559732032986387107991004021392285783925812861821192530917403151452391805634") )
         F_p2.(
           ~@"8495653923123431417604973247489272438418190587263600148770280649306958101930"
           + (i * ~@"4082367875863433681332203403145435568316851327593401208105741076214120093531") ) )
end)

(* Fₚ₁₂ = Fₚ[w]/(w¹²  − 18w⁶ + 82) *)
module F_p12 = struct
  include
    Polynomial_extension
      (F_p)
      (struct
        let modulus =
          let open Polynomial_ring (F_p) in
          monomial F_p.one 12 - monomial F_p.(~$18) 6 + ~$82
      end)

  let w : t = reduce Underlying_ring.monomial_x
end

(* Powers of w used in the twist map (precomputed once at init). *)
let w2 = F_p12.(F_p12.w * F_p12.w)
let w3 = F_p12.(w2 * F_p12.w)
let w6 = F_p12.(w3 * w3)

(* Frobenius endomorphism on F_p12: x ↦ x^p *)
let f12_pow (f : F_p12.t) (n : Uint.t) : F_p12.t =
  let rec loop n f acc =
    if Uint.(n = zero) then acc
    else
      let n, remainder = Uint.div_rem n Uint.(~$2) in
      let acc = if Uint.(remainder = one) then F_p12.(acc * f) else acc in
      loop n F_p12.(f * f) acc
  in
  loop n f F_p12.one

let frob12 (x : F_p12.t) : F_p12.t = f12_pow x p

(* BN128 pairing using the optimal Ate algorithm.
   final_exp_exp = (p^12 - 1) / r, computed once at module initialization. *)
module BN128_Pairing =
  Pairing.Make
    (F_p12)
    (struct
      let a12 = F_p12.zero
      let b12 = F_p12.(~$3)
      let ate_loop_count = Uint.(~@"29793968203157093288")
      let frob12 = frob12
      let apply_post_loop = true

      let final_exp_exp =
        let p12 = Uint.( ** ) p 12 in
        fst (Uint.div_rem Uint.(p12 - one) q)
    end)

(* "Twist" a point in G_2 (over Fₚ₂) into a point in BN128_Pairing.C_12 (over Fₚ₁₂).
   The isomorphism maps Fₚ₂ ≅ Fₚ[w⁶] inside Fₚ[w]/(w¹² − 18w⁶ + 82).
   See bn128_curve.py::twist for the reference. *)
let twist (pt : G_2.t) : BN128_Pairing.C_12.t =
  match (pt :> C_2.t) with
  | Infinity -> BN128_Pairing.C_12.Infinity
  | Point (xq, yq) ->
      let x0 = F_p2.(xq.$(0)) in
      let x1 = F_p2.(xq.$(1)) in
      let y0 = F_p2.(yq.$(0)) in
      let y1 = F_p2.(yq.$(1)) in
      let nx_c0 = F_p.(x0 - (~$9 * x1)) in
      let ny_c0 = F_p.(y0 - (~$9 * y1)) in
      let nx = F_p12.(const nx_c0 + (const x1 * w6)) in
      let ny = F_p12.(const ny_c0 + (const y1 * w6)) in
      let tx = F_p12.(nx * w2) in
      let ty = F_p12.(ny * w3) in
      BN128_Pairing.C_12.Point (tx, ty)

(* Embed a G1 point (over Fₚ) into BN128_Pairing.C_12 as a constant. *)
let cast_g1 (pt : G_1.t) : BN128_Pairing.C_12.t =
  match (pt :> C_1.t) with
  | Infinity -> BN128_Pairing.C_12.Infinity
  | Point (x, y) -> BN128_Pairing.C_12.Point (F_p12.const x, F_p12.const y)

(* Check that ∏ e(P_i, Q_i) = 1 in Fₚ₁₂. *)
let pairing_check (pairs : (G_1.t * G_2.t) list) : bool =
  BN128_Pairing.pairing_check (List.map (fun (p, q) -> (twist q, cast_g1 p)) pairs)
