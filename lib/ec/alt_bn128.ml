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
module F_p2 = Complex_extension (F_p)

(* YP (253) *)
module C_2 =
  Curve.Make
    (F_p2)
    (struct
      let a = F_p2.zero
      let b = F_p2.(~$3 / (i + ~$9))
    end)

(* YP (254) *)
let p_2 =
  Option.get
    (C_2.of_coords
       F_p2.(
         ~@"10857046999023057135944570762232829481370756359578518086990519993285655852781"
         + (i * ~@"11559732032986387107991004021392285783925812861821192530917403151452391805634") )
       F_p2.(
         ~@"8495653923123431417604973247489272438418190587263600148770280649306958101930"
         + (i * ~@"4082367875863433681332203403145435568316851327593401208105741076214120093531") ) )
module G_2 = C_2.Subgroup (struct
  let order = curve_order
  let generator = p_2
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

(* BN128 pairing using the optimal Ate algorithm. *)
module BN128_Pairing =
  Pairing.Make
    (F_p12)
    (struct
      let a = F_p12.zero
      let b = F_p12.(~$3)

      let field_characteristic = p
      let curve_order = curve_order

      let ate_loop_count = Uint.(~@"29793968203157093288")

      let curve_family = Pairing.BN

      (* Iterated frobenius maps. *)
      let frob_p = F_p12.automorphism (fun px -> F_p12.(px ** p))
      let frob_p2 = F_p12.automorphism (fun px -> frob_p (frob_p px))
      let frob_p6 = F_p12.automorphism (fun px -> frob_p2 (frob_p2 (frob_p2 px)))
    end)

(* "Twist" a point in G_2 (over Fₚ₂) into a point in BN128_Pairing.C_12 (over Fₚ₁₂).
   See py_ecc bn128_curve.py for the reference. *)
let twist =
  (* Powers of w used in the twist map (precomputed once at init). *)
  let w2 = F_p12.(w * w) in
  let w3 = F_p12.(w2 * w) in
  let w6 = F_p12.(w3 * w3) in

  fun (pt : G_2.t) : BN128_Pairing.C_12.t ->
    match (pt :> C_2.t) with
    | Infinity -> BN128_Pairing.C_12.Infinity
    | Point (xq, yq) ->
        let nx_c0 = F_p.(xq.re - (~$9 * xq.im)) in
        let ny_c0 = F_p.(yq.re - (~$9 * yq.im)) in
        let nx = F_p12.(const nx_c0 + (const xq.im * w6)) in
        let ny = F_p12.(const ny_c0 + (const yq.im * w6)) in
        let tx = F_p12.(nx * w2) in
        let ty = F_p12.(ny * w3) in
        BN128_Pairing.C_12.Point (tx, ty)

(* Embed a G1 point (over Fₚ) into BN128_Pairing.C_12 as a constant. *)
let embed_g1_c12 (pt : G_1.t) : BN128_Pairing.C_12.t =
  match (pt :> C_1.t) with
  | Infinity -> BN128_Pairing.C_12.Infinity
  | Point (x, y) -> BN128_Pairing.C_12.Point (F_p12.const x, F_p12.const y)

(* Check that ∏ e(P_i, Q_i) = 1 in Fₚ₁₂. Corresponds to YP (255), YP (256). *)
let pairing_check (pairs : (G_1.t * G_2.t) list) : bool =
  BN128_Pairing.pairing_check (List.map (fun (p, q) -> (twist q, embed_g1_c12 p)) pairs)
