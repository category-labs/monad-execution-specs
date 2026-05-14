open Numeric
open Algebra

(* BLS12-381 field modulus *)
let p = Uint.of_string "4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787"

(* BLS12-381 curve order *)
let q = Uint.of_string "52435875175126190479447740508185965837690552500527637822603658699938581184513"

module F_p = Prime_field (struct
  let modulus = Uint.as_signed p
end)

(* G1 curve: y² = x³ + 4 *)
module C_1 =
  Curve.Make
    (F_p)
    (struct
      let a = F_p.zero
      let b = F_p.(~@"4")
    end)

(* G1 generator *)
let p_1 =
  Option.get
    (C_1.of_coords
       F_p.(~@"3685416753713387016781088315183077757961620795782546409894578378688607592378376318836054947676345821548104185464507")
       F_p.(~@"1339506544944476473020471379941921221584933875938349620426543736416511423956333506472724655353366534992391756441569") )

(* Fₚ₂ = Fₚ[u]/(u² + 1) *)
module F_p2 = struct
  module Poly2 = Polynomial_ring (F_p)

  include
    Polynomial_extension
      (F_p)
      (struct
        let modulus = Poly2.((x * x) + one)
      end)

  let i = x

  let of_fp (fp : F_p.t) : t = reduce (Poly2.const fp)

  let get_coeff (e : t) (n : int) : F_p.t =
    let arr = ((e :> Poly2.t) :> F_p.t Iarray.t) in
    if n < Iarray.length arr then Iarray.get arr n else F_p.zero
end

(* G2 twisted curve: y² = x³ + (4 + 4u) over Fₚ₂ *)
module C_2 =
  Curve.Make
    (F_p2)
    (struct
      let a = F_p2.zero
      let b = F_p2.(~@"4" + (i * ~@"4"))
    end)

(* G2 generator *)
let p_2 =
  Option.get
    (C_2.of_coords
       F_p2.(
         ~@"352701069587466618187139116011060144890029952792775240219908644239793785735715026873347600343865175952761926303160"
         + (i * ~@"3059144344244213709971259814753781636986470325476647558659373206291635324768958432433509563104347017837885763365758") )
       F_p2.(
         ~@"1985150602287291935568054521177171638300868978215655730859378665066344726373823718423869104263333984641494340347905"
         + (i * ~@"927553665492332455747201965776037880757740193453592970025027978793976877002675564980949289727957565575433344219582") ) )

(* Fₚ₁₂ = Fₚ[w]/(w¹² − 2w⁶ + 2) *)
module F_p12 = struct
  module Poly12 = Polynomial_ring (F_p)

  include
    Quotient_field
      (Poly12)
      (struct
        let modulus =
          let open Poly12 in
          let x6 = x * x * x * x * x * x in
          (x6 * x6) - (~@"2" * x6) + ~@"2"
      end)

  let w : t = reduce Poly12.x

  let embed_fp (x : F_p.t) : t = reduce (Poly12.const x)
end

(* Powers of w used in the M-type twist map (precomputed once at init). *)
let w2 = F_p12.(F_p12.w * F_p12.w)
let w3 = F_p12.(w2 * F_p12.w)
let w4 = F_p12.(w3 * F_p12.w)
let w6 = F_p12.(w3 * w3)

(* M-type twist divides by w² and w³ rather than multiplying. *)
let winv2 = F_p12.(one / w2)
let winv3 = F_p12.(one / w3)

(* BLS12-381 pairing using the optimal Ate algorithm.
   apply_post_loop = false: BLS12-381 uses an M-type twist so no Frobenius
   correction is needed after the Miller loop (unlike BN128's D-type twist). *)
module BLS12_Pairing =
  Pairing.Make
    (F_p12)
    (struct
      let a12 = F_p12.zero
      let b12 = F_p12.(~@"4")
      let ate_loop_count = Uint.of_string "15132376222941642752"
      let frob12 (x : F_p12.t) : F_p12.t = x
      let apply_post_loop = false

      let final_exp_exp =
        let p12 = Uint.( ** ) p 12 in
        fst (Uint.div_rem Uint.(p12 - one) q)
    end)

(* "Twist" a G2 point (over Fₚ₂) into BLS12_Pairing.C12 (over Fₚ₁₂).
   BLS12-381 M-type twist: the field isomorphism maps u ↦ w⁶ − 1, so an
   element a₀ + a₁u becomes (a₀ − a₁) + a₁w⁶. In projective coordinates
   the twisted point has nz = w³ (for z = 1), giving affine coordinates:
     x_twisted = ((x₀ − x₁) + x₁w⁶) · w⁻²  =  (x₀ − x₁)w⁻² + x₁w⁴
     y_twisted = ((y₀ − y₁) + y₁w⁶) · w⁻³  =  (y₀ − y₁)w⁻³ + y₁w³  *)
let twist (pt : C_2.t) : BLS12_Pairing.C12.t =
  match pt with
  | C_2.Infinity -> BLS12_Pairing.C12.Infinity
  | C_2.Point (xq, yq) ->
      let x0 = F_p2.get_coeff xq 0 in
      let x1 = F_p2.get_coeff xq 1 in
      let y0 = F_p2.get_coeff yq 0 in
      let y1 = F_p2.get_coeff yq 1 in
      let emb = F_p12.embed_fp in
      let tx = F_p12.(emb F_p.(x0 - x1) * winv2 + emb x1 * w4) in
      let ty = F_p12.(emb F_p.(y0 - y1) * winv3 + emb y1 * w3) in
      BLS12_Pairing.C12.Point (tx, ty)

(* Embed a G1 point (over Fₚ) into BLS12_Pairing.C12 as a constant. *)
let cast_g1 (pt : C_1.t) : BLS12_Pairing.C12.t =
  match pt with
  | C_1.Infinity -> BLS12_Pairing.C12.Infinity
  | C_1.Point (x, y) ->
      BLS12_Pairing.C12.Point (F_p12.embed_fp x, F_p12.embed_fp y)

(* Check that ∏ e(Pᵢ, Qᵢ) = 1 in Fₚ₁₂, where Pᵢ ∈ C_1, Qᵢ ∈ C_2. *)
let pairing_check (pairs : (C_1.t * C_2.t) list) : bool =
  BLS12_Pairing.pairing_check
    (List.map (fun (p, q) -> (twist q, cast_g1 p)) pairs)
