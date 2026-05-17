open Numeric
open Algebra

(* BLS12-381 field modulus *)
let p =
  Uint.of_string
    "4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787"

(* BLS12-381 curve order *)
let q = Uint.of_string "52435875175126190479447740508185965837690552500527637822603658699938581184513"
let curve_order = q

module F_p = struct
  include Prime_field (struct
    let modulus = Uint.as_signed p
  end)

  let sqrt_opt = Option.get sqrt_opt
end

(* G1 curve: y² = x³ + 4 *)
module C_1 =
  Curve.Make
    (F_p)
    (struct
      let a = F_p.zero
      let b = F_p.(~@"4")
    end)
module G_1 = C_1.Subgroup (struct
  let order = curve_order
  let generator =
    Option.get
      (C_1.of_coords
         F_p.(
           ~@"3685416753713387016781088315183077757961620795782546409894578378688607592378376318836054947676345821548104185464507" )
         F_p.(
           ~@"1339506544944476473020471379941921221584933875938349620426543736416511423956333506472724655353366534992391756441569" ) )
end)

(* Fₚ₂ = Fₚ[i]/(i² + 1) *)
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

  (* Square root in F_p2 = Fₚ[i]/(i²+1).
     Let v = a + bi.
       - If b = 0, we take the square root of a or -a in Fₚ
       - If b ≠ 0, then sqrt(a + bi) = sqrt((a±r)/2) + (b/(2c))i *)
  let sqrt_opt =
    let two = F_p.(one + one) in
    fun (v : t) : t option ->
      Option.(
        let a, b = (v.$(0), v.$(1)) in
        if F_p.(b = zero) then
          (* b = 0, return sqrt(a) (which may be imaginary). *)
          match F_p.sqrt_opt a with
          | Some y -> return (const y)
          | None ->
              (* Root must be imaginary. *)
              let$ w = F_p.(sqrt_opt (zero - a)) in
              return (i * const w)
        else
          let$ r = F_p.(sqrt_opt ((a * a) + (b * b))) in
          let$ c =
            match F_p.(sqrt_opt ((a + r) / two)) with
            | Some c -> return c
            | None -> F_p.(sqrt_opt ((a - r) / two))
          in
          let d = F_p.(b / (two * c)) in
          return (const c + (i * const d)) )
end

(* G2 twisted curve: y² = x³ + (4 + 4u) over Fₚ₂ *)
module C_2 =
  Curve.Make
    (F_p2)
    (struct
      let a = F_p2.zero
      let b = F_p2.(~@"4" + (i * ~@"4"))
    end)
module G_2 = C_2.Subgroup (struct
  let order = curve_order

  let generator =
    Option.get
      (C_2.of_coords
         F_p2.(
           ~@"352701069587466618187139116011060144890029952792775240219908644239793785735715026873347600343865175952761926303160"
           + i
             * ~@"3059144344244213709971259814753781636986470325476647558659373206291635324768958432433509563104347017837885763365758" )
         F_p2.(
           ~@"1985150602287291935568054521177171638300868978215655730859378665066344726373823718423869104263333984641494340347905"
           + i
             * ~@"927553665492332455747201965776037880757740193453592970025027978793976877002675564980949289727957565575433344219582" ) )
end)

(* Fₚ₁₂ = Fₚ[w]/(w¹² − 2w⁶ + 2) *)
module F_p12 = struct
  include
    Polynomial_extension
      (F_p)
      (struct
        let modulus =
          let two = F_p.(one + one) in
          let open Polynomial_ring (F_p) in
          monomial F_p.one 12 - monomial two 6 + const two
      end)

  let w : t = reduce Underlying_ring.monomial_x
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
let twist (pt : G_2.t) : BLS12_Pairing.C12.t =
  match (pt :> C_2.t) with
  | Infinity -> BLS12_Pairing.C12.Infinity
  | Point (xq, yq) ->
      let x0 = F_p2.(xq.$(0)) in
      let x1 = F_p2.(xq.$(1)) in
      let y0 = F_p2.(yq.$(0)) in
      let y1 = F_p2.(yq.$(1)) in
      let tx = F_p12.((const F_p.(x0 - x1) * winv2) + (const x1 * w4)) in
      let ty = F_p12.((const F_p.(y0 - y1) * winv3) + (const y1 * w3)) in
      BLS12_Pairing.C12.Point (tx, ty)

(* Embed a G1 point (over Fₚ) into BLS12_Pairing.C12 as a constant. *)
let cast_g1 (pt : G_1.t) : BLS12_Pairing.C12.t =
  match (pt :> C_1.t) with
  | Infinity -> BLS12_Pairing.C12.Infinity
  | Point (x, y) -> BLS12_Pairing.C12.Point (F_p12.const x, F_p12.const y)

(* Check that ∏ e(Pᵢ, Qᵢ) = 1 in Fₚ₁₂, where Pᵢ ∈ G_1, Qᵢ ∈ G_2. *)
let pairing_check (pairs : (G_1.t * G_2.t) list) : bool =
  BLS12_Pairing.pairing_check (List.map (fun (p, q) -> (twist q, cast_g1 p)) pairs)
