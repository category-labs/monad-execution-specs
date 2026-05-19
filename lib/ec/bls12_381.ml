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
      let b = F_p.(~$4)
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
      let b = F_p2.(~$4 + (i * ~$4))
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
      let b12 = F_p12.(~$4)
      let ate_loop_count = Uint.(~@"15132376222941642752")
      let frob12 (x : F_p12.t) : F_p12.t = x
      let apply_post_loop = false

      let final_exp_exp =
        let p12 = Uint.( ** ) p 12 in
        fst (Uint.div_rem Uint.(p12 - one) q)
    end)

(* "Twist" a G2 point (over Fₚ₂) into BLS12_Pairing.C_12 (over Fₚ₁₂).
   BLS12-381 M-type twist: the field isomorphism maps u ↦ w⁶ − 1, so an
   element a₀ + a₁u becomes (a₀ − a₁) + a₁w⁶. In projective coordinates
   the twisted point has nz = w³ (for z = 1), giving affine coordinates:
     x_twisted = ((x₀ − x₁) + x₁w⁶) · w⁻²  =  (x₀ − x₁)w⁻² + x₁w⁴
     y_twisted = ((y₀ − y₁) + y₁w⁶) · w⁻³  =  (y₀ − y₁)w⁻³ + y₁w³  *)
let twist (pt : G_2.t) : BLS12_Pairing.C_12.t =
  match (pt :> C_2.t) with
  | Infinity -> BLS12_Pairing.C_12.Infinity
  | Point (xq, yq) ->
      let x0 = F_p2.(xq.$(0)) in
      let x1 = F_p2.(xq.$(1)) in
      let y0 = F_p2.(yq.$(0)) in
      let y1 = F_p2.(yq.$(1)) in
      let tx = F_p12.((const F_p.(x0 - x1) * winv2) + (const x1 * w4)) in
      let ty = F_p12.((const F_p.(y0 - y1) * winv3) + (const y1 * w3)) in
      BLS12_Pairing.C_12.Point (tx, ty)

(* Embed a G1 point (over Fₚ) into BLS12_Pairing.C_12 as a constant. *)
let cast_g1 (pt : G_1.t) : BLS12_Pairing.C_12.t =
  match (pt :> C_1.t) with
  | Infinity -> BLS12_Pairing.C_12.Infinity
  | Point (x, y) -> BLS12_Pairing.C_12.Point (F_p12.const x, F_p12.const y)

(* Check that ∏ e(Pᵢ, Qᵢ) = 1 in Fₚ₁₂. *)
let pairing_check (pairs : (G_1.t * G_2.t) list) : bool =
  BLS12_Pairing.pairing_check (List.map (fun (p, q) -> (twist q, cast_g1 p)) pairs)

(* SWU curve and isogeny map for Fₚ. All parameters taken from RFC-9380 §8.8.1. *)
module F_p_SWU_curve = struct
  include
    Curve.Make
      (F_p)
      (struct
        open F_p
        let a =
          ~@"0x144698A3B8E9433D693A02C96D4982B0EA985383EE66A8D8E8981AEFD881AC98936F8DA0E0F97F5CF428082D584C1D"
        let b =
          ~@"0x12E2908D11688030018B12E8753EEE3B2016C1F0F24F4070A0B9C14FCEF35EF55A23215A316CEAA5D1CC48E98E172BE0"
      end)

  (* 11-isogeny coefficient tables as polynomials. Constants taken from RFC-9380 Appendix E.2. *)
  module F_px = Polynomial_ring (F_p)
  let x_num =
    F_px.trim
      F_p.
        [| ~@"0x11A05F2B1E833340B809101DD99815856B303E88A2D7005FF2627B56CDB4E2C85610C2D5F2E62D6EAEAC1662734649B7"
         ; ~@"0x17294ED3E943AB2F0588BAB22147A81C7C17E75B2F6A8417F565E33C70D1E86B4838F2A6F318C356E834EEF1B3CB83BB"
         ; ~@"0xD54005DB97678EC1D1048C5D10A9A1BCE032473295983E56878E501EC68E25C958C3E3D2A09729FE0179F9DAC9EDCB0"
         ; ~@"0x1778E7166FCC6DB74E0609D307E55412D7F5E4656A8DBF25F1B33289F1B330835336E25CE3107193C5B388641D9B6861"
         ; ~@"0xE99726A3199F4436642B4B3E4118E5499DB995A1257FB3F086EEB65982FAC18985A286F301E77C451154CE9AC8895D9"
         ; ~@"0x1630C3250D7313FF01D1201BF7A74AB5DB3CB17DD952799B9ED3AB9097E68F90A0870D2DCAE73D19CD13C1C66F652983"
         ; ~@"0xD6ED6553FE44D296A3726C38AE652BFB11586264F0F8CE19008E218F9C86B2A8DA25128C1052ECADDD7F225A139ED84"
         ; ~@"0x17B81E7701ABDBE2E8743884D1117E53356DE5AB275B4DB1A682C62EF0F2753339B7C8F8C8F475AF9CCB5618E3F0C88E"
         ; ~@"0x80D3CF1F9A78FC47B90B33563BE990DC43B756CE79F5574A2C596C928C5D1DE4FA295F296B74E956D71986A8497E317"
         ; ~@"0x169B1F8E1BCFA7C42E0C37515D138F22DD2ECB803A0C5C99676314BAF4BB1B7FA3190B2EDC0327797F241067BE390C9E"
         ; ~@"0x10321DA079CE07E272D8EC09D2565B0DFA7DCCDDE6787F96D50AF36003B14866F69B771F8C285DECCA67DF3F1605FB7B"
         ; ~@"0x6E08C248E260E70BD1E962381EDEE3D31D79D7E22C837BC23C0BF1BC24C6B68C24B1B80B64D391FA9C8BA2E8BA2D229"
        |]
  let x_den =
    F_px.trim
      F_p.
        [| ~@"0x8CA8D548CFF19AE18B2E62F4BD3FA6F01D5EF4BA35B48BA9C9588617FC8AC62B558D681BE343DF8993CF9FA40D21B1C"
         ; ~@"0x12561A5DEB559C4348B4711298E536367041E8CA0CF0800C0126C2588C48BF5713DAA8846CB026E9E5C8276EC82B3BFF"
         ; ~@"0xB2962FE57A3225E8137E629BFF2991F6F89416F5A718CD1FCA64E00B11ACEACD6A3D0967C94FEDCFCC239BA5CB83E19"
         ; ~@"0x3425581A58AE2FEC83AAFEF7C40EB545B08243F16B1655154CCA8ABC28D6FD04976D5243EECF5C4130DE8938DC62CD8"
         ; ~@"0x13A8E162022914A80A6F1D5F43E7A07DFFDFC759A12062BB8D6B44E833B306DA9BD29BA81F35781D539D395B3532A21E"
         ; ~@"0xE7355F8E4E667B955390F7F0506C6E9395735E9CE9CAD4D0A43BCEF24B8982F7400D24BC4228F11C02DF9A29F6304A5"
         ; ~@"0x772CAACF16936190F3E0C63E0596721570F5799AF53A1894E2E073062AEDE9CEA73B3538F0DE06CEC2574496EE84A3A"
         ; ~@"0x14A7AC2A9D64A8B230B3F5B074CF01996E7F63C21BCA68A81996E1CDF9822C580FA5B9489D11E2D311F7D99BBDCC5A5E"
         ; ~@"0xA10ECF6ADA54F825E920B3DAFC7A3CCE07F8D1D7161366B74100DA67F39883503826692ABBA43704776EC3A79A1D641"
         ; ~@"0x95FC13AB9E92AD4476D6E3EB3A56680F682B4EE96F7D03776DF533978F31C1593174E4B4B7865002D6384D168ECDD0A"
         ; ~@"1" |]
  let y_num =
    F_px.trim
      F_p.
        [| ~@"0x90D97C81BA24EE0259D1F094980DCFA11AD138E48A869522B52AF6C956543D3CD0C7AEE9B3BA3C2BE9845719707BB33"
         ; ~@"0x134996A104EE5811D51036D776FB46831223E96C254F383D0F906343EB67AD34D6C56711962FA8BFE097E75A2E41C696"
         ; ~@"0xCC786BAA966E66F4A384C86A3B49942552E2D658A31CE2C344BE4B91400DA7D26D521628B00523B8DFE240C72DE1F6"
         ; ~@"0x1F86376E8981C217898751AD8746757D42AA7B90EEB791C09E4A3EC03251CF9DE405ABA9EC61DECA6355C77B0E5F4CB"
         ; ~@"0x8CC03FDEFE0FF135CAF4FE2A21529C4195536FBE3CE50B879833FD221351ADC2EE7F8DC099040A841B6DAECF2E8FEDB"
         ; ~@"0x16603FCA40634B6A2211E11DB8F0A6A074A7D0D4AFADB7BD76505C3D3AD5544E203F6326C95A807299B23AB13633A5F0"
         ; ~@"0x4AB0B9BCFAC1BBCB2C977D027796B3CE75BB8CA2BE184CB5231413C4D634F3747A87AC2460F415EC961F8855FE9D6F2"
         ; ~@"0x987C8D5333AB86FDE9926BD2CA6C674170A05BFE3BDD81FFD038DA6C26C842642F64550FEDFE935A15E4CA31870FB29"
         ; ~@"0x9FC4018BD96684BE88C9E221E4DA1BB8F3ABD16679DC26C1E8B6E6A1F20CABE69D65201C78607A360370E577BDBA587"
         ; ~@"0xE1BBA7A1186BDB5223ABDE7ADA14A23C42A0CA7915AF6FE06985E7ED1E4D43B9B3F7055DD4EBA6F2BAFAAEBCA731C30"
         ; ~@"0x19713E47937CD1BE0DFD0B8F1D43FB93CD2FCBCB6CAF493FD1183E416389E61031BF3A5CCE3FBAFCE813711AD011C132"
         ; ~@"0x18B46A908F36F6DEB918C143FED2EDCC523559B8AAF0C2462E6BFE7F911F643249D9CDF41B44D606CE07C8A4D0074D8E"
         ; ~@"0xB182CAC101B9399D155096004F53F447AA7B12A3426B08EC02710E807B4633F06C851C1919211F20D4C04F00B971EF8"
         ; ~@"0x245A394AD1ECA9B72FC00AE7BE315DC757B3B080D4C158013E6632D3C40659CC6CF90AD1C232A6442D9D3F5DB980133"
         ; ~@"0x5C129645E44CF1102A159F748C4A3FC5E673D81D7E86568D9AB0F5D396A7CE46BA1049B6579AFB7866B1E715475224B"
         ; ~@"0x15E6BE4E990F03CE4EA50B3B42DF2EB5CB181D8F84965A3957ADD4FA95AF01B2B665027EFEC01C7704B456BE69C8B604"
        |]
  let y_den =
    F_px.trim
      F_p.
        [| ~@"0x16112C4C3A9C98B252181140FAD0EAE9601A6DE578980BE6EEC3232B5BE72E7A07F3688EF60C206D01479253B03663C1"
         ; ~@"0x1962D75C2381201E1A0CBD6C43C348B885C84FF731C4D59CA4A10356F453E01F78A4260763529E3532F6102C2E49A03D"
         ; ~@"0x58DF3306640DA276FAAAE7D6E8EB15778C4855551AE7F310C35A5DD279CD2ECA6757CD636F96F891E2538B53DBF67F2"
         ; ~@"0x16B7D288798E5395F20D23BF89EDB4D1D115C5DBDDBCD30E123DA489E726AF41727364F2C28297ADA8D26D98445F5416"
         ; ~@"0xBE0E079545F43E4B00CC912F8228DDCC6D19C9F0F69BBB0542EDA0FC9DEC916A20B15DC0FD2EDEDDA39142311A5001D"
         ; ~@"0x8D9E5297186DB2D9FB266EAAC783182B70152C65550D881C5ECD87B6F0F5A6449F38DB9DFA9CCE202C6477FAAF9B7AC"
         ; ~@"0x166007C08A99DB2FC3BA8734ACE9824B5EECFDFA8D0CF8EF5DD365BC400A0051D5FA9C01A58B1FB93D1A1399126A775C"
         ; ~@"0x16A3EF08BE3EA7EA03BCDDFABBA6FF6EE5A4375EFA1F4FD7FEB34FD206357132B920F5B00801DEE460EE415A15812ED9"
         ; ~@"0x1866C8ED336C61231A1BE54FD1D74CC4F9FB0CE4C6AF5920ABC5750C4BF39B4852CFE2F7BB9248836B233D9D55535D4A"
         ; ~@"0x167A55CDA70A6E1CEA820597D94A84903216F763E13D87BB5308592E7EA7D4FBC7385EA3D529B35E346EF48BB8913F55"
         ; ~@"0x4D2F259EEA405BD48F010A01AD2911D9C6DD039BB61A6290E591B36E636A5C871A5C29F4F83060400F8B49CBA8F6AA8"
         ; ~@"0xACCBB67481D033FF5852C1E48C50C477F94FF8AEFCE42D28C0F9A88CEA7913516F968986F7EBBEA9684B529E2561092"
         ; ~@"0xAD6B9514C767FE3C3613144B45F1496543346D98ADF02267D5CEEF9A00D9B8693000763E3B90AC11E99B138573345CC"
         ; ~@"0x2660400EB2E4F3B628BDD0D53CD76F2BF565B94E72927C1CB748DF27942480E420517BD8714CC80D1FADC1326ED06F7"
         ; ~@"0xE0FA1D816DDC03E6B24255E0D7819C171C40F65E273B853324EFCD6356CAA205CA2F570F13497804415473A1D634B8F"
         ; ~@"1" |]
  let h_eff = Uint.(~@"0xD201000000010001")
  let isogeny (pt : t) : G_1.t =
    let x, y = coords pt in
    let x_g1 = F_p.(F_px.eval x_num x / F_px.eval x_den x) in
    let y_g1 = F_p.(F_px.eval y_num x / F_px.eval y_den x * y) in

    let p = Option.get (C_1.of_coords x_g1 y_g1) in
    Option.get (G_1.in_subgroup C_1.(h_eff * p))
end
module F_p_SWU =
  Curve.SWU_method
    (F_p_SWU_curve)
    (struct
      open F_p
      let z = ~$11
      let sqrt = sqrt_opt

      (* As sgn0_m_eq_1 in RFC-9380 §4.1. *)
      let sgn0 (x : t) = Integer.(one = modulo (x :> t) ~$2)
    end)

(* EIP-2537 §5.4: SWU map + 11-isogeny + cofactor clearing from Fₚ to G₁. *)
let map_fp_to_g1 (t : F_p.t) : G_1.t =
  (* The SWU map gives us a point on the 11-isogenous auxiliary curve C_p_SWU_curve. *)
  let swu_t = F_p_SWU.map_to_curve_simple_swu t in
  F_p_SWU_curve.isogeny swu_t

(* SWU curve and isogeny map for Fₚ₂. All parameters taken from RFC-9380 §8.8.2. *)
module F_p2_SWU_curve = struct
  include
    Curve.Make
      (F_p2)
      (struct
        open F_p2
        let a = ~$240 * i
        let b = ~$1012 * (~$1 + i)
      end)

  (* 3-isogeny coefficient tables as polynomials. Constants taken from RFC-9380 Appendix E.3. *)
  module F_p2x = Polynomial_ring (F_p2)
  let x_num =
    F_p2x.trim
      F_p2.
        [| ~@"0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97d6"
           + ~@"0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97d6"
             * i
         ; ~@"0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71a"
           * i
         ; ~@"0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71e"
           + ~@"0x8ab05f8bdd54cde190937e76bc3e447cc27c3d6fbd7063fcd104635a790520c0a395554e5c6aaaa9354ffffffffe38d"
             * i
         ; ~@"0x171d6541fa38ccfaed6dea691f5fb614cb14b4e7f4e810aa22d6108f142b85757098e38d0f671c7188e2aaaaaaaa5ed1"
        |]
  let x_den =
    F_p2x.trim
      F_p2.
        [| ~@"0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa63"
           * i
         ; ~@"0xc"
           + ~@"0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa9f"
             * i
         ; ~@"1" |]
  let y_num =
    F_p2x.trim
      F_p2.
        [| ~@"0x1530477c7ab4113b59a4c18b076d11930f7da5d4a07f649bf54439d87d27e500fc8c25ebf8c92f6812cfc71c71c6d706"
           + ~@"0x1530477c7ab4113b59a4c18b076d11930f7da5d4a07f649bf54439d87d27e500fc8c25ebf8c92f6812cfc71c71c6d706"
             * i
         ; ~@"0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97be"
           * i
         ; ~@"0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71c"
           + ~@"0x8ab05f8bdd54cde190937e76bc3e447cc27c3d6fbd7063fcd104635a790520c0a395554e5c6aaaa9354ffffffffe38f"
             * i
         ; ~@"0x124c9ad43b6cf79bfbf7043de3811ad0761b0f37a1e26286b0e977c69aa274524e79097a56dc4bd9e1b371c71c718b10"
        |]
  let y_den =
    F_p2x.trim
      F_p2.
        [| ~@"0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa8fb"
           + ~@"0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa8fb"
             * i
         ; ~@"0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa9d3"
           * i
         ; ~@"0x12"
           + ~@"0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa99"
             * i
         ; ~@"1" |]
  let h_eff =
    Uint.(
      ~@"0xbc69f08f2ee75b3584c6a0ea91b352888e2a8e9145ad7689986ff031508ffe1329c2f178731db956d82bf015d1212b02ec0ec69d7477c1ae954cbc06689f6a359894c0adebbf6b4e8020005aaa95551" )
  let isogeny (pt : t) : G_2.t =
    let x, y = coords pt in
    let x_g2 = F_p2.(F_p2x.eval x_num x / F_p2x.eval x_den x) in
    let y_g2 = F_p2.(F_p2x.eval y_num x / F_p2x.eval y_den x * y) in

    let p = Option.get (C_2.of_coords x_g2 y_g2) in
    Option.get (G_2.in_subgroup C_2.(h_eff * p))
end
module F_p2_SWU =
  Curve.SWU_method
    (F_p2_SWU_curve)
    (struct
      open F_p2
      let z = zero - (~$2 + i)
      let sqrt = sqrt_opt

      (* As sgn0_m_eq_2 in RFC-9380 §4.1. *)
      let sgn0 (x : t) =
        let x_0, x_1 = (x.$(0), x.$(1)) in
        let sign_0 = Integer.(modulo (x_0 :> t) ~$2 = one) in
        let zero_0 = F_p.(x_0 = zero) in
        let sign_1 = Integer.(modulo (x_1 :> t) ~$2 = one) in
        sign_0 || (zero_0 && sign_1)
    end)

(* EIP-2537 §5.4: SWU map + 3-isogeny + cofactor clearing from Fₚ₂ to G₂. *)
let map_fp2_to_g2 (t : F_p2.t) : G_2.t =
  (* The SWU map gives us a point on the 3-isogenous auxiliary curve C_p2_SWU_curve. *)
  let swu_t = F_p2_SWU.map_to_curve_simple_swu t in
  F_p2_SWU_curve.isogeny swu_t
