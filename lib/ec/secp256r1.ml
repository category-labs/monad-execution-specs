open Numeric
open Algebra

(* secp256r1 field modulus. *)
let p = Uint.of_string "0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff"

(* secp256r1 curve order. *)
let q = Uint.of_string "0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551"
let curve_order = q

module F_p = Prime_field (struct
  let modulus = Uint.as_signed p
end)

module F_q = Prime_field (struct
  let modulus = Uint.as_signed q
end)

module C_1 =
  Curve.Make
    (F_p)
    (struct
      let a = F_p.(~@"0xffffffff00000001000000000000000000000000fffffffffffffffffffffffc")
      let b = F_p.(~@"0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b")
    end)
module G_1 = C_1.Subgroup (struct
  let order = curve_order
  let generator =
    Option.get
      (C_1.of_coords
         F_p.(~@"0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296")
         F_p.(~@"0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5") )
end)
