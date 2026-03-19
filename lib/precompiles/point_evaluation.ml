(** EIP-4844 point evaluation precompile. *)

open Byte_string
open Numeric
open Chain.Ethereum

open Utils
open Ec.Bls12_381

(* All references to PolyCom refer to the Deneb Polynomial Commitments document, as cited in EIP-4844.
   https://github.com/ethereum/consensus-specs/blob/86fb82b221474cc89387fa6436806507b3849d88/specs/deneb/polynomial-commitments.md *)
(* All references to IRTF refer to the BLS Signatures IRTF Version 4, as cited in PolyCom.
   https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-04 *)
(* All references to ZCash refer to the source quoted in IRTF.
   https://github.com/zkcrypto/pairing/blob/0.13.0/src/bls12_381/README.md *)

let versioned_hash_version_kzg = '\x01'
let kzg_commitment_to_versioned_hash (kzg : B48.t) =
  let h = Crypto.sha_256 (B48.to_bytes kzg) in
  B32.init (function 0 -> versioned_hash_version_kzg | i -> B32.(h.$(i)))

let field_elements_per_blob : Uint.t = Uint.(~$4_096)
let bls_modulus : Integer.t = Uint.as_signed q

(* The point evaluation precompile always returns this output in case of success. *)
let precompile_result : Bytes.t =
  U256.to_repr_bytes (U256.of_uint_exn field_elements_per_blob)
  ^ U256.to_repr_bytes (U256.of_integer_exn bls_modulus)

(* Flags for a compressed G1 or G2 point. *)
type flags = {compressed : bool; infinity : bool; negative : bool}
let flag_compressed = 0x80
let flag_infinity = 0x40
let flag_negative = 0x20

let read_flags (c : char) : flags =
  let b = Char.code c in
  { compressed = b land flag_compressed <> 0
  ; infinity = b land flag_infinity <> 0
  ; negative = b land flag_negative <> 0 }

(* Decompression for G1 and G2 points.
   These functions incorporate pubkey_to_point and KeyValidate from IRTF, and bytes_to_kzg_commitment,
   bytes_to_kzg_proof from PolyCom.
   As per IRTF, the point serialization scheme is defined by ZCash.
   In particular, note that the encoding of a G2 point c0 + c1 i starts with the encoding of c1, followed by
   the encoding of c0, going against the conventions in other precompiles.
   *)
let infinity_G1 =
  (* The canonical compressed representation for the infinity point in G1. *)
  B48.init (function
    | 0 -> Char.chr (flag_compressed lor flag_infinity)
    | _ -> '\x00' )
let decompress_G1 (bs : B48.t) : G_1.t option =
  let {compressed; infinity; negative} = read_flags B48.(bs.$(0)) in
  Option.(
    if not compressed then None
    else if infinity then
      (* The only canonical representation of infinity. *)
      let$ () = ensure B48.(bs = infinity_G1) in
      return G_1.zero
    else
      (* IRTF states that octets_to_point returns INVALID if the octet stream does not correspond exactly
         to a canonical representation. Therefore we reject inputs that are not reduced modulo p. *)
      let$ x : F_p.t = F_p.of_uint_opt Uint.(modulo (of_bytes_be (B48.to_bytes bs)) (~$2 ** 381)) in
      (* Solve y^2 = x^3 + 4 for y. *)
      let$ y : F_p.t =
        let$ y_abs = F_p.(sqrt_opt ((x * x * x) + ~$4)) in
        let y_is_large = Integer.((y_abs :> Integer.t) * ~$2 >= Uint.as_signed p) in
        return (if y_is_large <> negative then F_p.(zero - y_abs) else y_abs)
      in
      G_1.of_coords x y )

let infinity_G2 =
  (* The canonical compressed representation for the infinity point in G2. *)
  B96.init (function
    | 0 -> Char.chr (flag_compressed lor flag_infinity)
    | _ -> '\x00' )
let decompress_G2 (bs : B96.t) : G_2.t option =
  let {compressed; infinity; negative} = read_flags B96.(bs.$(0)) in
  Option.(
    if not compressed then None
    else if infinity then
      let$ () = ensure B96.(bs = infinity_G2) in
      return G_2.zero
    else
      let bs = B96.to_bytes bs in
      (* IRTF states that octets_to_point returns INVALID if the octet stream does not correspond exactly
         to a canonical representation. Therefore we reject inputs that are not reduced modulo p. *)
      let$ x_c1 : F_p.t = F_p.of_uint_opt Uint.(modulo (of_bytes_be (Bytes.sub bs 0 48)) (~$2 ** 381)) in
      let$ x_c0 : F_p.t = F_p.of_uint_opt Uint.(of_bytes_be (Bytes.sub bs 48 48)) in
      let x : F_p2.t = F_p2.{re = x_c0; im = x_c1} in
      (* Solve y^2 = x^3 + (4 + 4i) for y. *)
      let$ y : F_p2.t =
        let$ y_abs = F_p2.(sqrt_opt ((x * x * x) + (~$4 + (i * ~$4)))) in
        let F_p2.{im = y_im; re = y_re} = y_abs in
        let dominant = if F_p.(y_im <> zero) then y_im else y_re in
        let sign_y = Integer.((dominant :> Integer.t) * ~$2 >= Uint.as_signed p) in
        return (if sign_y <> negative then F_p2.(zero - y_abs) else y_abs)
      in
      G_2.of_coords x y )

(* As PolyCom. Note that the result lives in F_q but it is returned as an Integer.t *)
let bytes_to_bls_field (bs : B32.t) : Integer.t option =
  let x = U256.(to_integer (of_repr bs)) in
  if Integer.(x >= zero && x < Uint.as_signed Ec.Bls12_381.curve_order) then Some x else None

let bytes_to_kzg_commitment (commitment : B48.t) = decompress_G1 commitment
let bytes_to_kzg_proof (proof : B48.t) = decompress_G1 proof

let kzg_setup_G2_monomial_1 : G_2.t =
  B96.of_hex_string
    "0xb5bfd7dd8cdeb128843bc287230af38926187075cbfbefa81009a2ce615ac53d2914e5870cb452d2afaaab24f3499f72185cbfee53492714734429b7b38608e23926c911cceceac9a36851477ba4c60b087041de621000edc98edada20c1def2"
  |> decompress_G2
  |> Option.get

let verify_kzg_proof ~commitment ~z ~y ~proof =
  Option.(
    let$ commitment = bytes_to_kzg_commitment commitment in
    let$ z = bytes_to_bls_field z in
    let$ y = bytes_to_bls_field y in
    let$ proof = bytes_to_kzg_proof proof in
    let x_minus_z =
      G_2.(
        kzg_setup_G2_monomial_1
        + (Integer.(as_unsigned_exn (modulo (bls_modulus - z) bls_modulus)) * G_2.generator) )
    in
    let p_minus_y =
      G_1.(commitment + (Integer.(as_unsigned_exn (modulo (bls_modulus - y) bls_modulus)) * G_1.generator))
    in
    ensure (pairing_check [(p_minus_y, G_2.(neg generator)); (proof, x_minus_z)]) )

let address = Address.of_hex_string "0x0a"
let precompile (msg : Evmc.Message.t) : precompile_result =
  Precompile.(
    run msg
      (let$ () = ensure (Bytes.length msg.input_data = 192) in

       (* Monad §4.2. *)
       let$ () = spend_gas Gas.(of_int 200_000) in

       let$ versioned_hash = b32 in
       let$ z = b32 in
       let$ y = b32 in

       let$ commitment = b48 in
       let$ proof = b48 in

       let$ () = ensure B32.(versioned_hash = kzg_commitment_to_versioned_hash commitment) in

       let$ () = Option.or_fail (verify_kzg_proof ~commitment ~z ~y ~proof) in

       return precompile_result ) )
