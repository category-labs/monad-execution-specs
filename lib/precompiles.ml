open Byte_string
open Numeric
open Chain.Ethereum

type precompile = Evmc.Message.t -> Evmc.Result.t

(* Note that Monad does not refund gas on transaction success. This also applies to precompiles. *)
let check_gas (msg : Evmc.Message.t) (gas : Gas.t) (exec : unit -> Bytes.t option) : Evmc.Result.t =
  if Gas.(of_uint64 msg.gas >= gas) then
    match exec () with
    | None -> Evmc.Result.(failure StatusCode.Precompile_failure)
    | Some output ->
        Evmc.Result.
          { status_code = StatusCode.Success
          ; gas_left = Gas.(to_uint64 (of_uint64 msg.gas - gas))
          ; gas_refund = 0L
          ; output_data = output
          ; create_address = Address.zero }
  else Evmc.Result.(failure StatusCode.Out_of_gas)

(* A state/result monad for executing ad-hoc precompiles. *)
module Precompile = struct
  module Base = Monad.StErr.Make (struct
    type state = Evmc.Message.t * int
    type error = Evmc.Result.StatusCode.t
  end)
  include Base

  let input_data =
    let$ msg, _ = get in
    return msg.input_data

  let advance n =
    let$ msg, i = get in
    let$ () = put (msg, i + n) in
    return i

  (** Helpers for reading. *)
  let byte : char t =
    let$ i = advance 1 in
    let$ bs = input_data in
    return bs.[i]

  module type BYTES = sig
    type t
    val byte_width : int
    val sub_with_zero_padding : Bytes.t -> int -> t
    val reverse : t -> t
    val to_bytes : t -> Bytes.t
  end

  let byte_reader (type bs) (module B : BYTES with type t = bs) : bs t =
    let$ i = advance B.byte_width in
    let$ bs = input_data in
    return (B.sub_with_zero_padding bs i)

  let b32 : B32.t t = byte_reader (module B32)
  let b48 : B48.t t = byte_reader (module B48)

  module type NUMERIC = sig
    module Repr : BYTES
    type t
    val of_repr : Repr.t -> t
  end

  let numeric_reader (type num) (module N : NUMERIC with type t = num) : num t =
    N.of_repr <$> byte_reader (module N.Repr)

  let numeric_reader_le (type num) (module N : NUMERIC with type t = num) : num t =
    let$ repr_be = byte_reader (module N.Repr) in
    let repr_le = N.Repr.reverse repr_be in
    return (N.of_repr repr_le)

  let u256 = numeric_reader (module U256)
  let u32 = numeric_reader (module U32)

  let u64_le = numeric_reader_le (module U64)

  let bytes (n : int) : Bytes.t t =
    let$ i = advance n in
    let$ bs = input_data in
    return (Bytes.sub_with_zero_padding bs i n)

  let pair (e1 : 'a t) (e2 : 'b t) : ('a * 'b) t =
    let$ e1 = e1 in
    let$ e2 = e2 in
    return (e1, e2)

  let list (n : int) (elt : 'a t) : 'a list t =
    let rec loop i =
      if i = 0 then return []
      else
        let$ hd = elt in
        let$ tl = loop (i - 1) in
        return (hd :: tl)
    in
    loop n

  (** Gas checks. *)
  let spend_gas (gas : Gas.t) : unit t =
    let$ msg, i = get in
    if Gas.(of_uint64 msg.gas < gas) then fail Evmc.Result.StatusCode.Out_of_gas
    else put ({msg with gas = Gas.(to_uint64 (of_uint64 msg.gas - gas))}, i)

  (** Generic precompile failure. *)
  let precompile_failure : 'a t = fail Evmc.Result.StatusCode.Precompile_failure

  let ensure (condition : bool) : unit t = if condition then return () else precompile_failure
  module Option = struct
    include Option
    let or_fail (opt : 'a option) = match opt with None -> precompile_failure | Some v -> Base.return v
  end
  module Result = struct
    include Stdlib.Result
    let or_fail (res : ('a, 'b) result) =
      match res with Error _ -> precompile_failure | Ok v -> Base.return v
  end

  (** Run a Bytes.t computation on an input message, returning an Evmc.Result.t *)
  let run (msg : Evmc.Message.t) (impl : Bytes.t t) : Evmc.Result.t =
    match impl (msg, 0) with
    | Ok (output, (msg', _)) ->
        Evmc.Result.
          { status_code = StatusCode.Success
          ; gas_left = msg'.gas
          ; gas_refund = 0L
          ; output_data = output
          ; create_address = Address.zero }
    | Error err ->
        assert (err <> Evmc.Result.StatusCode.Success) ;
        Evmc.Result.failure err
end

let ecrecover_address = Address.of_hex_string "0x01"
let ecrecover (msg : Evmc.Message.t) : Evmc.Result.t =
  Precompile.(
    run msg
      (let$ () = spend_gas Gas.(of_int 6_000) in
       let$ h = b32 in
       let$ v = u256 in
       let$ r = u256 in
       let$ s = u256 in

       Option.(
         (* As per YP (212), if any of these steps fails, ECRECOVER returns an empty byte string. *)
         let$ y_parity =
           if U256.(v = ~$27) then Some U8.zero else if U256.(v = ~$28) then Some U8.one else None
         in

         let$ () = ensure U256.(r > zero && r < Crypto.secp256k1n) in
         let$ () = ensure U256.(s > zero && s < Crypto.secp256k1n) in

         let$ addr = Crypto.ecrecover {r; s; y_parity} h in
         return (B32.to_bytes (Address.to_bytes32 addr)) )
       |> Option.value ~default:Bytes.empty
       |> return ) )

let sha256_address = Address.of_hex_string "0x02"
let sha256 (msg : Evmc.Message.t) : Evmc.Result.t =
  Precompile.(
    run msg
      (let$ () = spend_gas Gas.(~$60 + (~$12 * bytes_to_whole_words ~$(Bytes.length msg.input_data))) in
       return (B32.to_bytes (Crypto.sha_256 msg.input_data)) ) )

let ripemd160_address = Address.of_hex_string "0x03"
let ripemd160 (msg : Evmc.Message.t) : Evmc.Result.t =
  Precompile.(
    run msg
      (let$ () = spend_gas Gas.(~$600 + (~$120 * bytes_to_whole_words ~$(Bytes.length msg.input_data))) in
       return (B32.to_bytes (B20.to_bytes32 (Crypto.ripemd_160 msg.input_data))) ) )

let identity_address = Address.of_hex_string "0x04"
let identity (msg : Evmc.Message.t) : Evmc.Result.t =
  Precompile.(
    run msg
      (let$ () = spend_gas Gas.(~$15 + (~$3 * bytes_to_whole_words ~$(Bytes.length msg.input_data))) in
       return msg.input_data ) )

module Modexp = struct
  (* Modexp gas cost calculation functions. EIP-2565. *)
  let calculate_multiplication_complexity ~base_length ~modulus_length =
    Uint.(
      let max_length = max base_length modulus_length in
      let words = ceil_div max_length ~$8 in
      words ** 2 )

  let calculate_iteration_count ~exponent_length ~exponent =
    (* EIP-2565 and EIP-7883 use n.bit_length()-1. However, they implicitly take 0.bit_length() = 1. This is
       consistent with the behavior in EIP-198 and the Ethereum execution spec. *)
    let bit_length_minus_one n =
      Uint.of_int
        (let b = Uint.significant_bits n in
         if b = 0 then 0 else b - 1 )
    in
    let k =
      match () with
      | () when Uint.(exponent_length <= ~$32 && exponent = zero) -> Uint.zero
      | () when Uint.(exponent_length <= ~$32) -> bit_length_minus_one exponent
      | () ->
          (* EIP-2565 and EIP-7883 use a formula that would compute the least significant 256 bits. We follow
            the Ethereum execution spec, which instead uses the most significant 256 bits. *)
          let upper_256_bits = Uint.shift_right exponent ((8 * Uint.to_int exponent_length) - 256) in
          Uint.((~$8 * (exponent_length - ~$32)) + bit_length_minus_one upper_256_bits)
    in
    Uint.(max k one)

  let calculate_gas_cost ~base_length ~modulus_length ~exponent_length ~exponent =
    let multiplication_complexity = calculate_multiplication_complexity ~base_length ~modulus_length in
    let iteration_count = calculate_iteration_count ~exponent_length ~exponent in
    Uint.(max ~$200 (multiplication_complexity * iteration_count / ~$3))

  (* Input length bounds checking. Currently incorrect but required since all indices must be int. EIP-7823
     introduces stricter constraints, so this will become irrelevant in MONAD_NINE.
   *)
  let parameter_length =
    Precompile.(
      let$ len = u256 in
      match U256.(to_int_opt len) with
      | Some i when i <= Sys.max_string_length -> return i
      | _ -> precompile_failure )

  let address = Address.of_hex_string "0x05"

  (* EIP-198. *)
  let precompile (msg : Evmc.Message.t) : Evmc.Result.t =
    Precompile.(
      run msg
        (let$ base_length = parameter_length in
         let$ exponent_length = parameter_length in
         let$ modulus_length = parameter_length in
         let$ base = Uint.of_bytes_be <$> bytes base_length in
         let$ exponent = Uint.of_bytes_be <$> bytes exponent_length in
         let$ () =
           let gas_cost =
             let base_length = Uint.of_int base_length in
             let modulus_length = Uint.of_int modulus_length in
             let exponent_length = Uint.of_int exponent_length in
             calculate_gas_cost ~base_length ~modulus_length ~exponent_length ~exponent
           in
           spend_gas gas_cost
         in
         let$ modulus = Uint.of_bytes_be <$> bytes modulus_length in
         let result =
           if Uint.(modulus = zero) then Uint.zero else Uint.exp_mod base exponent ~modulo:modulus
         in
         let result_bytes = Uint.to_bytes_be result in
         (* As per EIP-198, the result must be a byte array of the same length as modulus_length, so
            it may be necessary to add padding. *)
         let padding_length = modulus_length - Bytes.length result_bytes in
         assert (padding_length >= 0) ;
         return (Bytes.make padding_length '\x00' ^ result_bytes) ) )
end

(* Encoding and decoding for G_1/G_2 points for EC precompiles. *)
module Ec_precompile_utils (M : sig
  module F_p : sig
    include Ec.Algebra.FIELD with type t = private Integer.t
    val of_uint_opt : Uint.t -> t option
  end
  module C1_coord_repr : Precompile.BYTES
  module C_1 : Ec.Curve.SIG with type Underlying.t = F_p.t
  module G_1 : sig
    include Ec.Curve.SIG with type Underlying.t = F_p.t and type t = private C_1.t
    val in_subgroup : C_1.t -> t option
  end

  module F_p2 : sig
    include Ec.Algebra.FIELD
    val i : t
    val const : F_p.t -> t
    val ( .$() ) : t -> int -> F_p.t
  end
  module C_2 : Ec.Curve.SIG with type Underlying.t = F_p2.t
  module G_2 : sig
    include Ec.Curve.SIG with type Underlying.t = F_p2.t and type t = private C_2.t
    val in_subgroup : C_2.t -> t option
  end
end) =
struct
  open M

  (* YP (257) *)
  let f_p =
    Precompile.(
      let$ x = Uint.of_bytes_be <$> (M.C1_coord_repr.to_bytes <$> byte_reader (module M.C1_coord_repr)) in
      Option.or_fail (F_p.of_uint_opt x) )

  let point_c1 =
    Precompile.(
      let$ () = return () in
      (* YP (260) *)
      let$ x = f_p in
      (* YP (261) *)
      let$ y = f_p in
      (* YP (259) *)
      Option.or_fail C_1.(of_coords x y) )

  (* YP (258) *)
  let point_g1 =
    Precompile.(
      let$ p = point_c1 in
      Option.or_fail G_1.(in_subgroup p) )

  let f_p2 =
    Precompile.(
      let$ x =
        let$ x = Uint.of_bytes_be <$> (M.C1_coord_repr.to_bytes <$> byte_reader (module M.C1_coord_repr)) in
        Option.or_fail (F_p.of_uint_opt x)
      in
      let$ y =
        let$ y = Uint.of_bytes_be <$> (M.C1_coord_repr.to_bytes <$> byte_reader (module M.C1_coord_repr)) in
        Option.or_fail (F_p.of_uint_opt y)
      in
      return F_p2.(const x + (i * const y)) )

  let point_c2 =
    Precompile.(
      (* YP (264), YP (265) *)
      let$ g_x = f_p2 in
      (* YP (266), YP (267) *)
      let$ g_y = f_p2 in
      (* YP (263) *)
      Option.or_fail (C_2.of_coords g_x g_y) )

  (* YP (262) *)
  let point_g2 =
    Precompile.(
      let$ p = point_c2 in
      Option.or_fail G_2.(in_subgroup p) )

  let c1_coord_to_repr (x : F_p.t) : Bytes.t =
    (x :> Integer.t)
    |> Integer.as_unsigned_exn
    |> Uint.to_bytes_be
    |> fun bs ->
    let padding_length = M.C1_coord_repr.byte_width - Bytes.length bs in
    assert (padding_length >= 0) ;
    Bytes.make padding_length '\x00' ^ bs

  (* Inverse of YP (258) *)
  let delta_1_inv (p : C_1.t) =
    let x, y = C_1.(coords p) in
    [x; y] |> List.map c1_coord_to_repr |> Bytes.(concat empty)

  (* Inverse of YP (262) *)
  let delta_2_inv (p : C_2.t) =
    let x, y = C_2.(coords p) in
    let x_re, x_im = F_p2.(x.$(0), x.$(1)) in
    let y_re, y_im = F_p2.(y.$(0), y.$(1)) in
    [x_re; x_im; y_re; y_im] |> List.map c1_coord_to_repr |> Bytes.(concat empty)
end

(* EIP-196 and EIP-197. *)
module Alt_bn128 = struct
  open Ec.Alt_bn128
  open Ec_precompile_utils (struct
    (* As per EIP-196, field elements and scalars are encoded as 32 byte big-endian numbers. *)
    module C1_coord_repr = B32
    include Ec.Alt_bn128
  end)

  let add_address = Address.of_hex_string "0x06"
  let add (msg : Evmc.Message.t) : Evmc.Result.t =
    Precompile.(
      run msg
        (let$ () = spend_gas Gas.(of_int 300) in

         let$ p_0 = point_c1 in
         let$ p_1 = point_c1 in

         return (delta_1_inv C_1.(p_0 + p_1)) ) )

  let mul_address = Address.of_hex_string "0x07"
  let mul (msg : Evmc.Message.t) : Evmc.Result.t =
    Precompile.(
      run msg
        (let$ () = spend_gas Gas.(of_int 30_000) in

         let$ p_0 = point_c1 in
         let$ n = U256.to_uint <$> u256 in

         return (delta_1_inv C_1.(n * p_0)) ) )

  let pairing_check_address = Address.of_hex_string "0x08"
  let pairing_check (msg : Evmc.Message.t) : Evmc.Result.t =
    Precompile.(
      run msg
        (let n = Bytes.length msg.input_data in
         let$ () = ensure (n mod 192 = 0) in
         let k = n / 192 in
         let$ () = spend_gas Gas.(of_int 225_000) in

         let$ pairs : (G_1.t * G_2.t) list = list k (pair point_g1 point_g2) in

         let result = pairing_check pairs in
         return (B32.to_bytes (U256.to_repr (if result then U256.one else U256.zero))) ) )
end

let blake2f_address = Address.of_hex_string "0x09"
let blake2f (msg : Evmc.Message.t) : Evmc.Result.t =
  Precompile.(
    run msg
      (let$ () = ensure (Bytes.length msg.input_data = 213) in
       let$ r = u32 in

       let$ () = spend_gas U32.(to_uint r) in

       (* r must fit in an int since we were able to afford the gas. *)
       let$ r = Option.or_fail (U32.to_int_opt r) in

       let$ h = Iarray.of_list <$> list 8 u64_le in
       let$ m = Iarray.of_list <$> list 16 u64_le in

       let$ t_low = u64_le in
       let$ t_high = u64_le in

       let$ f =
         byte >>= function '\x00' -> return false | '\x01' -> return true | _ -> precompile_failure
       in

       Iarray.to_list (Crypto.blake2f ~rounds:r ~h ~m ~t0:t_low ~t1:t_high ~final_block:f)
       |> List.map (fun i -> U64.to_repr i |> B8.reverse |> B8.to_bytes)
       |> Bytes.(concat empty)
       |> return ) )

(* EIP-4844 point evaluation precompile. *)
module Point_evaluation = struct
  (* All references to PolyCom refer to the Deneb Polynomial Commitments document, as cited in EIP-4844.
     https://github.com/ethereum/consensus-specs/blob/86fb82b221474cc89387fa6436806507b3849d88/specs/deneb/polynomial-commitments.md *)
  (* All references to IRTF refer to the BLS Signatures IRTF Version 4, as cited in PolyCom.
     https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-04 *)
  open Ec.Bls12_381

  let versioned_hash_version_kzg = '\x01'
  let kzg_to_versioned_hash (kzg : B48.t) =
    let h = Crypto.keccak_256 (B48.to_bytes kzg) in
    B32.init (function 0 -> versioned_hash_version_kzg | i -> B32.(h.$(i)))

  let field_elements_per_blob : Uint.t = Uint.(~$4_096)
  let bls_modulus : Integer.t = Uint.as_signed q

  let precompile_result : Bytes.t =
    U256.to_repr_bytes (U256.of_uint_exn field_elements_per_blob)
    ^ U256.to_repr_bytes (U256.of_integer_exn bls_modulus)

  (* Ad-hoc conversion because point evaluation uses different conventions than the other two EC precompile
     families. *)
  let read_fp ostr i = F_p.of_uint_opt (Uint.of_bytes_be (Bytes.sub ostr (i * 24) 24))

  (* Flags for a compressed G1 or G2 point. *)
  type flags = {compressed : bool; infinity : bool; negative : bool}
  let read_flags (c : char) : flags =
    let b = Char.code c in
    {compressed = b land 0x80 <> 0; infinity = b land 0x40 <> 0; negative = b land 0x20 <> 0}

  (* This covers pubkey_to_point and KeyValidate from IRTF, and bytes_to_kzg_commitment, bytes_to_kzg_proof from
     PolyCom. *)
  let decompress_G1 (bs : B48.t) : G_1.t option =
    let {compressed; infinity; negative} = read_flags B48.(bs.$(0)) in
    if not compressed then None
    else if infinity then Some G_1.zero
    else
      Option.(
        let x : F_p.t = F_p.reduce Integer.(modulo (of_bytes_be (B48.to_bytes bs)) (~$2 ** 381)) in
        (* Solve y^2 = x^3 + 4 for y. *)
        let$ y : F_p.t =
          let$ y_abs = F_p.(sqrt_opt ((x * x * x) + ~@"4")) in
          let y_is_large = Integer.((y_abs :> Integer.t) * ~$2 >= Uint.as_signed p) in
          return (if y_is_large <> negative then F_p.(zero - y_abs) else y_abs)
        in
        G_1.of_coords x y )

  (* Decompress a 96-byte compressed G2 point.
     Format: bytes[0..48] = x.c1 with 3 flag bits in MSB, bytes[48..96] = x.c0. *)
  let decompress_G2 (bs : Bytes.t) : G_2.t option =
    let {compressed; infinity; negative} = read_flags (Bytes.get bs 0) in
    if not compressed then None
    else if infinity then Some G_2.zero
    else
      Option.(
        let x_c1 : F_p.t = F_p.reduce Integer.(modulo (of_bytes_be (Bytes.sub bs 0 48)) (~$2 ** 381)) in
        let x_c0 : F_p.t = F_p.reduce (Integer.of_bytes_be (Bytes.sub bs 48 48)) in
        let x : F_p2.t = F_p2.(const x_c0 + (i * const x_c1)) in
        (* Solve y^2 = x^3 + (4 + 4i) for y. *)
        let$ y : F_p2.t =
          let$ y_abs = F_p2.(sqrt_opt ((x * x * x) + (~@"4" + (i * ~@"4")))) in
          let y_im = F_p2.(y_abs.$(1)) in
          let y_re = F_p2.(y_abs.$(0)) in
          let dominant = if F_p.(y_im <> zero) then y_im else y_re in
          let sign_y = Integer.((dominant :> Integer.t) * ~$2 >= Uint.as_signed p) in
          return (if sign_y <> negative then F_p2.(zero - y_abs) else y_abs)
        in
        G_2.of_coords x y )

  (* As PolyCom. Note that this returns an Integer.t *)
  let bytes_to_bls_field (bs : B32.t) : Integer.t option =
    (F_p.of_uint_opt U256.(to_uint (of_repr bs)) :> Integer.t option)

  let bytes_to_kzg_commitment (commitment : B48.t) = decompress_G1 commitment
  let bytes_to_kzg_proof (proof : B48.t) = decompress_G1 proof

  let kzg_setup_G2_monomial_1 : G_2.t =
    Bytes.of_hex_string
      "0xb5bfd7dd8cdeb128843bc287230af38926187075cbfbefa81009a2ce615ac53d2914e5870cb452d2afaaab24f3499f72185cbfee53492714734429b7b38608e23926c911cceceac9a36851477ba4c60b087041de621000edc98edada20c1def2"
    |> decompress_G2
    |> Option.get

  let verify_kzg_proof ~commitment ~z ~y ~proof =
    Option.(
      let$ commitment = bytes_to_kzg_commitment commitment in
      (* TODO: double-check z, y validation. *)
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
  let precompile (msg : Evmc.Message.t) : Evmc.Result.t =
    Precompile.(
      run msg
        (let$ () = ensure (Bytes.length msg.input_data = 192) in

         let$ () = spend_gas Gas.(of_int 200_000) in

         let$ versioned_hash = b32 in
         let$ z = b32 in
         let$ y = b32 in

         let$ commitment = b48 in
         let$ proof = b48 in

         let$ () = ensure B32.(versioned_hash = kzg_to_versioned_hash commitment) in

         let$ () = Option.or_fail (verify_kzg_proof ~commitment ~z ~y ~proof) in

         return precompile_result ) )
end

(* EIP-2537. *)
module Bls12 = struct
  open Ec.Bls12_381
  open Ec_precompile_utils (struct
    include Ec.Bls12_381
    module C1_coord_repr = B64
  end)

  (* Constants for gas cost calculation. *)
  let g1_add_cost = Gas.of_int 375
  let g1_mul_cost = Gas.of_int 12_000
  let g2_add_cost = Gas.of_int 600
  let g2_mul_cost = Gas.of_int 22_500
  let multiplier = Gas.of_int 1_000

  module IntMap = Map.Make (Int)

  let g1_discount =
    let open Gas in
    let max_discount = ~$519 in
    let discount_table =
      IntMap.of_list
        [ (1, ~$1000)
        ; (2, ~$949)
        ; (3, ~$848)
        ; (4, ~$797)
        ; (5, ~$764)
        ; (6, ~$750)
        ; (7, ~$738)
        ; (8, ~$728)
        ; (9, ~$719)
        ; (10, ~$712)
        ; (11, ~$705)
        ; (12, ~$698)
        ; (13, ~$692)
        ; (14, ~$687)
        ; (15, ~$682)
        ; (16, ~$677)
        ; (17, ~$673)
        ; (18, ~$669)
        ; (19, ~$665)
        ; (20, ~$661)
        ; (21, ~$658)
        ; (22, ~$654)
        ; (23, ~$651)
        ; (24, ~$648)
        ; (25, ~$645)
        ; (26, ~$642)
        ; (27, ~$640)
        ; (28, ~$637)
        ; (29, ~$635)
        ; (30, ~$632)
        ; (31, ~$630)
        ; (32, ~$627)
        ; (33, ~$625)
        ; (34, ~$623)
        ; (35, ~$621)
        ; (36, ~$619)
        ; (37, ~$617)
        ; (38, ~$615)
        ; (39, ~$613)
        ; (40, ~$611)
        ; (41, ~$609)
        ; (42, ~$608)
        ; (43, ~$606)
        ; (44, ~$604)
        ; (45, ~$603)
        ; (46, ~$601)
        ; (47, ~$599)
        ; (48, ~$598)
        ; (49, ~$596)
        ; (50, ~$595)
        ; (51, ~$593)
        ; (52, ~$592)
        ; (53, ~$591)
        ; (54, ~$589)
        ; (55, ~$588)
        ; (56, ~$586)
        ; (57, ~$585)
        ; (58, ~$584)
        ; (59, ~$582)
        ; (60, ~$581)
        ; (61, ~$580)
        ; (62, ~$579)
        ; (63, ~$577)
        ; (64, ~$576)
        ; (65, ~$575)
        ; (66, ~$574)
        ; (67, ~$573)
        ; (68, ~$572)
        ; (69, ~$570)
        ; (70, ~$569)
        ; (71, ~$568)
        ; (72, ~$567)
        ; (73, ~$566)
        ; (74, ~$565)
        ; (75, ~$564)
        ; (76, ~$563)
        ; (77, ~$562)
        ; (78, ~$561)
        ; (79, ~$560)
        ; (80, ~$559)
        ; (81, ~$558)
        ; (82, ~$557)
        ; (83, ~$556)
        ; (84, ~$555)
        ; (85, ~$554)
        ; (86, ~$553)
        ; (87, ~$552)
        ; (88, ~$551)
        ; (89, ~$550)
        ; (90, ~$549)
        ; (91, ~$548)
        ; (92, ~$547)
        ; (93, ~$547)
        ; (94, ~$546)
        ; (95, ~$545)
        ; (96, ~$544)
        ; (97, ~$543)
        ; (98, ~$542)
        ; (99, ~$541)
        ; (100, ~$540)
        ; (101, ~$540)
        ; (102, ~$539)
        ; (103, ~$538)
        ; (104, ~$537)
        ; (105, ~$536)
        ; (106, ~$536)
        ; (107, ~$535)
        ; (108, ~$534)
        ; (109, ~$533)
        ; (110, ~$532)
        ; (111, ~$532)
        ; (112, ~$531)
        ; (113, ~$530)
        ; (114, ~$529)
        ; (115, ~$528)
        ; (116, ~$528)
        ; (117, ~$527)
        ; (118, ~$526)
        ; (119, ~$525)
        ; (120, ~$525)
        ; (121, ~$524)
        ; (122, ~$523)
        ; (123, ~$522)
        ; (124, ~$522)
        ; (125, ~$521)
        ; (126, ~$520)
        ; (127, ~$520)
        ; (128, ~$519) ]
    in
    fun k -> IntMap.find_opt k discount_table |> Option.value ~default:max_discount

  let g2_discount =
    let open Gas in
    let max_discount = ~$524 in
    let discount_table =
      IntMap.of_list
        [ (1, ~$1000)
        ; (2, ~$1000)
        ; (3, ~$923)
        ; (4, ~$884)
        ; (5, ~$855)
        ; (6, ~$832)
        ; (7, ~$812)
        ; (8, ~$796)
        ; (9, ~$782)
        ; (10, ~$770)
        ; (11, ~$759)
        ; (12, ~$749)
        ; (13, ~$740)
        ; (14, ~$732)
        ; (15, ~$724)
        ; (16, ~$717)
        ; (17, ~$711)
        ; (18, ~$704)
        ; (19, ~$699)
        ; (20, ~$693)
        ; (21, ~$688)
        ; (22, ~$683)
        ; (23, ~$679)
        ; (24, ~$674)
        ; (25, ~$670)
        ; (26, ~$666)
        ; (27, ~$663)
        ; (28, ~$659)
        ; (29, ~$655)
        ; (30, ~$652)
        ; (31, ~$649)
        ; (32, ~$646)
        ; (33, ~$643)
        ; (34, ~$640)
        ; (35, ~$637)
        ; (36, ~$634)
        ; (37, ~$632)
        ; (38, ~$629)
        ; (39, ~$627)
        ; (40, ~$624)
        ; (41, ~$622)
        ; (42, ~$620)
        ; (43, ~$618)
        ; (44, ~$615)
        ; (45, ~$613)
        ; (46, ~$611)
        ; (47, ~$609)
        ; (48, ~$607)
        ; (49, ~$606)
        ; (50, ~$604)
        ; (51, ~$602)
        ; (52, ~$600)
        ; (53, ~$598)
        ; (54, ~$597)
        ; (55, ~$595)
        ; (56, ~$593)
        ; (57, ~$592)
        ; (58, ~$590)
        ; (59, ~$589)
        ; (60, ~$587)
        ; (61, ~$586)
        ; (62, ~$584)
        ; (63, ~$583)
        ; (64, ~$582)
        ; (65, ~$580)
        ; (66, ~$579)
        ; (67, ~$578)
        ; (68, ~$576)
        ; (69, ~$575)
        ; (70, ~$574)
        ; (71, ~$573)
        ; (72, ~$571)
        ; (73, ~$570)
        ; (74, ~$569)
        ; (75, ~$568)
        ; (76, ~$567)
        ; (77, ~$566)
        ; (78, ~$565)
        ; (79, ~$563)
        ; (80, ~$562)
        ; (81, ~$561)
        ; (82, ~$560)
        ; (83, ~$559)
        ; (84, ~$558)
        ; (85, ~$557)
        ; (86, ~$556)
        ; (87, ~$555)
        ; (88, ~$554)
        ; (89, ~$553)
        ; (90, ~$552)
        ; (91, ~$552)
        ; (92, ~$551)
        ; (93, ~$550)
        ; (94, ~$549)
        ; (95, ~$548)
        ; (96, ~$547)
        ; (97, ~$546)
        ; (98, ~$545)
        ; (99, ~$545)
        ; (100, ~$544)
        ; (101, ~$543)
        ; (102, ~$542)
        ; (103, ~$541)
        ; (104, ~$541)
        ; (105, ~$540)
        ; (106, ~$539)
        ; (107, ~$538)
        ; (108, ~$537)
        ; (109, ~$537)
        ; (110, ~$536)
        ; (111, ~$535)
        ; (112, ~$535)
        ; (113, ~$534)
        ; (114, ~$533)
        ; (115, ~$532)
        ; (116, ~$532)
        ; (117, ~$531)
        ; (118, ~$530)
        ; (119, ~$530)
        ; (120, ~$529)
        ; (121, ~$528)
        ; (122, ~$528)
        ; (123, ~$527)
        ; (124, ~$526)
        ; (125, ~$526)
        ; (126, ~$525)
        ; (127, ~$524)
        ; (128, ~$524) ]
    in
    fun k -> IntMap.find_opt k discount_table |> Option.value ~default:max_discount

  let g1_add_address = Address.of_hex_string "0x0b"
  let g1_add (msg : Evmc.Message.t) : Evmc.Result.t =
    Precompile.(
      run msg
        (let$ () = ensure (Bytes.length msg.input_data = 256) in

         let$ () = spend_gas g1_add_cost in

         (* g1_add does not check that its inputs are in G1. *)
         let$ p_0 = point_c1 in
         let$ p_1 = point_c1 in

         return (delta_1_inv C_1.(p_0 + p_1)) ) )

  let g1_msm_address = Address.of_hex_string "0x0c"
  let g1_msm (msg : Evmc.Message.t) : Evmc.Result.t =
    Precompile.(
      run msg
        (let$ () = ensure (Bytes.length msg.input_data mod 160 = 0) in
         let k = Bytes.length msg.input_data / 160 in
         let$ () = ensure (k > 0) in

         let$ () = spend_gas Gas.(~$k * g1_mul_cost * g1_discount k / multiplier) in

         let$ points = list k (pair point_g1 u256) in

         (* TODO: this can be done faster with Pippenger's algorithm. *)
         let sum = List.fold_left (fun acc (pt, s) -> G_1.(acc + (U256.to_uint s * pt))) G_1.zero points in
         return (delta_1_inv (sum :> C_1.t)) ) )

  let g2_add_address = Address.of_hex_string "0x0d"
  let g2_add (msg : Evmc.Message.t) : Evmc.Result.t =
    Precompile.(
      run msg
        (let$ () = ensure (Bytes.length msg.input_data = 512) in

         let$ () = spend_gas g2_add_cost in

         (* g2_add does not check that its inputs are in G2. *)
         let$ p_0 = point_c2 in
         let$ p_1 = point_c2 in

         return (delta_2_inv C_2.(p_0 + p_1)) ) )

  let g2_msm_address = Address.of_hex_string "0x0e"
  let g2_msm (msg : Evmc.Message.t) : Evmc.Result.t =
    Precompile.(
      run msg
        (let$ () = ensure (Bytes.length msg.input_data mod 288 = 0) in
         let k = Bytes.length msg.input_data / 288 in
         let$ () = ensure (k > 0) in

         let$ () = spend_gas Gas.(~$k * g2_mul_cost * g2_discount k / multiplier) in

         let$ points = list k (pair point_g2 u256) in

         (* TODO: this can be done faster with Pippenger's algorithm. *)
         let sum = List.fold_left (fun acc (pt, s) -> G_2.(acc + (U256.to_uint s * pt))) G_2.zero points in
         return (delta_2_inv (sum :> C_2.t)) ) )

  let pairing_check_address = Address.of_hex_string "0x0f"
  let pairing_check (msg : Evmc.Message.t) : Evmc.Result.t =
    Precompile.(
      run msg
        (let$ () = ensure (Bytes.length msg.input_data mod 384 = 0) in
         let k = Bytes.length msg.input_data / 384 in
         let$ () = ensure (k > 0) in

         let$ () = spend_gas Gas.((~$k * ~$32_600) + ~$37_700) in

         let$ points = list k (pair point_g1 point_g2) in

         return
           (if Ec.Bls12_381.pairing_check points then U256.(to_repr_bytes one) else U256.(to_repr_bytes zero))
        ) )

  let map_fp_to_g1_address = Address.of_hex_string "0x10"
  let map_fp_to_g1 (msg : Evmc.Message.t) : Evmc.Result.t =
    Precompile.(
      run msg
        (let$ () = ensure (Bytes.length msg.input_data = 64) in

         let$ () = spend_gas Gas.(of_int 5_500) in

         let$ fp_elem = f_p in
         return (delta_1_inv (Ec.Bls12_381.map_fp_to_g1 fp_elem :> C_1.t)) ) )

  let map_fp2_to_g2_address = Address.of_hex_string "0x11"
  let map_fp2_to_g2 (msg : Evmc.Message.t) : Evmc.Result.t =
    Precompile.(
      run msg
        (let$ () = ensure (Bytes.length msg.input_data = 128) in

         let$ () = spend_gas Gas.(of_int 23_800) in

         let$ fp2_elem = f_p2 in
         return (delta_2_inv (Ec.Bls12_381.map_fp2_to_g2 fp2_elem :> C_2.t)) ) )
end

(* EIP-7951 *)
module Secp256r1 = struct
  open Ec.Secp256r1

  let f_p =
    Precompile.(
      let$ x = U256.to_uint <$> u256 in
      Option.or_fail (F_p.of_uint_opt x) )

  let f_q_nz =
    Precompile.(
      let$ x = U256.to_uint <$> u256 in
      let$ () = ensure Uint.(x <> zero) in
      Option.or_fail (F_q.of_uint_opt x) )

  let point_g1 =
    Precompile.(
      (* YP (260) *)
      let$ x = f_p in
      (* YP (261) *)
      let$ y = f_p in
      (* YP (258), YP (259) *)
      Option.or_fail G_1.(of_coords x y) )

  let address = Address.of_hex_string "0x0100"
  let verify (msg : Evmc.Message.t) : Evmc.Result.t =
    Precompile.(
      run msg
        (let$ () = spend_gas Gas.(of_int 6_900) in

         let$ h = U256.to_integer <$> u256 in

         let$ r = U256.to_uint <$> u256 in
         let$ s = U256.to_uint <$> u256 in

         let$ q_x = U256.to_uint <$> u256 in
         let$ q_y = U256.to_uint <$> u256 in

         Option.(
           (* If input length validation fails here, the contract does not revert but instead returns the empty
              byte string, as per EIP-7951. *)
           let$ () = ensure (Bytes.length msg.input_data = 160) in
           let$ r = F_q.of_uint_opt r in
           let$ s = F_q.of_uint_opt s in
           (* TODO: double-check? *)
           let$ () = ensure (F_q.(r <> zero) && F_q.(s <> zero)) in

           let$ q =
             let$ q_x = F_p.of_uint_opt q_x in
             let$ q_y = F_p.of_uint_opt q_y in
             G_1.of_coords q_x q_y
           in
           let$ () = ensure G_1.(q <> zero) in

           let s_inv = (F_q.(one / s) :> Integer.t) in
           let u_1 = Integer.as_unsigned_exn (F_q.(reduce Integer.(h * s_inv)) :> Integer.t) in
           let u_2 = Integer.as_unsigned_exn (F_q.(reduce Integer.((r :> Integer.t) * s_inv)) :> Integer.t) in
           let r' = G_1.((u_1 * generator) + (u_2 * q)) in
           let$ () = ensure (not G_1.(r' = zero)) in
           let x, _ = G_1.coords r' in
           let$ () = ensure F_q.(reduce (x :> Integer.t) = r) in
           return U256.(to_repr_bytes one) )
         |> Option.value ~default:Bytes.empty
         |> return ) )
end

let precompiles : precompile Address.Map.t =
  Address.Map.of_list
    [ (ecrecover_address, ecrecover)
    ; (sha256_address, sha256)
    ; (ripemd160_address, ripemd160)
    ; (identity_address, identity)
    ; Modexp.(address, precompile)
    ; Alt_bn128.(add_address, add)
    ; Alt_bn128.(mul_address, mul)
    ; Alt_bn128.(pairing_check_address, pairing_check)
    ; (blake2f_address, blake2f)
    ; Point_evaluation.(address, precompile)
    ; Bls12.(g1_add_address, g1_add)
    ; Bls12.(g1_msm_address, g1_msm)
    ; Bls12.(g2_add_address, g2_add)
    ; Bls12.(g2_msm_address, g2_msm)
    ; Bls12.(pairing_check_address, pairing_check)
    ; Bls12.(map_fp_to_g1_address, map_fp_to_g1)
    ; Bls12.(map_fp2_to_g2_address, map_fp2_to_g2)
    ; Secp256r1.(address, verify) ]
