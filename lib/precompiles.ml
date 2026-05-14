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
module Simple_precompile = struct
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
  Simple_precompile.(
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
  Simple_precompile.(
    run msg
      (let$ () = spend_gas Gas.(~$60 + (~$12 * bytes_to_whole_words ~$(Bytes.length msg.input_data))) in
       return (B32.to_bytes (Crypto.sha_256 msg.input_data)) ) )

let ripemd160_address = Address.of_hex_string "0x03"
let ripemd160 (msg : Evmc.Message.t) : Evmc.Result.t =
  Simple_precompile.(
    run msg
      (let$ () = spend_gas Gas.(~$600 + (~$120 * bytes_to_whole_words ~$(Bytes.length msg.input_data))) in
       return (B32.to_bytes (B20.to_bytes32 (Crypto.ripemd_160 msg.input_data))) ) )

let identity_address = Address.of_hex_string "0x04"
let identity (msg : Evmc.Message.t) : Evmc.Result.t =
  Simple_precompile.(
    run msg
      (let$ () = spend_gas Gas.(~$15 + (~$3 * bytes_to_whole_words ~$(Bytes.length msg.input_data))) in
       return msg.input_data ) )

module Modexp = struct
  (* TODO: Revert EIP-7883 and EIP-7823. *)
  (* Modexp gas cost calculation functions. EIP-7883, obsoleting EIP-2565. *)

  let calculate_multiplication_complexity ~base_length ~modulus_length =
    Uint.(
      let max_length = max base_length modulus_length in
      let words = ceil_div max_length ~$8 in
      if max_length > ~$32 then ~$2 * (words ** 2) else ~$16 )

  let calculate_iteration_count ~exponent_length ~exponent =
    Uint.(
      let k =
        match () with
        | () when exponent_length <= ~$32 && exponent = zero -> zero
        | () when exponent_length <= ~$32 -> ~$Stdlib.(significant_bits exponent - 1)
        | () ->
            (~$16 * (exponent_length - ~$32))
            + ~$Stdlib.(significant_bits (logand exponent Uint.((~$2 ** 256) - ~$1)) - 1)
      in
      max k ~$1 )

  let calculate_gas_cost ~base_length ~modulus_length ~exponent_length ~exponent =
    let multiplication_complexity = calculate_multiplication_complexity ~base_length ~modulus_length in
    let iteration_count = calculate_iteration_count ~exponent_length ~exponent in
    Uint.(max ~$500 (multiplication_complexity * iteration_count))

  let parameter_length =
    Simple_precompile.(
      let$ len = u256 in
      (* Input length bounds checking. EIP-7823. *)
      match U256.(to_int_opt len) with
      | Some i when i <= 1024 -> return i
      | _ -> precompile_failure )

  let address = Address.of_hex_string "0x05"

  (* EIP-198. *)
  let precompile (msg : Evmc.Message.t) : Evmc.Result.t =
    Simple_precompile.(
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
         let$ () = ensure Uint.(modulus <> zero) in
         let result = Uint.exp_mod base exponent ~modulo:modulus in
         let result_bytes = Uint.to_bytes_be result in
         (* As per EIP-198, the result must be a byte array of the same length as modulus_length, so
            it may be necessary to add padding. *)
         let padding_length = modulus_length - Bytes.length result_bytes in
         assert (padding_length >= 0) ;
         return (Bytes.make padding_length '\x00' ^ result_bytes) ) )
end

(* Read points in curves C_1 and C_2 for the alt_bn128 precompiles. *)
(* YP (257) *)
let f_p =
  Simple_precompile.(
    let open Ec.Alt_bn128 in
    let$ x = U256.to_uint <$> u256 in
    Option.or_fail (F_p.of_uint_opt x) )

let point_c1 =
  Simple_precompile.(
    let open Ec.Alt_bn128 in
    (* YP (260) *)
    let$ x = f_p in
    (* YP (261) *)
    let$ y = f_p in
    (* YP (258), YP (259) *)
    Option.or_fail C_1.(of_coords x y) )

let point_c2 =
  Simple_precompile.(
    let open Ec.Alt_bn128 in
    (* YP (264) *)
    let$ x_0 = f_p in
    (* YP (265) *)
    let$ x_1 = f_p in
    (* YP (266) *)
    let$ y_0 = f_p in
    (* YP (267) *)
    let$ y_1 = f_p in
    let g_x = F_p2.(const x_0 + (i * const x_1)) in
    let g_y = F_p2.(const y_0 + (i * const y_1)) in
    Option.or_fail C_2.(of_coords g_x g_y) )

let alt_bn128_add_address = Address.of_hex_string "0x06"
let alt_bn128_add (msg : Evmc.Message.t) : Evmc.Result.t =
  Simple_precompile.(
    run msg
      (let$ () = spend_gas Gas.(of_int 150) in

       let open Ec.Alt_bn128 in
       let$ p_0 = point_c1 in
       let$ p_1 = point_c1 in

       let s_x, s_y =
         match C_1.(p_0 + p_1) with
         | Infinity -> (U256.zero, U256.zero)
         | Point (x, y) -> (U256.of_integer_exn (x :> Integer.t), U256.of_integer_exn (y :> Integer.t))
       in
       return (B32.to_bytes (U256.to_repr s_x) ^ B32.to_bytes (U256.to_repr s_y)) ) )

let alt_bn128_mul_address = Address.of_hex_string "0x07"
let alt_bn128_mul (msg : Evmc.Message.t) : Evmc.Result.t =
  Simple_precompile.(
    run msg
      (let$ () = spend_gas Gas.(of_int 6_000) in

       let open Ec.Alt_bn128 in
       let$ p_0 = point_c1 in
       let$ n = U256.to_uint <$> u256 in

       let s_x, s_y =
         match C_1.(n * p_0) with
         | Infinity -> (U256.zero, U256.zero)
         | Point (x, y) -> (U256.of_integer_exn (x :> Integer.t), U256.of_integer_exn (y :> Integer.t))
       in
       return (B32.to_bytes U256.(to_repr s_x) ^ B32.to_bytes (U256.to_repr s_y)) ) )

let alt_bn128_pairing_check_address = Address.of_hex_string "0x08"
let alt_bn128_pairing_check (msg : Evmc.Message.t) : Evmc.Result.t =
  Simple_precompile.(
    run msg
      (let n = Bytes.length msg.input_data in
       let$ () = ensure (n mod 192 = 0) in
       let k = n / 192 in
       let$ () = spend_gas Gas.(of_int k) in

       let open Ec.Alt_bn128 in
       let$ pairs : (C_1.t * C_2.t) list = list k (pair point_c1 point_c2) in

       let result = pairing_check pairs in
       return (B32.to_bytes (U256.to_repr (if result then U256.one else U256.zero))) ) )

let blake2f_address = Address.of_hex_string "0x09"
let blake2f (msg : Evmc.Message.t) : Evmc.Result.t =
  Simple_precompile.(
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

module Point_evaluation = struct
  let versioned_hash_version_kzg = '\x01'
  let kzg_to_versioned_hash (kzg : B48.t) =
    let h = Crypto.keccak_256 (B48.to_bytes kzg) in
    B32.init (function 0 -> versioned_hash_version_kzg | i -> B32.(h.$(i)))

  let field_elements_per_blob = U256.(~$4_096)
  let bls_modulus = U256.(~@"52435875175126190479447740508185965837690552500527637822603658699938581184513")

  let precompile_result : Bytes.t =
    U256.to_repr_bytes field_elements_per_blob ^ U256.to_repr_bytes bls_modulus

  let verify_kzg_proof ~commitment ~z ~y ~proof = true

  let address = Address.of_hex_string "0x0a"
  let precompile (msg : Evmc.Message.t) : Evmc.Result.t =
    Simple_precompile.(
      run msg
        (let$ () = ensure (Bytes.length msg.input_data = 192) in

         let$ () = spend_gas Gas.(of_int 50_000) in

         let$ versioned_hash = b32 in
         let$ z = u256 in
         let$ y = u256 in

         let$ commitment = b48 in
         let$ proof = b48 in

         let$ () = ensure B32.(versioned_hash = kzg_to_versioned_hash commitment) in

         let$ () = ensure (verify_kzg_proof ~commitment ~z ~y ~proof) in

         return precompile_result ) )
end

let bls12_g1_add_address = Address.of_hex_string "0x0b"
let bls12_g1_add (_msg : Evmc.Message.t) : Evmc.Result.t = Evmc.Result.failure Precompile_failure

let bls12_g1_msm_address = Address.of_hex_string "0x0c"
let bls12_g1_msm (_msg : Evmc.Message.t) : Evmc.Result.t = Evmc.Result.failure Precompile_failure

let bls12_g2_add_address = Address.of_hex_string "0x0d"
let bls12_g2_add (_msg : Evmc.Message.t) : Evmc.Result.t = Evmc.Result.failure Precompile_failure

let bls12_g2_msm_address = Address.of_hex_string "0x0e"
let bls12_g2_msm (_msg : Evmc.Message.t) : Evmc.Result.t = Evmc.Result.failure Precompile_failure

let bls12_pairing_address = Address.of_hex_string "0x0f"
let bls12_pairing (_msg : Evmc.Message.t) : Evmc.Result.t = Evmc.Result.failure Precompile_failure

let bls12_map_fp_to_g1_address = Address.of_hex_string "0x10"
let bls12_map_fp_to_g1 (_msg : Evmc.Message.t) : Evmc.Result.t = Evmc.Result.failure Precompile_failure

let bls12_map_fp2_to_g2_address = Address.of_hex_string "0x11"
let bls12_map_fp2_to_g2 (_msg : Evmc.Message.t) : Evmc.Result.t = Evmc.Result.failure Precompile_failure

let precompiles : precompile Address.Map.t =
  Address.Map.of_list
    [ (ecrecover_address, ecrecover)
    ; (sha256_address, sha256)
    ; (ripemd160_address, ripemd160)
    ; (identity_address, identity)
    ; Modexp.(address, precompile)
    ; (alt_bn128_add_address, alt_bn128_add)
    ; (alt_bn128_mul_address, alt_bn128_mul)
    ; (alt_bn128_pairing_check_address, alt_bn128_pairing_check)
    ; (blake2f_address, blake2f)
    ; Point_evaluation.(address, precompile)
    ; (bls12_g1_add_address, bls12_g1_add)
    ; (bls12_g1_msm_address, bls12_g1_msm)
    ; (bls12_g2_add_address, bls12_g2_add)
    ; (bls12_g2_msm_address, bls12_g2_msm)
    ; (bls12_pairing_address, bls12_pairing)
    ; (bls12_map_fp_to_g1_address, bls12_map_fp_to_g1)
    ; (bls12_map_fp2_to_g2_address, bls12_map_fp2_to_g2) ]
