(** Modexp precompile as introduced by EIP-198, updated according to EIP-2565 and EIP-7883. *)

module Make (Revision : sig
  val revision : Chain.Monad.Revision.active
end) =
struct
  open Revision

  open Byte_string
  open Numeric
  open Chain.Ethereum
  open Utils

  (* Modexp gas cost calculation functions. YP (237), adjusted for EIP-2565. *)
  let calculate_multiplication_complexity =
    match revision with
    | `Eight ->
        (* EIP-2565. *)
        fun ~base_length ~modulus_length ->
          Uint.(
            let max_length = max base_length modulus_length in
            let words = ceil_div max_length ~$8 in
            words ** 2 )
    | `Nine ->
        (* EIP-7883. *)
        fun ~base_length ~modulus_length ->
          Uint.(
            let max_length = max base_length modulus_length in
            let words = ceil_div max_length ~$8 in
            if max_length > ~$32 then ~$2 * (words ** 2) else ~$16 )

  let calculate_iteration_count =
    (* EIP-2565 and EIP-7883 use n.bit_length()-1. However, they implicitly take 0.bit_length() = 1. This is
       consistent with the behavior in EIP-198 and the Ethereum execution spec. *)
    let bit_length_minus_one n =
      Uint.of_int
        (let b = Uint.significant_bits n in
         if b = 0 then 0 else b - 1 )
    in
    match revision with
    | `Eight ->
        (* EIP-2565. *)
        fun ~exponent_length ~exponent_upper_256_bits ->
          let k =
            (* YP (238), adjusted for EIP-2565 *)
            match () with
            | () when Uint.(exponent_length <= ~$32 && exponent_upper_256_bits = zero) -> Uint.zero
            | () when Uint.(exponent_length <= ~$32) -> bit_length_minus_one exponent_upper_256_bits
            | () -> Uint.((~$8 * (exponent_length - ~$32)) + bit_length_minus_one exponent_upper_256_bits)
          in
          Uint.(max k one)
    | `Nine ->
        (* EIP-7883. *)
        fun ~exponent_length ~exponent_upper_256_bits ->
          let k =
            (* YP (238), adjusted for EIP-7883 *)
            match () with
            | () when Uint.(exponent_length <= ~$32 && exponent_upper_256_bits = zero) -> Uint.zero
            | () when Uint.(exponent_length <= ~$32) -> bit_length_minus_one exponent_upper_256_bits
            | () -> Uint.((~$16 * (exponent_length - ~$32)) + bit_length_minus_one exponent_upper_256_bits)
          in
          Uint.(max k one)

  (* YP (236) *)
  let gas_quad_divisor = Gas.(~$3)

  let calculate_gas_cost =
    match revision with
    | `Eight ->
        (* EIP-2565. *)
        fun ~base_length ~modulus_length ~exponent_length ~exponent_upper_256_bits ->
          let multiplication_complexity = calculate_multiplication_complexity ~base_length ~modulus_length in
          let iteration_count = calculate_iteration_count ~exponent_length ~exponent_upper_256_bits in
          Uint.(max ~$200 (multiplication_complexity * iteration_count / gas_quad_divisor))
    | `Nine ->
        (* EIP-7883. *)
        fun ~base_length ~modulus_length ~exponent_length ~exponent_upper_256_bits ->
          let multiplication_complexity = calculate_multiplication_complexity ~base_length ~modulus_length in
          let iteration_count = calculate_iteration_count ~exponent_length ~exponent_upper_256_bits in
          Uint.(max ~$500 (multiplication_complexity * iteration_count))

  (* Read at most 256 most significant bits from a buffer, at an arbitrary position which may exceed the length
     of the buffer. This is used for reading the top word of the exponent, which is required for gas
     calculation, without reading the entire exponent. *)
  let read_at_most_256_bits (data : Bytes.t) ~(start : Uint.t) ~(length : Uint.t) : U256.t =
    let length = match Uint.to_int_opt length with None -> 32 | Some i -> min i 32 in
    match Uint.to_int_opt start with
    | Some i when i < Bytes.length data ->
        (* Number of bytes that's actually present in the data buffer (that is, not out of bounds). *)
        let in_range_bytes = min length (Bytes.length data - i) in
        let prefix = Bytes.sub data i in_range_bytes in
        let suffix = Bytes.make (length - in_range_bytes) '\x00' in
        U256.of_bytes_be_exn (prefix ^ suffix)
    | _ ->
        (* Start is beyond the input data length. Zero-padding gives 0. *)
        U256.zero

  (* Input length bounds checking. *)
  let parameter_length =
    let open Precompile in
    match revision with
    | `Eight ->
        (* EIP-2565. *)
        U256.to_uint <$> u256
    | `Nine ->
        (* EIP-7823. *)
        let$ len = U256.to_uint <$> u256 in
        let$ () = when_ Uint.(len > ~$1_024) precompile_failure in
        return len

  let address = Address.of_hex_string "0x05"

  let precompile (msg : Evmc.Message.t) : Evmc.Result.t =
    (* YP (234) *)
    Precompile.(
      run msg
        ((* YP (240) *)
         let$ base_length = parameter_length in
         (* YP (241) *)
         let$ exponent_length = parameter_length in
         (* YP (242) *)
         let$ modulus_length = parameter_length in

         let base_start = 3 * U256.byte_width in

         let$ () =
           (* YP (235), adjusted for EIP-2565 and EIP-7883. *)
           let gas_cost =
             (* EIP-2565 and EIP-7883 use a formula that would compute the least significant 256 bits, which is
                known to be an editorial mistake. We follow the Ethereum execution spec, which instead uses the
                most significant 256 bits. *)
             let exponent_upper_256_bits =
               let exponent_start = Uint.(~$base_start + base_length) in
               U256.to_uint
                 (read_at_most_256_bits msg.input_data ~start:exponent_start ~length:exponent_length)
             in
             calculate_gas_cost ~base_length ~modulus_length ~exponent_length ~exponent_upper_256_bits
           in
           spend_gas gas_cost
         in

         (* If we've been able to afford gas, we may assume base_length and modulus_length fit in an int
            (otherwise the multiplication_complexity term in the gas cost calculation would easily overflow
            gas limits even if exponent_length is zero). *)
         let base_length = Uint.to_int base_length in
         let modulus_length = Uint.to_int modulus_length in

         if modulus_length = 0 then return Bytes.empty
         else
           (* If modulus_length > 0 the multiplication_complexity term in the gas cost calculation is at least
              1. This means exponent_length must also fit in an int (otherwise the gas cost would have exceeded
              gas limits).
              TODO: once MONAD_EIGHT is obsoleted, the defensive coding here can be removed. *)
           let exponent_length = Uint.to_int exponent_length in
           (* YP (243) *)
           let$ base = Uint.of_bytes_be <$> bytes base_length in
           (* YP (244) *)
           let$ exponent = Uint.of_bytes_be <$> bytes exponent_length in
           (* YP (245) *)
           let$ modulus = Uint.of_bytes_be <$> bytes modulus_length in
           let result =
             if Uint.(modulus = zero || modulus = one) then Uint.zero
             else if Uint.(exponent = zero) then Uint.one
             else Uint.exp_mod base exponent ~modulo:modulus
           in
           let result_bytes = Uint.to_bytes_be result in
           (* As per EIP-198, the result must be a byte array of the same length as modulus_length, so
              it may be necessary to add padding. *)
           let padding_length = modulus_length - Bytes.length result_bytes in
           assert (padding_length >= 0) ;
           (* YP (239) *)
           return (Bytes.make padding_length '\x00' ^ result_bytes) ) )
end
