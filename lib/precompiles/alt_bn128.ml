(** EIP-196 and EIP-197: alt_bn128 addition, scalar multiplication and pairing. *)

open Byte_string
open Numeric
open Chain.Ethereum

open Utils

open Ec.Alt_bn128
open Ec_precompile_utils (struct
  (* As per EIP-196, field elements and scalars are encoded as 32 byte big-endian numbers. *)
  module C1_coord_repr = B32
  include Ec.Alt_bn128

  (* See YP (263), YP (264), YP (265). *)
  let complex_encoding = `Imaginary_first
end)

(* Pricings are as per Monad §4.2. *)

let add_address = Address.of_hex_string "0x06"
let add (msg : Evmc.Message.t) : Evmc.Result.t =
  (* YP (279) *)
  Precompile.(
    run msg
      ((* YP (281), adjusted for Monad §4.2. *)
       let$ () = spend_gas Gas.(of_int 300) in

       (* YP (283) *)
       let$ p_0 = point_c1 in
       (* YP (284) *)
       let$ p_1 = point_c1 in

       (* YP (282) *)
       return (delta_1_inv C_1.(p_0 + p_1)) ) )

let mul_address = Address.of_hex_string "0x07"
let mul (msg : Evmc.Message.t) : Evmc.Result.t =
  (* YP (286) *)
  Precompile.(
    run msg
      ((* YP (288), adjusted for Monad §4.2. *)
       let$ () = spend_gas Gas.(of_int 30_000) in

       (* YP (290) *)
       let$ p_0 = point_c1 in
       (* YP (291) *)
       let$ n = U256.to_uint <$> u256 in

       (* YP (289) *)
       return (delta_1_inv C_1.(n * p_0)) ) )

let pairing_check_address = Address.of_hex_string "0x08"
let pairing_check (msg : Evmc.Message.t) : Evmc.Result.t =
  (* YP (268) *)
  Precompile.(
    run msg
      (let n = Bytes.length msg.input_data in
       (* YP (270) is checked here and implicitly in the binding of pairs below. *)
       let$ () = ensure (n mod 192 = 0) in
       (* YP (271) *)
       let k = n / 192 in
       (* YP (272), adjusted for Monad §4.2. *)
       let$ () = spend_gas Gas.(~$5 * ((~$34_000 * ~$k) + ~$45_000)) in

       (* YP (275), YP (276), YP (277), YP (278) *)
       let$ pairs : (G_1.t * G_2.t) list = list k (pair point_g1 point_g2) in

       (* YP (273), YP (274) *)
       let result = pairing_check pairs in
       return (B32.to_bytes (U256.to_repr (if result then U256.one else U256.zero))) ) )
