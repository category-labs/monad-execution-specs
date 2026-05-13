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
