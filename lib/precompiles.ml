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

let ecrecover_address = Address.of_hex_string "0x01"
let ecrecover (msg : Evmc.Message.t) : Evmc.Result.t =
  check_gas msg
    Gas.(of_int 3_000)
    (fun () ->
      let d = msg.input_data in
      let h = B32.sub_with_zero_padding d 0 in
      let v = U256.of_repr (B32.sub_with_zero_padding d 32) in
      let r = U256.of_repr (B32.sub_with_zero_padding d 64) in
      let s = U256.of_repr (B32.sub_with_zero_padding d 96) in

      Option.(
        let$ y_parity =
          if U256.(v = ~$27) then Some U8.zero else if U256.(v = ~$28) then Some U8.one else None
        in
        let$ () = ensure U256.(r > zero && r < Crypto.secp256k1n) in
        let$ () = ensure U256.(s > zero && s < Crypto.secp256k1n) in

        try return (Address.to_bytes (Crypto.ecrecover {r; s; y_parity} h)) with _ -> None ) )

let sha256_address = Address.of_hex_string "0x02"
let sha256 (_msg : Evmc.Message.t) : Evmc.Result.t = failwith "todo"

let ripemd160_address = Address.of_hex_string "0x03"
let ripemd160 (_msg : Evmc.Message.t) : Evmc.Result.t = failwith "todo"

let identity_address = Address.of_hex_string "0x04"
let identity (_msg : Evmc.Message.t) : Evmc.Result.t = failwith "todo"

let modexp_address = Address.of_hex_string "0x05"
let modexp (_msg : Evmc.Message.t) : Evmc.Result.t = failwith "todo"

let alt_bn128_add_address = Address.of_hex_string "0x06"
let alt_bn128_add (_msg : Evmc.Message.t) : Evmc.Result.t = failwith "todo"

let alt_bn128_mul_address = Address.of_hex_string "0x07"
let alt_bn128_mul (_msg : Evmc.Message.t) : Evmc.Result.t = failwith "todo"

let alt_bn128_pairing_check_address = Address.of_hex_string "0x08"
let alt_bn128_pairing_check (_msg : Evmc.Message.t) : Evmc.Result.t = failwith "todo"

let blake2f_address = Address.of_hex_string "0x09"
let blake2f (_msg : Evmc.Message.t) : Evmc.Result.t = failwith "todo"

let point_evaluation_address = Address.of_hex_string "0x0a"
let point_evaluation (_msg : Evmc.Message.t) : Evmc.Result.t = failwith "todo"

let bls12_g1_add_address = Address.of_hex_string "0x0b"
let bls12_g1_add (_msg : Evmc.Message.t) : Evmc.Result.t = failwith "todo"

let bls12_g1_msm_address = Address.of_hex_string "0x0c"
let bls12_g1_msm (_msg : Evmc.Message.t) : Evmc.Result.t = failwith "todo"

let bls12_g2_add_address = Address.of_hex_string "0x0d"
let bls12_g2_add (_msg : Evmc.Message.t) : Evmc.Result.t = failwith "todo"

let bls12_g2_msm_address = Address.of_hex_string "0x0e"
let bls12_g2_msm (_msg : Evmc.Message.t) : Evmc.Result.t = failwith "todo"

let bls12_pairing_address = Address.of_hex_string "0x0f"
let bls12_pairing (_msg : Evmc.Message.t) : Evmc.Result.t = failwith "todo"

let bls12_map_fp_to_g1_address = Address.of_hex_string "0x10"
let bls12_map_fp_to_g1 (_msg : Evmc.Message.t) : Evmc.Result.t = failwith "todo"

let bls12_map_fp2_to_g2_address = Address.of_hex_string "0x11"
let bls12_map_fp2_to_g2 (_msg : Evmc.Message.t) : Evmc.Result.t = failwith "todo"

let precompiles : precompile Address.Map.t =
  Address.Map.of_list
    [ (ecrecover_address, ecrecover)
    ; (sha256_address, sha256)
    ; (ripemd160_address, ripemd160)
    ; (identity_address, identity)
    ; (modexp_address, modexp)
    ; (alt_bn128_add_address, alt_bn128_add)
    ; (alt_bn128_mul_address, alt_bn128_mul)
    ; (alt_bn128_pairing_check_address, alt_bn128_pairing_check)
    ; (blake2f_address, blake2f)
    ; (point_evaluation_address, point_evaluation)
    ; (bls12_g1_add_address, bls12_g1_add)
    ; (bls12_g1_msm_address, bls12_g1_msm)
    ; (bls12_g2_add_address, bls12_g2_add)
    ; (bls12_g2_msm_address, bls12_g2_msm)
    ; (bls12_pairing_address, bls12_pairing)
    ; (bls12_map_fp_to_g1_address, bls12_map_fp_to_g1)
    ; (bls12_map_fp2_to_g2_address, bls12_map_fp2_to_g2) ]
