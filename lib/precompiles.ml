open Byte_string
open Numeric
open Chain.Ethereum

module M = State.TransactionState.M
type precompile = Evmc.Message.t -> Evmc.Result.t M.t

let success ~gas_left ~output_data =
  Evmc.Result.
    {status_code = StatusCode.Success; gas_left; gas_refund = 0L; output_data; create_address = Address.zero}

(* Note that Monad does not refund gas on transaction success. This also applies to precompiles. *)
let ethereum_precompile (msg : Evmc.Message.t) (gas : Gas.t) (exec : unit -> Bytes.t option) :
    Evmc.Result.t M.t =
  let result =
    match () with
    | () when msg.delegated ->
        (* As per EIP-7702, calls to Ethereum precompiles through a delegation behave as if the code of the
           precompile was empty. Monad precompiles may behave differently. *)
        success ~gas_left:msg.gas ~output_data:Bytes.empty
    | () when Gas.(of_uint64 msg.gas < gas) -> Evmc.Result.(failure StatusCode.Out_of_gas)
    | () -> (
      match exec () with
      | None -> Evmc.Result.(failure StatusCode.Precompile_failure)
      | Some output_data -> success ~gas_left:Gas.(to_uint64 (of_uint64 msg.gas - gas)) ~output_data )
  in
  M.return result

let ecrecover_address = Address.of_hex_string "0x01"
let ecrecover (msg : Evmc.Message.t) : Evmc.Result.t M.t =
  ethereum_precompile msg
    Gas.(of_int 6_000)
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

        let$ addr = Crypto.ecrecover {r; s; y_parity} h in

        return (B32.to_bytes (Address.to_bytes32 addr)) )
      |> Option.value ~default:Bytes.empty
      |> Option.return )

let sha256_address = Address.of_hex_string "0x02"
let sha256 (msg : Evmc.Message.t) : Evmc.Result.t M.t =
  ethereum_precompile msg
    Gas.(~$60 + (~$12 * bytes_to_whole_words ~$(Bytes.length msg.input_data)))
    (fun () -> Some (B32.to_bytes (Crypto.sha_256 msg.input_data)))

let ripemd160_address = Address.of_hex_string "0x03"
let ripemd160 (msg : Evmc.Message.t) : Evmc.Result.t M.t =
  ethereum_precompile msg
    Gas.(~$600 + (~$120 * bytes_to_whole_words ~$(Bytes.length msg.input_data)))
    (fun () -> Some (B32.to_bytes (B20.to_bytes32 (Crypto.ripemd_160 msg.input_data))))

let identity_address = Address.of_hex_string "0x04"
let identity (msg : Evmc.Message.t) : Evmc.Result.t M.t =
  ethereum_precompile msg
    Gas.(~$15 + (~$3 * bytes_to_whole_words ~$(Bytes.length msg.input_data)))
    (fun () -> Some msg.input_data)

let modexp_address = Address.of_hex_string "0x05"
let modexp (msg : Evmc.Message.t) : Evmc.Result.t M.t =
  ethereum_precompile msg Gas.zero (fun () -> failwith "todo 4")

let alt_bn128_add_address = Address.of_hex_string "0x06"
let alt_bn128_add (msg : Evmc.Message.t) : Evmc.Result.t M.t =
  ethereum_precompile msg Gas.zero (fun () -> failwith "todo 5")

let alt_bn128_mul_address = Address.of_hex_string "0x07"
let alt_bn128_mul (msg : Evmc.Message.t) : Evmc.Result.t M.t =
  ethereum_precompile msg Gas.zero (fun () -> failwith "todo 6")

let alt_bn128_pairing_check_address = Address.of_hex_string "0x08"
let alt_bn128_pairing_check (msg : Evmc.Message.t) : Evmc.Result.t M.t =
  ethereum_precompile msg Gas.zero (fun () -> failwith "todo 7")

let blake2f_address = Address.of_hex_string "0x09"
let blake2f (msg : Evmc.Message.t) : Evmc.Result.t M.t =
  ethereum_precompile msg Gas.zero (fun () -> failwith "todo 8")

let point_evaluation_address = Address.of_hex_string "0x0a"
let point_evaluation (msg : Evmc.Message.t) : Evmc.Result.t M.t =
  ethereum_precompile msg Gas.zero (fun () -> failwith "todo 9")

let bls12_g1_add_address = Address.of_hex_string "0x0b"
let bls12_g1_add (msg : Evmc.Message.t) : Evmc.Result.t M.t =
  ethereum_precompile msg Gas.zero (fun () -> failwith "todo 10")

let bls12_g1_msm_address = Address.of_hex_string "0x0c"
let bls12_g1_msm (msg : Evmc.Message.t) : Evmc.Result.t M.t =
  ethereum_precompile msg Gas.zero (fun () -> failwith "todo 11")

let bls12_g2_add_address = Address.of_hex_string "0x0d"
let bls12_g2_add (msg : Evmc.Message.t) : Evmc.Result.t M.t =
  ethereum_precompile msg Gas.zero (fun () -> failwith "todo 12")

let bls12_g2_msm_address = Address.of_hex_string "0x0e"
let bls12_g2_msm (msg : Evmc.Message.t) : Evmc.Result.t M.t =
  ethereum_precompile msg Gas.zero (fun () -> failwith "todo 13")

let bls12_pairing_address = Address.of_hex_string "0x0f"
let bls12_pairing (msg : Evmc.Message.t) : Evmc.Result.t M.t =
  ethereum_precompile msg Gas.zero (fun () -> failwith "todo 14")

let bls12_map_fp_to_g1_address = Address.of_hex_string "0x10"
let bls12_map_fp_to_g1 (msg : Evmc.Message.t) : Evmc.Result.t M.t =
  ethereum_precompile msg Gas.zero (fun () -> failwith "todo 15")

let bls12_map_fp2_to_g2_address = Address.of_hex_string "0x11"
let bls12_map_fp2_to_g2 (msg : Evmc.Message.t) : Evmc.Result.t M.t =
  ethereum_precompile msg Gas.zero (fun () -> failwith "todo 16")

module Reserve_balance = struct
  (** MIP-4: reserve balance introspection precompile. *)

  let address = Address.of_hex_string "0x1001"

  (* TODO: Currently the selector handling and the return value encoding are hard-coded. Once the Solidity ABI
     helpers are merged from the staking precompile, the code here should be updated. *)
  let selector_dipped_into_reserve = Bytes.(~@"0x3a61584e")
  let gas_dipped_into_reserve = Gas.(~$100)

  let revert (msg : string) : Evmc.Result.t =
    (* The error message is returned directly, it is not ABI-encoded. *)
    Evmc.Result.
      { status_code = StatusCode.Revert
      ; gas_left = 0L
      ; gas_refund = 0L
      ; output_data = msg
      ; create_address = Address.zero }

  let precompile (msg : Evmc.Message.t) : Evmc.Result.t M.t =
    M.(
      let invoked_via_call = msg.kind = Call && (not msg.static) && not msg.delegated in
      if not invoked_via_call then return Evmc.Result.(failure Rejected)
      else if Gas.(of_uint64 msg.gas < gas_dipped_into_reserve) then return Evmc.Result.(failure Out_of_gas)
      else if Bytes.length msg.input_data < 4 then return (revert "method not supported")
      else if Bytes.sub msg.input_data 0 4 <> selector_dipped_into_reserve then
        return (revert "method not supported")
      else if U256.(msg.value <> zero) then return (revert "value is nonzero")
      else if Bytes.length msg.input_data > 4 then return (revert "input is invalid")
      else
        (* The reserve balance precompile is only available starting at MONAD_NINE, so it uses that revision's
           notion of reserve balance. *)
        let$ dipped = Reserve_balance.dipped_into_reserve `Nine in
        let output_data = U256.to_repr_bytes (if dipped then U256.one else U256.zero) in
        return (success ~gas_left:Gas.(to_uint64 (of_uint64 msg.gas - gas_dipped_into_reserve)) ~output_data) )
end

let precompiles_eight : precompile Address.Map.t =
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

let precompiles_nine : precompile Address.Map.t =
  let new_precompiles = List.to_seq [Reserve_balance.(address, precompile)] in
  Address.Map.add_seq new_precompiles precompiles_eight

let precompiles (revision : Chain.Monad.Revision.active) : precompile Address.Map.t =
  match revision with `Eight -> precompiles_eight | `Nine -> precompiles_nine
