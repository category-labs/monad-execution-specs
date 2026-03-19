open Byte_string
open Numeric
open Chain.Ethereum
open State

open Utils

type precompile = Evmc.Message.t -> Evmc.Result.t TransactionState.M.t

let ecrecover_address = Address.of_hex_string "0x01"
let ecrecover (msg : Evmc.Message.t) : precompile_result =
  Precompile.(
    run msg
      ((* Monad §4.2. *)
       let$ () = spend_gas Gas.(of_int 6_000) in
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
let sha256 (msg : Evmc.Message.t) : precompile_result =
  Precompile.(
    run msg
      (let$ () = spend_gas Gas.(~$60 + (~$12 * bytes_to_whole_words ~$(Bytes.length msg.input_data))) in
       return (B32.to_bytes (Crypto.sha_256 msg.input_data)) ) )

let ripemd160_address = Address.of_hex_string "0x03"
let ripemd160 (msg : Evmc.Message.t) : precompile_result =
  Precompile.(
    run msg
      (let$ () = spend_gas Gas.(~$600 + (~$120 * bytes_to_whole_words ~$(Bytes.length msg.input_data))) in
       return (B32.to_bytes (B20.to_bytes32 (Crypto.ripemd_160 msg.input_data))) ) )

let identity_address = Address.of_hex_string "0x04"
let identity (msg : Evmc.Message.t) : precompile_result =
  Precompile.(
    run msg
      (let$ () = spend_gas Gas.(~$15 + (~$3 * bytes_to_whole_words ~$(Bytes.length msg.input_data))) in
       return msg.input_data ) )

let blake2f_address = Address.of_hex_string "0x09"
let blake2f (msg : Evmc.Message.t) : precompile_result =
  Precompile.(
    run msg
      (let$ () = ensure (Bytes.length msg.input_data = 213) in
       let$ r = u32 in

       (* Monad §4.2: blake2f cost is 2x the rounds. *)
       let$ () = spend_gas Gas.(~$2 * U32.(to_uint r)) in

       (* r must fit in an int since we were able to afford the gas. *)
       let$ r = Option.or_fail (U32.to_int_opt r) in

       let$ h = Iarray.of_list <$> list 8 uint64_le in
       let$ m = Iarray.of_list <$> list 16 uint64_le in

       let$ t_low = uint64_le in
       let$ t_high = uint64_le in

       let$ f =
         byte >>= function '\x00' -> return false | '\x01' -> return true | _ -> precompile_failure
       in

       Iarray.to_list (Crypto.blake2f ~rounds:r ~h ~m ~t0:t_low ~t1:t_high ~final_block:f)
       |> List.map (fun i -> U64.of_uint64 i |> U64.to_repr |> B8.reverse |> B8.to_bytes)
       |> Bytes.(concat empty)
       |> return ) )

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
    ; Bls12_381.(g1_add_address, g1_add)
    ; Bls12_381.(g1_msm_address, g1_msm)
    ; Bls12_381.(g2_add_address, g2_add)
    ; Bls12_381.(g2_msm_address, g2_msm)
    ; Bls12_381.(pairing_check_address, pairing_check)
    ; Bls12_381.(map_fp_to_g1_address, map_fp_to_g1)
    ; Bls12_381.(map_fp2_to_g2_address, map_fp2_to_g2)
    ; Secp256r1.(address, verify) ]

let precompile_addresses : Address.Set.t =
  Address.Map.to_seq precompiles |> Seq.map (fun (addr, _precompile) -> addr) |> Address.Set.of_seq

(* Monad allows for privileged system transactions to call into special endpoints of certain precompiles.
   Currently this is only the staking precompile. *)
let syscall_endpoints : precompile Address.Map.t =
  Address.Map.of_list [(Staking.staking_address, Staking.staking_syscalls)]

let syscall_endpoint_addresses : Address.Set.t =
  Address.Map.to_seq syscall_endpoints |> Seq.map (fun (addr, _endpoint) -> addr) |> Address.Set.of_seq
