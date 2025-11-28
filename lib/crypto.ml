(** Bindings to cryptographic functions in external libraries. *)

open Numeric

(** [keccak_256 bytes] computes the Keccak-256 digest of a byte array. *)
let keccak_256 (input : Bytes.t) : U256.t =
  let bytes = Digestif.KECCAK_256.(to_raw_string (digest_string input)) in
  U256.of_bytes_be bytes

(** The Keccak-256 encoding of the empty byte array. *)
let keccak_256_empty = keccak_256 Bytes.empty

let secp256k1b = U256.(~$7)
let secp256k1p = U256.(~@"0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F")
let secp256k1n = U256.(~@"0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141")

let context = Libsecp256k1.External.Context.create ()

let secp256k1_recover (r : U256.t) (s : U256.t) (v : U256.t) (msg_hash : U256.t) : Bytes.t =
  let is_square =
    U256.(
      one
      = exp_mod (exp_mod r ~$3 ~modulo:secp256k1p + secp256k1b) ((secp256k1p - ~$1) / ~$2) ~modulo:secp256k1p )
  in
  assert is_square ;
  Libsecp256k1.External.(
    let r_bytes = U256.to_bytes_be r in
    let s_bytes = U256.to_bytes_be s in
    let v_bytes = U256.to_bytes_be v in
    let signature_i = function
      | i when i < 32 -> r_bytes.[i]
      | i when i < 64 -> s_bytes.[i - 32]
      | _ -> v_bytes.[31]
    in
    let signature = Sign.read_recoverable_exn context (Bigstring.init Sign.recoverable_bytes signature_i) in
    let result_bigstring =
      msg_hash
      |> U256.to_bytes_be
      |> Bigstring.of_string
      |> Sign.recover_exn context ~signature
      |> Key.to_bytes ~compress:false context
    in
    let result_i i = result_bigstring.{i + 1} in
    let result = Bytes.init 64 result_i in
    result )
