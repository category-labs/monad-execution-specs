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

let secp256k1_recover (r : U256.t) (s : U256.t) (v : U256.t) (hash : U256.t) : Bytes.t =
  let open U256 in
  let is_square =
    exp_mod (exp_mod r ~$3 ~modulo:secp256k1p + secp256k1b) ((secp256k1p - ~$1) / ~$2) ~modulo:secp256k1p
  in
  assert (is_square = one) ;
  ()
