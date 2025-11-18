(** Bindings to cryptographic functions in external libraries. *)

open Numeric

(** [keccak_256 bytes] computes the Keccak-256 digest of a byte array. *)
let keccak_256 (input : Bytes.t) : U256.t =
  let bytes = Digestif.KECCAK_256.(to_raw_string (digest_string input)) in
  U256.of_bytes_be bytes

(** The Keccak-256 encoding of the empty byte array. *)
let keccak_256_empty = keccak_256 Bytes.empty
