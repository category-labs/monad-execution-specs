open Utils
open Numeric

let keccak_256 (input : Bytes.t) : U256.t =
  let bytes = Digestif.KECCAK_256.(to_raw_string (digest_string input)) in
  U256.of_bytes_be bytes
