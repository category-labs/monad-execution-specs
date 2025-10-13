open Utils

let keccak_256 (input : Bytes.t) : Word.t =
  let bytes = Digestif.KECCAK_256.(to_raw_string (digest_string input)) in
  Word.of_bytes_be bytes
