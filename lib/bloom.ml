(** 256-byte Bloom filters, used to index Ethereum logs. *)

open Byte_string
include B256

(* M_{3:2048} in YP (31) to YP (34) *)
let hash_bytes (bytes : Bytes.t) : t =
  let of_bit_indices (indices : int list) : t = List.fold_left set_bit zeros indices in
  let byte_pair_at (bytes : B32.t) index =
    let b0 = B32.(bytes.$(index)) in
    let b1 = B32.(bytes.$(index + 1)) in
    (Char.code b0 lsl 8) + Char.code b1
  in
  let hashed_bytes = Crypto.keccak_256 bytes in
  [0; 2; 4]
  |> List.map (fun i ->
      let bp = byte_pair_at hashed_bytes i in
      0x07ff - (bp land 0x07ff) )
  |> of_bit_indices
