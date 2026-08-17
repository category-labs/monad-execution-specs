(** 256-byte Bloom filters, used to index Ethereum logs. *)

open Byte_string
include B256

(** [logor b1 b2] computes the bitwise OR of [b1] and [b2]. *)
let logor (b1 : t) (b2 : t) : t = init (fun i -> Char.unsafe_chr (Char.code b1.$(i) lor Char.code b2.$(i)))

(** [union bs] returns the bitwise OR of all the logs in the sequence [bs], or zero if it is empty. *)
let union (bs : t Seq.t) : t = Seq.fold_left logor zeros bs

(** [set_bit b i] returns [b] with its [i]-th bit set to 1. [i] must be in the range \[[0], [2048]). *)
let set_bit (bloom : t) (bit_index : int) =
  let byte_index = bit_index / 8 in
  let bit_index = bit_index mod 8 in
  init (fun i ->
      if Stdlib.(i = byte_index) then Char.unsafe_chr (Char.code bloom.$(i) lor (128 lsr bit_index))
      else bloom.$(i) )

(** [test_bit b i] returns [true] if the [i]-th bit of [b] is set. [i] must be in the range \[[0], [2048]). *)
let test_bit (bloom : t) (bit_index : int) : bool =
  let byte_index = bit_index / 8 in
  let bit_index = bit_index mod 8 in
  Stdlib.(Char.code bloom.$(byte_index) land (1 lsl bit_index) <> 0)

(** Digest an arbitrary byte-string into a Bloom filter by computing M_\{3:2048\} in YP (31), YP (32), YP (33),
    YP (34). *)
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
