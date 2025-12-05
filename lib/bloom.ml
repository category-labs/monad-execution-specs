(** 256-byte Bloom filters, used to index Ethereum logs. *)

open Byte_string
include B256

let logor (b1 : t) (b2 : t) : t = init (fun i -> Char.unsafe_chr (Char.code b1.$(i) lor Char.code b2.$(i)))

let union (bs : t Seq.t) : t = Seq.fold_left logor zeros bs

let set_bit (bloom : t) (bit_index : int) =
  let byte_index = bit_index / 8 in
  let bit_index = bit_index mod 8 in
  init (fun i ->
      if Stdlib.(i = byte_index) then Char.unsafe_chr (Char.code bloom.$(i) lor (1 lsl bit_index))
      else bloom.$(i) )

let test_bit (bloom : t) (bit_index : int) : bool =
  let byte_index = bit_index / 8 in
  let bit_index = bit_index mod 8 in
  Stdlib.(Char.code bloom.$(byte_index) land (1 lsl bit_index) <> 0)

(* M_{3:2048} in YP (31) to YP (34) *)
let hash_bytes (bytes : Bytes.t) : t =
  let of_bit_indices (indices : int list) : t = List.fold_left set_bit zeros indices in
  let byte_pair_at (bytes : B32.t) index =
    let b0 = B32.(bytes.$(index)) in
    let b1 = B32.(bytes.$(index + 1)) in
    (Char.code b0 lsl 8) + Char.code b1
  in
  let hash_bytes = Crypto.keccak_256 bytes in
  [0; 2; 4]
  |> List.map (fun i ->
      let bp = byte_pair_at hash_bytes i in
      0x07ff - (bp land 0x07ff) )
  |> of_bit_indices
