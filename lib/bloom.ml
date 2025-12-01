(** 256-byte Bloom filters, used to index Ethereum logs. *)
open Numeric

module Impl : sig
  type t = private Bytes.t

  val zeros : t
  val init : char -> t
  val make : (int -> char) -> t

  (* Reinterprets the input as a Bloom filter. Will throw an exception if the input is not exactly 256 bytes
     long. *)
  val of_raw_bytes_exn : Bytes.t -> t
end = struct
  type t = Bytes.t

  let length = 256

  let zeros : t = Bytes.make length '\x00'
  let init c : t = Bytes.make length c
  let make b_i : t = Bytes.init length b_i

  let of_raw_bytes_exn bs =
    assert (Bytes.length bs = 256) ;
    bs
end

include Impl

let ( = ) (b1 : t) (b2 : t) = Bytes.equal (b1 :> Bytes.t) (b2 :> Bytes.t)

let logor (b1 : t) (b2 : t) : t =
  let b1 = (b1 :> Bytes.t) in
  let b2 = (b2 :> Bytes.t) in
  make (fun i -> Char.unsafe_chr (Char.code b1.[i] lor Char.code b2.[i]))

let union (bs : t Seq.t) : t = Seq.fold_left logor zeros bs

let set_bit (bloom : t) (bit_index : int) =
  let bloom = (bloom :> Bytes.t) in
  let byte_index = bit_index / 8 in
  let bit_index = bit_index mod 8 in
  make (fun i ->
      if Stdlib.(i = byte_index) then Char.unsafe_chr (Char.code bloom.[i] lor (1 lsl bit_index))
      else bloom.[i] )

let test_bit (bloom : t) (bit_index : int) : bool =
  let bloom = (bloom :> Bytes.t) in
  let byte_index = bit_index / 8 in
  let bit_index = bit_index mod 8 in
  Char.code bloom.[byte_index] land (1 lsl bit_index) <> 0

(* M_{3:2048} in YP (31) to YP (34) *)
let of_bytes (bytes : Bytes.t) : t =
  let of_bit_indices (indices : int list) : t = List.fold_left set_bit zeros indices in
  let byte_pair_at bytes index =
    let b0 = bytes.[index] in
    let b1 = bytes.[index + 1] in
    (Char.code b0 lsl 8) + Char.code b1
  in
  let hash_bytes = U256.to_bytes_be (Crypto.keccak_256 bytes) in
  [0; 2; 4]
  |> List.map (fun i ->
      let bp = byte_pair_at hash_bytes i in
      0x07ff - (bp land 0x07ff) )
  |> of_bit_indices

let of_yojson (json : Yojson.Safe.t) : (t, string) result =
  match json with
  | `String str ->
      let bytes = Bytes.of_hex_string str in
      if Int.(equal (Bytes.length bytes) 256) then Ok (of_raw_bytes_exn bytes)
      else Error "Byte string must be 256 bytes"
  | _ -> Error "Expected string"

let of_yojson_exn (json : Yojson.Safe.t) : t =
  match of_yojson json with Ok bloom -> bloom | Error err -> raise (Invalid_argument err)

let to_yojson (x : t) : Yojson.Safe.t = `String (Format.sprintf "0x%s" (Bytes.to_hex_string (x :> Bytes.t)))

let to_rlp (x: t) : Rlp.t = Rlp.Bytes (x :> Bytes.t)
