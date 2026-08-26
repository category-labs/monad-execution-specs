(** Recursive-length prefix encoding and decoding, as defined in YP Appendix B. *)

open Byte_string

(** The type of RLP-encodable objects: either a byte string or a list of RLP-encodable objects. High-level types
    define encoding and decoding functions into this type. YP (190), YP (191), YP (192) *)
type t = Bytes of Bytes.t | List of t list [@@deriving to_yojson]

let of_bytes (bs : Bytes.t) = Bytes bs
let of_bytes32 (bs : B32.t) = Bytes (B32.to_bytes bs)

(** [to_string t] returns a human-readable representation of the given RLP structure [t]. *)
let rec to_string x =
  match x with
  | Bytes bs -> Format.sprintf "Bytes(\"%s\")" (Bytes.to_hex_string bs)
  | List elts -> List.map to_string elts |> String.concat ", " |> Format.sprintf "List(%s)"

let equal (x : t) (y : t) = x = y

(** [be x] encodes an integer as a big-endian byte array of minimal length. YP (195) *)
let be (x : int) =
  let x = Z.of_int x in
  let x_bytes = (Z.numbits x + 7) / 8 in
  let x_le = Z.to_bits x in
  let byte_i i = x_le.[x_bytes - i - 1] in
  Bytes.init x_bytes byte_i

(* Covers YP (194) cases 2, 3 and YP (197) cases 1, 2. YP (196) is implemented here as string concatenation. *)
let encode_payload payload ~long_payload_prefix ~short_payload_prefix =
  let len = Bytes.length payload in
  let header =
    if len <= 55 then
      (* Case ‖x‖ < 56 *)
      Bytes.of_char (Char.chr (short_payload_prefix + len))
    else
      (* Case ‖x‖ < 2⁶⁴, in practice the bound is lower due to OCaml's size limitations. *)
      let len_bytes = be len in
      let len_bytes_len = Bytes.length len_bytes in
      Bytes.(of_char (Char.chr (long_payload_prefix + len_bytes_len)) ^ len_bytes)
  in
  header ^ payload

let short_bytes_prefix = 0x80
let long_bytes_prefix = 0xb7
let short_list_prefix = 0xc0
let long_list_prefix = 0xf7

let encode_bytes (bs : Bytes.t) : Bytes.t =
  if Bytes.length bs = 1 && Char.code bs.[0] < short_bytes_prefix then bs
  else encode_payload bs ~short_payload_prefix:short_bytes_prefix ~long_payload_prefix:long_bytes_prefix

let rec encode_list (encoded_items : Bytes.t list) : Bytes.t =
  (* YP (198) *)
  let bs = Bytes.(concat empty encoded_items) in
  encode_payload bs ~short_payload_prefix:short_list_prefix ~long_payload_prefix:long_list_prefix

(** [encode obj] RLP-encodes the object [obj] into a byte array. YP (193) *)
and encode (obj : t) : Bytes.t =
  (* TODO: OCaml's maximum string length is much smaller than 2^64, so we should switch to Bigarray *)
  match obj with
  | Bytes bs -> encode_bytes bs
  | List ls -> encode_list (List.map encode ls)

(** [decode_first bs] decodes the first RLP-encoded object in the byte array [bs] and returns it and any
    remaining bytes. [bs] must be non-empty, otherwise a runtime error is raised. *)
let rec decode_first (bs : Bytes.t) : t * Bytes.t =
  let len = Bytes.length bs in
  assert (len > 0) ;
  let tag = Char.code bs.[0] in
  let payload_start, payload_len =
    match tag with
    | b when b < short_bytes_prefix -> (0, 1)
    | b when b >= short_bytes_prefix && b <= long_bytes_prefix -> (1, b - short_bytes_prefix)
    | b when b > long_bytes_prefix && b < short_list_prefix ->
        let payload_len_len = b - long_bytes_prefix in
        let payload_len = Z.(to_int (of_bits (Bytes.reverse (Bytes.sub bs 1 payload_len_len) :> string))) in
        (1 + payload_len_len, payload_len)
    | b when b >= short_list_prefix && b <= long_list_prefix -> (1, b - short_list_prefix)
    | b ->
        let payload_len_len = b - long_list_prefix in
        let payload_len = Z.(to_int (of_bits (Bytes.reverse (Bytes.sub bs 1 payload_len_len) :> string))) in
        (1 + payload_len_len, payload_len)
  in
  let payload = Bytes.sub bs payload_start payload_len in
  let rest = Bytes.sub bs (payload_start + payload_len) (len - payload_start - payload_len) in
  if tag < short_list_prefix then (Bytes payload, rest) else (List (decode_all payload), rest)

(** [decode_all bs] repeatedly applies [decode_first] to the byte array [bs] until it is empty, returning
    a list containing the decoded objects. *)
and decode_all (bs : Bytes.t) : t list =
  if Bytes.length bs = 0 then []
  else
    let fst, rest = decode_first bs in
    fst :: decode_all rest

(** [decode bs] behaves as [decode_first bs] except the input [bs] must contain exactly one RLP-encoded object,
    otherwise a runtime error is raised. *)
let decode (bytes : Bytes.t) =
  let obj, rest = decode_first bytes in
  assert (Bytes.length rest = 0) ;
  obj
