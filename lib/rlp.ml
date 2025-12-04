type t = Bytes of Byte_string.t | List of t list

let of_bytes (bs : Byte_string.t) = Bytes bs
let of_bytes32 (bs : Byte_string.B32.t) = Bytes (bs :> Byte_string.t)

let rec to_string x =
  match x with
  | Bytes bs -> Format.sprintf "Bytes(\"%s\")" (Byte_string.to_hex_string bs)
  | List elts -> List.map to_string elts |> String.concat ", " |> Format.sprintf "List(%s)"

let equal x y = x = y

let encode_payload payload ~long_payload_prefix ~short_payload_prefix =
  let len = Byte_string.length payload in
  let header =
    if len <= 55 then Byte_string.of_char (Char.chr (short_payload_prefix + len))
    else
      let len_hex = Format.sprintf "%x" len in
      let len_bytes = Byte_string.of_hex_string len_hex in
      let len_bytes_len = Byte_string.length len_bytes in
      Byte_string.(of_char (Char.chr (long_payload_prefix + len_bytes_len)) ^ len_bytes)
  in
  Byte_string.(header ^ payload)

let short_bytes_prefix = 0x80
let long_bytes_prefix = 0xb7
let short_list_prefix = 0xc0
let long_list_prefix = 0xf7

(* TODO: OCaml's maximum string length is much smaller than 2^64, so we should switch to Bigarray *)
let rec encode (obj : t) : Byte_string.t =
  match obj with
  | Bytes bs when Byte_string.length bs = 1 && Char.code Byte_string.(bs.$(0)) < short_bytes_prefix -> bs
  | Bytes bs ->
      encode_payload bs ~short_payload_prefix:short_bytes_prefix ~long_payload_prefix:long_bytes_prefix
  | List ls ->
      let bs = Byte_string.concat Byte_string.empty (List.map encode ls) in
      encode_payload bs ~short_payload_prefix:short_list_prefix ~long_payload_prefix:long_list_prefix

(** [decode_first bs] decodes the first RLP-encoded object in the byte array [bs] and returns it and any
    remaining bytes. [bs] must be non-empty. *)
let rec decode_first (bs : Byte_string.t) : t * Byte_string.t =
  let len = Byte_string.length bs in
  assert (len > 0) ;
  let tag = Char.code Byte_string.(bs.$(0)) in
  let payload_start, payload_len =
    match tag with
    | b when b < short_bytes_prefix -> (0, 1)
    | b when b >= short_bytes_prefix && b <= long_bytes_prefix -> (1, b - short_bytes_prefix)
    | b when b > long_bytes_prefix && b < short_list_prefix ->
        let payload_len_len = b - long_bytes_prefix in
        let payload_len = Z.(to_int (of_bits ((Byte_string.reverse (Byte_string.sub bs 1 payload_len_len)) :> string))) in
        (1 + payload_len_len, payload_len)
    | b when b >= short_list_prefix && b <= long_list_prefix -> (1, b - short_list_prefix)
    | b ->
        let payload_len_len = b - long_list_prefix in
        let payload_len = Z.(to_int (of_bits ((Byte_string.reverse (Byte_string.sub bs 1 payload_len_len)) :> string))) in
        (1 + payload_len_len, payload_len)
  in
  let payload = Byte_string.sub bs payload_start payload_len in
  let rest = Byte_string.sub bs (payload_start + payload_len) (len - payload_start - payload_len) in
  if tag < short_list_prefix then (Bytes payload, rest) else (List (decode_all payload), rest)

(** [decode_all bs] repeatedly applies [decode_first] to the byte array [bs] until it is empty, returning
    a list containing the decoded objects. *)
and decode_all (bs : Byte_string.t) : t list =
  if Byte_string.length bs = 0 then []
  else
    let fst, rest = decode_first bs in
    fst :: decode_all rest

(** [decode bs] behaves as [decode_first bs] except the input [bs] must contain exactly one RLP-encoded object. *)
let decode (bytes : Byte_string.t) =
  let obj, rest = decode_first bytes in
  assert (Byte_string.length rest = 0) ;
  obj
