(* This module avoids using Byte_string to allow Byte_string to define of_rlp, to_rlp functions which are very
   useful in general. *)
let to_hex_string (bytes : String.t) =
  String.to_seq bytes
  |> Seq.map Char.code
  |> Seq.map (Format.sprintf "%02x")
  |> List.of_seq
  |> String.concat ""

let reverse (str : String.t) =
  let n = String.length str in
  String.mapi (fun i _ -> str.[n - i - 1]) str

type t = Bytes of String.t | List of t list

let of_bytes (bs : String.t) = Bytes bs

let rec to_string x =
  match x with
  | Bytes bs -> Format.sprintf "Bytes(\"%s\")" (to_hex_string bs)
  | List elts -> List.map to_string elts |> String.concat ", " |> Format.sprintf "List(%s)"

let equal x y = x = y

let encode_payload payload ~long_payload_prefix ~short_payload_prefix =
  let len = String.length payload in
  let header =
    if len <= 55 then String.make 1 (Char.chr (short_payload_prefix + len))
    else
      let len = Z.of_int len in
      let len_bytes = (Z.numbits len + 7) / 8 in
      let len_bytes =
        let len_le = Z.to_bits len in
        let byte_i i = len_le.[len_bytes - i - 1] in
        String.init len_bytes byte_i
      in
      let len_bytes_len = String.length len_bytes in
      String.(make 1 (Char.chr (long_payload_prefix + len_bytes_len)) ^ len_bytes)
  in
  header ^ payload

let short_bytes_prefix = 0x80
let long_bytes_prefix = 0xb7
let short_list_prefix = 0xc0
let long_list_prefix = 0xf7

(* TODO: OCaml's maximum string length is much smaller than 2^64, so we should switch to Bigarray *)
let rec encode (obj : t) : String.t =
  match obj with
  | Bytes bs when String.length bs = 1 && Char.code bs.[0] < short_bytes_prefix -> bs
  | Bytes bs ->
      encode_payload bs ~short_payload_prefix:short_bytes_prefix ~long_payload_prefix:long_bytes_prefix
  | List ls ->
      let bs = String.concat String.empty (List.map encode ls) in
      encode_payload bs ~short_payload_prefix:short_list_prefix ~long_payload_prefix:long_list_prefix

(** [decode_first bs] decodes the first RLP-encoded object in the byte array [bs] and returns it and any
    remaining bytes. [bs] must be non-empty. *)
let rec decode_first (bs : String.t) : t * String.t =
  let len = String.length bs in
  assert (len > 0) ;
  let tag = Char.code bs.[0] in
  let payload_start, payload_len =
    match tag with
    | b when b < short_bytes_prefix -> (0, 1)
    | b when b >= short_bytes_prefix && b <= long_bytes_prefix -> (1, b - short_bytes_prefix)
    | b when b > long_bytes_prefix && b < short_list_prefix ->
        let payload_len_len = b - long_bytes_prefix in
        let payload_len = Z.(to_int (of_bits (reverse (String.sub bs 1 payload_len_len) :> string))) in
        (1 + payload_len_len, payload_len)
    | b when b >= short_list_prefix && b <= long_list_prefix -> (1, b - short_list_prefix)
    | b ->
        let payload_len_len = b - long_list_prefix in
        let payload_len = Z.(to_int (of_bits (reverse (String.sub bs 1 payload_len_len) :> string))) in
        (1 + payload_len_len, payload_len)
  in
  let payload = String.sub bs payload_start payload_len in
  let rest = String.sub bs (payload_start + payload_len) (len - payload_start - payload_len) in
  if tag < short_list_prefix then (Bytes payload, rest) else (List (decode_all payload), rest)

(** [decode_all bs] repeatedly applies [decode_first] to the byte array [bs] until it is empty, returning
    a list containing the decoded objects. *)
and decode_all (bs : String.t) : t list =
  if String.length bs = 0 then []
  else
    let fst, rest = decode_first bs in
    fst :: decode_all rest

(** [decode bs] behaves as [decode_first bs] except the input [bs] must contain exactly one RLP-encoded object. *)
let decode (bytes : String.t) =
  let obj, rest = decode_first bytes in
  assert (String.length rest = 0) ;
  obj
