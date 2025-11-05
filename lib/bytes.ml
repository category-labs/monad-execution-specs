(** Immutable byte arrays, as opposed to the mutable [Stdlib.Bytes.t], and associated utilities. *)
include String

(** [sub_with_zero_padding bytes i sz] returns a [sz]-length byte array formed by zero-padding
      the array [bytes[i, min(len(bytes), i+sz))]] to [length sz]. *)
let sub_with_zero_padding bytes i sz =
  init sz (fun j -> if i + j >= length bytes then '\x00' else bytes.[i + j])

(** Print [bytes] as a hexadecimal string, without a '0x' prefix. *)
let to_hex_string bytes =
  to_seq bytes |> Seq.map Char.code |> Seq.map (Format.sprintf "%02x") |> List.of_seq |> String.concat ""

(** Parse a string consisting of an even number of hex digits (\[a-f\]\[A-F\]\[0-9\]), optionally prefixed by
      '0x', into an array of bytes. *)
let of_hex_string str =
  assert (String.length str mod 2 = 0) ;
  let str = String.lowercase_ascii str in
  (* Optionally discard 0x prefix *)
  let str = if String.starts_with ~prefix:"0x" str then String.sub str 2 (String.length str - 2) else str in
  init
    (String.length str / 2)
    (fun i -> Char.chr (int_of_string (Printf.sprintf "0x%c%c" str.[i * 2] str.[(i * 2) + 1])))

let reverse (bs : t) : t =
  let l = length bs in
  init l (fun i -> bs.[l - i - 1])
