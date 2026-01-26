(* TODO: fold back into MPT *)

open Byte_string

type t = {bytes : Bytes.t; start : int; length : int}
(* Both start and length count nibbles, not bytes. *)

let length (nibbles : t) = nibbles.length

let of_bytes (bytes : Bytes.t) = {bytes; start = 0; length = 2 * Bytes.length bytes}

let ( .$[] ) (nibbles : t) (i : int) =
  assert (i >= 0 && i < nibbles.length) ;
  let nibble_index = nibbles.start + i in
  let byte_index = nibble_index / 2 in
  let byte = Char.code nibbles.bytes.[byte_index] in
  (if nibble_index mod 2 = 0 then byte lsr 4 else byte) land 0xf

let to_bytes (ns : t) =
  Bytes.init
    ((ns.length / 2) + (ns.length mod 2))
    (fun i ->
      if i = ns.length / 2 && ns.length mod 2 = 1 then Char.unsafe_chr (ns.$[2 * i] lsl 4)
      else Char.unsafe_chr ((ns.$[2 * i] lsl 4) lor ns.$[(2 * i) + 1]) )

let to_yojson nibbles = Bytes.to_yojson (to_bytes nibbles)

let init length n_i =
  let parity = length mod 2 in
  let length_bytes = (length / 2) + parity in
  let b_i i =
    if i = length_bytes - 1 && parity = 1 then Char.unsafe_chr (n_i (i * 2) lsl 4)
    else Char.unsafe_chr ((n_i (i * 2) lsl 4) lor n_i ((i * 2) + 1))
  in
  let bytes = Bytes.init length_bytes b_i in
  {bytes; start = 0; length}

let concat (n_1 : t) (n_2 : t) =
  let l_1 = length n_1 in
  let l_2 = length n_2 in
  let n_i i = if i < l_1 then n_1.$[i] else n_2.$[i - l_1] in
  init (l_1 + l_2) n_i

let of_nibble_array (bytes : Bytes.t) = init (Bytes.length bytes) (fun i -> Char.code bytes.[i])

let char_table =
  Iarray.init 16 (fun i -> if i < 10 then Char.(chr (i + code '0')) else Char.(chr (i - 10 + code 'a')))

let to_hex_string nibbles = String.init (length nibbles) (fun i -> Iarray.get char_table nibbles.$[i])

let to_yojson (nibbles : t) : Yojson.Safe.t = `String (to_hex_string nibbles)

let prepend (nibble : int) (nibbles : t) =
  assert (nibble < 16) ;
  init (nibbles.length + 1) (fun i -> if i = 0 then nibble else nibbles.$[i - 1])

let of_nibble (nibble : int) =
  assert (nibble < 16) ;
  {bytes = Bytes.of_char (Char.unsafe_chr nibble); start = 1; length = 1}

let sub (nibbles : t) (start : int) (length : int) =
  assert (start >= 0) ;
  assert (length >= 0) ;
  assert (start + length <= nibbles.length) ;
  {bytes = nibbles.bytes; start = nibbles.start + start; length}

let hd (nibbles : t) = nibbles.$[0]
let tl (nibbles : t) = sub nibbles 1 (length nibbles - 1)
let uncons (nibbles : t) = if length nibbles > 0 then Some (hd nibbles, tl nibbles) else None

let split (nibbles : t) (i : int) = (sub nibbles 0 i, sub nibbles i (length nibbles - i))

let empty = {bytes = ""; start = 0; length = 0}

let odd_mask = 0x10
let flag_mask = 0x20

let to_seq (nibbles : t) : int Seq.t =
  Seq.ints 0 |> Seq.take nibbles.length |> Seq.map (fun i -> nibbles.$[i])

let rec compare (m : t) (n : t) =
  match (uncons m, uncons n) with
  | None, None -> 0
  | Some _, None -> 1
  | None, Some _ -> -1
  | Some (m_0, m), Some (n_0, n) ->
      let d = Int.compare m_0 n_0 in
      if d = 0 then compare m n else d

(** [is_prefix_at_depth ~prefix key ~depth] checks whether [key\[depth..(depth + length prefix)) = prefix] *)
let is_prefix_at_depth ~(prefix : t) (key : t) ~(depth : int) =
  Seq.(zip (to_seq prefix) (drop depth (to_seq key)))
  |> Seq.map (function p_i, k_i -> Stdlib.compare p_i k_i)
  |> Seq.find (( <> ) 0)
  |> function None -> true | Some _ -> false

(** [hex_prefix_encode n flag] encodes a sequence of nibbles plus an extra flag into a sequence of bytes,
             following the definition of HP in YP (200) *)
let hex_prefix_encode (nibbles : t) (flag : bool) : Bytes.t =
  let odd = length nibbles mod 2 = 1 in
  let header =
    (if odd then odd_mask else 0x00)
    lor (if flag then flag_mask else 0x00)
    lor if odd then nibbles.$[0] else 0x00
  in
  let shift = if odd then 1 else 0 in
  Bytes.init
    ((length nibbles / 2) + 1)
    (function
      | 0 -> Char.unsafe_chr header
      | i ->
          let upper_nibble = nibbles.$[((i - 1) * 2) + shift] in
          let lower_nibble = nibbles.$[((i - 1) * 2) + 1 + shift] in
          Char.unsafe_chr Int.((upper_nibble lsl 4) lor lower_nibble) )

let hex_prefix_decode (bytes : Bytes.t) : t * bool =
  let header = Char.code bytes.[0] in
  let odd = header land odd_mask <> 0 in
  let flag = header land flag_mask <> 0 in
  assert (header land 0xc0 = 0) ;
  if not odd then assert (header land 0x0f = 0) ;
  let shift = if odd then 1 else 0 in
  let ns =
    init
      (((Bytes.length bytes - 1) * 2) + shift)
      (fun i ->
        let byte = Char.code bytes.[(i + 2 - shift) / 2] in
        if (i + shift) mod 2 = 0 then (* Upper nibble *)
          byte lsr 4
        else (* Lower nibble *)
          byte land 0x0f )
  in
  (ns, flag)

include Comparable.Make (struct
  type nonrec t = t
  let compare = compare
end)
