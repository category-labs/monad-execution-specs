open Numeric
open Byte_string

module Nibbles = struct
  include Byte_string.Bytes
  open Stdlib

  let of_bytes (bs : t) =
    init
      (2 * length bs)
      (fun i ->
        let byte = Char.code bs.[i / 2] in
        if Stdlib.(i mod 2 = 0) then (* Upper nibble *)
          Char.unsafe_chr (Int.shift_right_logical byte 4)
        else (* Lower nibble *)
          Char.unsafe_chr (byte land 0xf) )

  let to_bytes (ns : t) =
    assert (length ns mod 2 = 0) ;
    init
      (length ns / 2)
      (fun i ->
        let upper_nibble = Char.code ns.[i * 2] in
        let lower_nibble = Char.code ns.[(i * 2) + 1] in
        Char.unsafe_chr Int.(shift_left upper_nibble 4 lor lower_nibble) )

  let prepend (nibble : Char.t) (ns : t) =
    assert (Char.code nibble < 16) ;
    init (length ns + 1) (function 0 -> nibble | i -> ns.[i - 1])

  let odd_mask = 0x10
  let flag_mask = 0x20

  (** [is_prefix_at_depth ~prefix key ~depth] checks whether [key\[depth..(depth + length prefix)) = prefix] *)
  let is_prefix_at_depth ~(prefix : t) (key : t) ~(depth : int) =
    Seq.(zip (to_seq prefix) (drop depth (to_seq key)))
    |> Seq.map (function p_i, k_i -> Stdlib.compare p_i k_i)
    |> Seq.find (( <> ) 0)
    |> function None -> true | Some _ -> false

  (** [hex_prefix_encode n flag] encodes a sequence of nibbles plus an extra flag into a sequence of bytes,
             following the definition of HP in YP (200) *)
  let hex_prefix_encode (ns : t) (flag : bool) : t =
    let odd = length ns mod 2 = 1 in
    let header =
      (if odd then odd_mask else 0x00)
      lor (if flag then flag_mask else 0x00)
      lor if odd then Char.code ns.[0] else 0x00
    in
    let shift = if odd then 1 else 0 in
    init
      ((length ns / 2) + 1)
      (function
        | 0 -> Char.unsafe_chr header
        | i ->
            let upper_nibble = Char.code ns.[((i - 1) * 2) + shift] in
            let lower_nibble = Char.code ns.[((i - 1) * 2) + 1 + shift] in
            Char.unsafe_chr Int.(shift_left upper_nibble 4 lor lower_nibble) )

  let hex_prefix_decode (bs : t) : t * bool =
    let header = Char.code bs.[0] in
    let odd = header land odd_mask <> 0 in
    let flag = header land flag_mask <> 0 in
    assert (header land 0xc0 = 0) ;
    if not odd then assert (header land 0x0f = 0) ;
    let shift = if odd then 1 else 0 in
    let ns =
      init
        (((length bs - 1) * 2) + shift)
        (fun i ->
          let byte = Char.code bs.[(i + 2 - shift) / 2] in
          if (i + shift) mod 2 = 0 then (* Upper nibble *)
            Char.unsafe_chr (Int.shift_right_logical byte 4)
          else (* Lower nibble *)
            Char.unsafe_chr (byte land 0x0f) )
    in
    (ns, flag)
end

module Node = struct
  type small_node_or_hash = Small of t | Hash of B32.t
  and t =
    | Empty
    | Branch of small_node_or_hash Iarray.t * Rlp.t
    | Leaf of {path : Nibbles.t; value : Rlp.t}
    | Extension of {path_segment : Nibbles.t; subtree : small_node_or_hash}

  let rec to_rlp = function
    | Empty -> Rlp.Bytes "" (* See YP (207) *)
    | Branch (branches, value) ->
        let branches = Iarray.to_seq branches |> Seq.map small_node_or_hash_to_rlp in
        Rlp.List (List.of_seq Seq.(append branches (singleton value)))
    | Leaf {path; value} -> Rlp.(List [Bytes (Nibbles.hex_prefix_encode path true); value])
    | Extension {path_segment; subtree} ->
        Rlp.(List [Bytes (Nibbles.hex_prefix_encode path_segment false); small_node_or_hash_to_rlp subtree])

  and small_node_or_hash_to_rlp = function
    | Small node ->
        let enc = to_rlp node in
        assert (Bytes.length (Rlp.encode enc) < 32) ;
        enc
    | Hash h -> Rlp.Bytes (B32.to_bytes h)

  let rec of_rlp = function
    | Rlp.Bytes bs when bs = "" -> Empty
    | Rlp.List [Bytes p; v] ->
        let ns, is_leaf = Nibbles.hex_prefix_decode p in
        if is_leaf then Leaf {path = ns; value = v}
        else Extension {path_segment = ns; subtree = small_node_or_hash_of_rlp v}
    | Rlp.List [b0; b1; b2; b3; b4; b5; b6; b7; b8; b9; b10; b11; b12; b13; b14; b15; v] ->
        Branch
          ( [| small_node_or_hash_of_rlp b0
             ; small_node_or_hash_of_rlp b1
             ; small_node_or_hash_of_rlp b2
             ; small_node_or_hash_of_rlp b3
             ; small_node_or_hash_of_rlp b4
             ; small_node_or_hash_of_rlp b5
             ; small_node_or_hash_of_rlp b6
             ; small_node_or_hash_of_rlp b7
             ; small_node_or_hash_of_rlp b8
             ; small_node_or_hash_of_rlp b9
             ; small_node_or_hash_of_rlp b10
             ; small_node_or_hash_of_rlp b11
             ; small_node_or_hash_of_rlp b12
             ; small_node_or_hash_of_rlp b13
             ; small_node_or_hash_of_rlp b14
             ; small_node_or_hash_of_rlp b15 |]
          , v )
    | _ -> assert false

  and small_node_or_hash_of_rlp = function
    | Rlp.Bytes bs when bs = "" -> Small Empty
    | Rlp.Bytes bs ->
        assert (Bytes.length bs = 32) ;
        Hash (B32.of_bytes_exn bs)
    | rlp -> Small (of_rlp rlp)
end

type t = {inv_hashes : Node.t B32.Map.t; root_hash : B32.t}

module M = struct
  include Monad.State (struct
    type t = Node.t B32.Map.t
  end)

  let hash (node : Node.t) : B32.t t =
    let hash = Crypto.keccak_256 (Rlp.encode (Node.to_rlp node)) in
    let$ () = update (B32.Map.add hash node) in
    return hash

  let to_small_node_or_hash (node : Node.t) : Node.small_node_or_hash t =
    let encoded = Rlp.encode (Node.to_rlp node) in
    if Bytes.length encoded < 32 then return (Node.Small node)
    else
      let hash = Crypto.keccak_256 encoded in
      let$ () = update (B32.Map.add hash node) in
      return (Node.Hash hash)
end
