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

module Trie = struct
  let branching_factor = 16

  type t = Empty | Branch of t Iarray.t * Rlp.t

  let rec insert (k : Nibbles.t) ?(depth = 0) (v : Rlp.t) = function
    | Branch (branches, _) when depth = Nibbles.length k -> Branch (branches, v)
    | Branch (branches, v') ->
        let k_i = Char.code k.[depth] in
        let branches =
          Iarray.mapi (fun i b -> if i = k_i then insert k ~depth:(depth + 1) v b else b) branches
        in
        Branch (branches, v')
    | Empty when depth = Nibbles.length k -> Branch (Iarray.init branching_factor (fun _ -> Empty), v)
    | Empty ->
        let k_i = Char.code k.[depth] in
        Branch
          ( Iarray.init branching_factor (fun i ->
                if i = k_i then insert k ~depth:(depth + 1) v Empty else Empty )
          , Rlp.Bytes Bytes.empty )

  let of_seq (entries : (Nibbles.t * Rlp.t) Seq.t) : t =
    Seq.fold_left (fun trie (k, v) -> insert k v trie) Empty entries

  let rec find (k : Nibbles.t) ?(depth = 0) (trie : t) =
    match trie with
    | Empty -> None
    | Branch (_branches, v) when depth = Nibbles.length k -> Some v
    | Branch (branches, _) ->
        let k_i = Char.code k.[depth] in
        find k ~depth:(depth + 1) (Iarray.get branches k_i)
end

module PatriciaTrie = struct
  type t =
    | Empty
    | Branch of t Iarray.t * Rlp.t
    | Leaf of {path : Nibbles.t; value : Rlp.t}
    | Extension of {path_segment : Nibbles.t; subtree : t}

  let rec of_trie (t : Trie.t) =
    match t with
    | Empty -> Empty
    | Branch (branches, v) -> (
        (* Patricialize sub-branches *)
        let branches = Iarray.map of_trie branches in
        let first_non_empty_nibble =
          Iarray.find_mapi
            (fun index branch -> if branch <> Empty then Some (index, branch) else None)
            branches
        in
        let non_empty_nibbles =
          Iarray.fold_left (fun n branch -> n + if branch <> Empty then 1 else 0) 0 branches
        in
        match (first_non_empty_nibble, non_empty_nibbles) with
        | Some (k_i, b), 1 when v = Bytes "" -> (
          (* Exactly one non-empty branch: we can compress the entry, but only if it didn't contain a value. *)
          match b with
          | Empty -> Empty
          | Branch (_, _) as bp ->
              Extension {path_segment = Nibbles.make 1 (Char.unsafe_chr k_i); subtree = bp}
          | Leaf {path; value} -> Leaf {path = Nibbles.prepend (Char.unsafe_chr k_i) path; value}
          | Extension {path_segment; subtree} ->
              Extension {path_segment = Nibbles.prepend (Char.unsafe_chr k_i) path_segment; subtree} )
        | None, 0 ->
            (* Terminal: we can compress the entry to a Leaf, or Empty if v = "" *)
            if v = Rlp.Bytes "" then Empty else Leaf {path = Nibbles.empty; value = v}
        | _ -> Branch (branches, v) )

  let rec find (k : Nibbles.t) ?(depth = 0) (trie : t) =
    match trie with
    | Empty -> None
    | Branch (_branches, v) when depth = Nibbles.length k -> Some v
    | Branch (branches, _) ->
        let k_i = Char.code k.[depth] in
        find k ~depth:(depth + 1) (Iarray.get branches k_i)
    | Leaf {path; value} ->
        if depth + Nibbles.length path <> Nibbles.length k then None
        else if Nibbles.is_prefix_at_depth ~prefix:path k ~depth then Some value
        else None
    | Extension {path_segment; subtree} ->
        if depth + Nibbles.length path_segment > Nibbles.length k then None
        else if Nibbles.is_prefix_at_depth ~prefix:path_segment k ~depth then
          find k ~depth:(depth + Nibbles.length path_segment) subtree
        else None
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

(* Internal *)
let rec of_patricia trie =
  let open M in
  match trie with
  | PatriciaTrie.Empty -> return Node.Empty
  | Branch (branches, value) ->
      let$ branches =
        Iarray.to_seq branches
        |> Seq.mapM ~f:(fun branch -> of_patricia branch >>= to_small_node_or_hash)
        |> M.fmap Iarray.of_seq
      in
      return (Node.Branch (branches, value))
  | Leaf {path; value} -> return (Node.Leaf {path; value})
  | Extension {path_segment; subtree} ->
      let$ subtree = of_patricia subtree in
      let$ subtree = to_small_node_or_hash subtree in
      return (Node.Extension {path_segment; subtree})

let of_patricia trie =
  let root_hash, inv_hashes =
    M.(
      let$ root = of_patricia trie in
      hash root )
      B32.Map.empty
  in
  {root_hash; inv_hashes}

(** {!of_seq seq} builds an MPT representing the mapping given by the key-value pairs in the input sequence. *)
let of_seq (entries : (Bytes.t * Bytes.t) Seq.t) =
  entries
  |> Seq.map (fun (k, v) -> (Nibbles.of_bytes k, Rlp.Bytes v))
  |> Trie.of_seq
  |> PatriciaTrie.of_trie
  |> of_patricia

(** {!of_seq_i seq} works as {!of_seq}, but it uses the position of every entry in the sequence as the key. *)
let of_seq_i (entries : Bytes.t Seq.t) =
  of_seq (Seq.mapi (fun i v -> (U64.(Repr.to_bytes (to_repr (of_int i))), v)) entries)

let find (k : Nibbles.t) {inv_hashes; root_hash} =
  let get_node = function Node.Small node -> node | Node.Hash h -> B32.Map.find h inv_hashes in
  let rec loop depth node =
    match node with
    | Node.Empty -> None
    | Branch (_branches, v) when depth = Nibbles.length k -> Some v
    | Branch (branches, _) ->
        let k_i = Char.code k.[depth] in
        loop (depth + 1) (get_node (Iarray.get branches k_i))
    | Leaf {path; value} ->
        if depth + Nibbles.length path <> Nibbles.length k then None
        else if Nibbles.is_prefix_at_depth ~prefix:path k ~depth then Some value
        else None
    | Extension {path_segment; subtree} ->
        if depth + Nibbles.length path_segment > Nibbles.length k then None
        else if Nibbles.is_prefix_at_depth ~prefix:path_segment k ~depth then
          loop (depth + Nibbles.length path_segment) (get_node subtree)
        else None
  in
  loop 0 (B32.Map.find root_hash inv_hashes)
