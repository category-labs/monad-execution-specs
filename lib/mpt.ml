open Numeric

module Nibbles = struct
  include Bytes
  let of_bytes (bs : Bytes.t) =
    init
      (2 * Bytes.length bs)
      (fun i ->
        let byte = Char.code bs.[i / 2] in
        if i mod 2 = 0 then (* Upper nibble *)
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
  let hex_prefix_encode (ns : t) (flag : bool) : Bytes.t =
    let odd = length ns mod 2 = 1 in
    let header =
      (if odd then odd_mask else 0x00)
      lor (if flag then flag_mask else 0x00)
      lor if odd then Char.code ns.[0] else 0x00
    in
    let shift = if odd then 1 else 0 in
    Bytes.init
      ((length ns / 2) + 1)
      (function
        | 0 -> Char.unsafe_chr header
        | i ->
            let upper_nibble = Char.code ns.[((i - 1) * 2) + shift] in
            let lower_nibble = Char.code ns.[((i - 1) * 2) + 1 + shift] in
            Char.unsafe_chr Int.(shift_left upper_nibble 4 lor lower_nibble) )

  let hex_prefix_decode (bs : Bytes.t) : t * bool =
    let header = Char.code bs.[0] in
    let odd = header land odd_mask <> 0 in
    let flag = header land flag_mask <> 0 in
    assert (header land 0xc0 = 0) ;
    if not odd then assert (header land 0x0f = 0) ;
    let shift = if odd then 1 else 0 in
    let ns =
      init
        (((Bytes.length bs - 1) * 2) + shift)
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
  let branching_factor = Trie.branching_factor

  type t =
    | Empty
    | Branch of t Iarray.t * Rlp.t
    | Leaf of {path : Nibbles.t; value : Rlp.t}
    | Extension of {path_segment : Nibbles.t; subtree : t}

  let rec of_trie (t : Trie.t) =
    match t with
    | Empty -> Empty
    | Branch (branches, v) -> (
        let first_non_empty_nibble =
          Iarray.find_mapi
            (fun index branch -> if branch <> Trie.Empty then Some (index, branch) else None)
            branches
        in
        let non_empty_nibbles =
          Iarray.fold_left (fun n branch -> n + if branch <> Trie.Empty then 1 else 0) 0 branches
        in
        match (first_non_empty_nibble, non_empty_nibbles) with
        | Some (k_i, b), 1 -> (
          (* Exactly one non-empty branch: we can compress the entry *)
          match of_trie b with
          | Empty -> Empty
          | Branch (_, _) as bp ->
              Extension {path_segment = Nibbles.make 1 (Char.unsafe_chr k_i); subtree = bp}
          | Leaf {path; value} -> Leaf {path = Nibbles.prepend (Char.unsafe_chr k_i) path; value}
          | Extension {path_segment; subtree} ->
              Extension {path_segment = Nibbles.prepend (Char.unsafe_chr k_i) path_segment; subtree} )
        | None, 0 ->
            (* Terminal: we can compress the entry to a Leaf *)
            Leaf {path = Nibbles.empty; value = v}
        | _ -> Branch (Iarray.map of_trie branches, v) )

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
  type small_node_or_hash = Bytes.t (* At most 32 bytes, either a hash or a RLP-encoded node *)
  and t =
    | Empty
    | Branch of small_node_or_hash Iarray.t * Rlp.t
    | Leaf of {path : Nibbles.t; value : Rlp.t}
    | Extension of {path_segment : Nibbles.t; subtree : small_node_or_hash}

  let to_rlp = function
    | Empty -> Rlp.Bytes Bytes.empty (* See YP (207) *)
    | Branch (branches, value) ->
        let branches = Iarray.to_seq branches |> Seq.map (fun branch -> Rlp.Bytes branch) in
        Rlp.List (List.of_seq Seq.(append branches (singleton value)))
    | Leaf {path; value} -> Rlp.(List [Bytes (Nibbles.hex_prefix_encode path true); value])
    | Extension {path_segment; subtree} ->
        Rlp.(List [Bytes (Nibbles.hex_prefix_encode path_segment false); Bytes subtree])

  let of_rlp = function
    | Rlp.Bytes "" -> Empty
    | Rlp.List [Bytes p; v] -> (
        let ns, is_leaf = Nibbles.hex_prefix_decode p in
        if is_leaf then Leaf {path = ns; value = v}
        else match v with Bytes bs -> Extension {path_segment = ns; subtree = bs} | List _ -> assert false )
    | Rlp.List
        [ Bytes b0
        ; Bytes b1
        ; Bytes b2
        ; Bytes b3
        ; Bytes b4
        ; Bytes b5
        ; Bytes b6
        ; Bytes b7
        ; Bytes b8
        ; Bytes b9
        ; Bytes b10
        ; Bytes b11
        ; Bytes b12
        ; Bytes b13
        ; Bytes b14
        ; Bytes b15
        ; v ] ->
        Branch ([|b0; b1; b2; b3; b4; b5; b6; b7; b8; b9; b10; b11; b12; b13; b14; b15|], v)
    | _ -> assert false
end

type t = {inv_hashes : Node.t U256.Map.t; root_hash : U256.t}

module M = struct
  include Monad.State (struct
    type t = Node.t U256.Map.t
  end)
  let hash (node : Node.t) : U256.t t =
    let hash = Crypto.keccak_256 (Rlp.encode (Node.to_rlp node)) in
    let$ () = update (U256.Map.add hash node) in
    return hash

  let to_small_node_or_hash (node : Node.t) : Node.small_node_or_hash t =
    let encoded = Rlp.encode (Node.to_rlp node) in
    if Bytes.length encoded < 32 then return encoded else U256.to_bytes_be <$> hash node
end

(* Internal *)
let rec of_patricia trie =
  let open M in
  match trie with
  | PatriciaTrie.Empty -> return Node.Empty
  | Branch (branches, value) ->
      let$ branches =
        Iarray.to_seq branches
        |> Seq.map of_patricia
        |> Seq.mapM ~f:to_small_node_or_hash
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
      U256.Map.empty
  in
  {root_hash; inv_hashes}

(* Convenience function for testing *)
let make (entries : (Bytes.t * Rlp.t) list) =
  List.to_seq entries
  |> Seq.map (fun (k, v) -> (Nibbles.of_bytes k, v))
  |> Trie.of_seq
  |> PatriciaTrie.of_trie
  |> of_patricia

let find (k : Nibbles.t) {inv_hashes; root_hash} =
  let get_node (n : Node.small_node_or_hash) =
    if Bytes.length n < 32 then Node.of_rlp (Rlp.decode n) else U256.Map.find (U256.of_bytes_be n) inv_hashes
  in
  let rec loop depth = function
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
  loop 0 (U256.Map.find root_hash inv_hashes)
