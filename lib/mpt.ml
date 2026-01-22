open Numeric
open Byte_string

module Nibbles = struct
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

  let init length n_i =
    let parity = length mod 2 in
    let length_bytes = (length / 2) + parity in
    let b_i i =
      if i = length_bytes - 1 && parity = 1 then Char.unsafe_chr (n_i (i * 2) lsl 4)
      else Char.unsafe_chr ((n_i (i * 2) lsl 4) lor n_i ((i * 2) + 1))
    in
    let bytes = Bytes.init length_bytes b_i in
    {bytes; start = 0; length}

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
end

module Iarray = struct
  include Stdlib.Iarray
  let to_yojson elt_to_yojson arr = `List (List.map elt_to_yojson (to_list arr))
end

module Trie = struct
  let branching_factor = 16

  type t = Empty | Branch of t Iarray.t * Rlp.t

  let rec insert (k : Nibbles.t) ?(depth = 0) (v : Rlp.t) = function
    | Branch (branches, _) when depth = Nibbles.length k -> Branch (branches, v)
    | Branch (branches, v') ->
        let k_i = Nibbles.(k.$[depth]) in
        let branches =
          Iarray.mapi (fun i b -> if i = k_i then insert k ~depth:(depth + 1) v b else b) branches
        in
        Branch (branches, v')
    | Empty when depth = Nibbles.length k -> Branch (Iarray.init branching_factor (fun _ -> Empty), v)
    | Empty ->
        let k_i = Nibbles.(k.$[depth]) in
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
        let k_i = Nibbles.(k.$[depth]) in
        find k ~depth:(depth + 1) (Iarray.get branches k_i)
end

module PatriciaTrie = struct
  let branching_factor = 16

  type t = Empty | Branch of (t Iarray.t * Rlp.t) | Extension of {path : Nibbles.t; ending : ending}
  [@@deriving to_yojson]
  and ending = Subtree of t | Value of Rlp.t [@@deriving to_yojson]

  let dump t = Format.eprintf "%s\n" (Yojson.Safe.pretty_to_string (to_yojson t))

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
          | Branch (_, _) as bp -> Extension {path = Nibbles.of_nibble k_i; ending = Subtree bp}
          | Extension {path; ending = Value value} ->
              Extension {path = Nibbles.prepend k_i path; ending = Value value}
          | Extension {path; ending = Subtree subtree} ->
              Extension {path = Nibbles.prepend k_i path; ending = Subtree subtree} )
        | None, 0 ->
            (* Terminal: we can compress the entry to a Leaf, or Empty if v = "" *)
            if v = Rlp.Bytes "" then Empty else Extension {path = Nibbles.empty; ending = Value v}
        | _ -> Branch (branches, v) )

  let rec find (k : Nibbles.t) ?(depth = 0) (trie : t) =
    match trie with
    | Empty -> None
    | Branch (_branches, v) when depth = Nibbles.length k -> Some v
    | Branch (branches, _) ->
        let k_i = Nibbles.(k.$[depth]) in
        find k ~depth:(depth + 1) (Iarray.get branches k_i)
    | Extension {path; ending = Value value} ->
        if depth + Nibbles.length path <> Nibbles.length k then None
        else if Nibbles.is_prefix_at_depth ~prefix:path k ~depth then Some value
        else None
    | Extension {path; ending = Subtree subtree} ->
        if depth + Nibbles.length path > Nibbles.length k then None
        else if Nibbles.is_prefix_at_depth ~prefix:path k ~depth then
          find k ~depth:(depth + Nibbles.length path) subtree
        else None

  let common_prefix (path : Nibbles.t) (key : Nibbles.t) : int =
    Seq.zip (Nibbles.to_seq path) (Nibbles.to_seq key)
    |> Seq.take_while (fun (n_p, n_k) -> n_p = n_k)
    |> Seq.length

  let one_branch (k_0, trie_0) = Iarray.init branching_factor (fun i -> if i = k_0 then trie_0 else Empty)
  let two_branches (k_0, trie_0) (k_1, trie_1) =
    Iarray.init branching_factor (fun i -> if i = k_0 then trie_0 else if i = k_1 then trie_1 else Empty)

  let extension ~path ~ending =
    match ending with
    | Subtree subtree when Nibbles.length path = 0 -> subtree
    | _ -> Extension {path; ending}

  let rec graft_disjoint (path, ending) (key, value) =
    match (Nibbles.uncons path, Nibbles.uncons key, ending) with
    | None, None, Value _ -> Value value
    | None, None, Subtree subtree -> Subtree (insert subtree key value)
    | Some (p_0, path), None, _ -> Subtree (Branch (one_branch (p_0, extension ~path ~ending), value))
    | None, Some (k_0, key'), Value v ->
        Subtree (Branch (one_branch (k_0, extension ~path:key' ~ending:(Value value)), v))
    | None, Some (k_0, key'), Subtree subtree -> Subtree (insert subtree key value)
    | Some (p_0, path), Some (k_0, key), _ ->
        assert (p_0 <> k_0) ;
        Subtree
          (Branch
             ( two_branches (p_0, extension ~path ~ending) (k_0, extension ~path:key ~ending:(Value value))
             , Rlp.Bytes "" ) )

  and insert (trie : t) key value =
    assert (value <> Rlp.Bytes "") ;
    match trie with
    | Empty -> extension ~path:key ~ending:(Value value)
    | Extension {path; ending} ->
        let i = common_prefix path key in
        let p_0, p_1 = Nibbles.split path i in
        let _, k_1 = Nibbles.split key i in
        let ending = graft_disjoint (p_1, ending) (k_1, value) in
        if Nibbles.length p_0 = 0 then
          match ending with
          | Subtree subtree -> subtree
          | Value _ ->
              (* This can only happen if p_0 = p_1 = k_0 = k_1 = "". *)
              Extension {path = key; ending = Value value}
        else extension ~path:p_0 ~ending:ending
    | Branch (branches, branch_value) -> (
      match Nibbles.uncons key with
      | None -> Branch (branches, value)
      | Some (k_0, key) ->
          let branches =
            Iarray.mapi (fun i branch -> if i = k_0 then insert branch key value else branch) branches
          in
          Branch (branches, branch_value) )

  let of_seq entries = Seq.fold_left (fun trie (k, v) -> insert trie k v) Empty entries

  let rec ( = ) l r =
    match (l, r) with
    | Empty, Empty -> true
    | Extension e_l, Extension e_r -> Nibbles.(e_l.path = e_r.path) && ending_equal e_l.ending e_r.ending
    | Branch (b_l, v_l), Branch (b_r, v_r) -> Iarray.equal ( = ) b_l b_r && Stdlib.(v_l = v_r)
    | _ -> false

  and ending_equal l r =
    match (l, r) with Value l, Value r -> Stdlib.(l = r) | Subtree l, Subtree r -> l = r | _ -> false
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
  | Extension {path; ending = Value value} -> return (Node.Leaf {path; value})
  | Extension {path; ending = Subtree subtree} ->
      let$ subtree = of_patricia subtree in
      let$ subtree = to_small_node_or_hash subtree in
      return (Node.Extension {path_segment = path; subtree})

let of_patricia trie =
  let root_hash, inv_hashes =
    M.(
      run
        (let$ root = of_patricia trie in
         hash root ) )
      B32.Map.empty
  in
  {root_hash; inv_hashes}

(** {!of_seq} builds an MPT representing the mapping given by the key-value pairs in the input sequence. *)
let of_seq (entries : (Bytes.t * Bytes.t) Seq.t) =
  entries |> Seq.map (fun (k, v) -> (Nibbles.of_bytes k, Rlp.Bytes v)) |> PatriciaTrie.of_seq |> of_patricia

let of_seq_via_trie (entries : (Bytes.t * Bytes.t) Seq.t) =
  entries |> Seq.map (fun (k, v) -> (Nibbles.of_bytes k, Rlp.Bytes v)) |> Trie.of_seq |> PatriciaTrie.of_trie |> of_patricia

let empty = of_seq Seq.empty

(** {!of_seq_i} works as {!of_seq}, but it uses the RLP encoding of the position of every entry in the
    sequence as the key. This implements the encoding scheme described in YP (36), YP (37) and YP (38). *)
let of_seq_i (entries : Bytes.t Seq.t) =
  let to_kv i v = (Rlp.encode U64.(to_rlp ~$i), v) in
  of_seq (Seq.mapi to_kv entries)

let find (k : Nibbles.t) {inv_hashes; root_hash} =
  let get_node = function Node.Small node -> node | Node.Hash h -> B32.Map.find h inv_hashes in
  let rec loop depth node =
    match node with
    | Node.Empty -> None
    | Branch (_branches, v) when depth = Nibbles.length k -> Some v
    | Branch (branches, _) ->
        let k_i = Nibbles.(k.$[depth]) in
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
