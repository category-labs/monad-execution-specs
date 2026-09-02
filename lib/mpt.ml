(** Merkle Patricia tries, used in the calculation of state roots.

    The current implementation does not maintain MPTs incrementally but instead stores all state as standard
    maps, which are converted into MPTs only at the end of a block's execution, when their state roots are
    required.

    Construction of MPTs is done in stages, by constructing a regular trie first, then a Patricialized version
    of it and finally Merkleizing it to an MPT. *)

open Numeric
open Byte_string

module Iarray = struct
  include Stdlib.Iarray
  let to_yojson elt_to_yojson arr = `List (List.map elt_to_yojson (to_list arr))
end

(** Nibble sequences backed by byte arrays, offering constant-time subsequence extraction. *)
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

  let ( ^ ) (n_1 : t) (n_2 : t) =
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
            Char.unsafe_chr ((upper_nibble lsl 4) lor lower_nibble) )

  (** [hex_prefix_decode bs] decodes a sequence of bytes following the definition of HP in YP (200). *)
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

(** Lazily-Merkleized Patricia tries, mapping byte strings to ['a].
    The API is a subset of the OCaml Stdlib map signature [Map.S]. *)
module Generic = struct
  let branching_factor = 16

  type merkleization = Small of Bytes.t | Hash of B32.t [@@deriving to_yojson]
  type 'a impl =
    | Empty
    | Branch of ('a t Iarray.t * 'a option)
    | Extension of {path : Nibbles.t; ending : 'a ending}
  [@@deriving to_yojson]
  and 'a ending = Subtree of 'a t | Value of 'a [@@deriving to_yojson]

  (* We would like to encode whether a node has been merkleized or not with a phantom type.
     But it doesn't seem to be possible to do this in an ergonomic way: we need subtyping
     (so that a merkleized subtree can be included in a non-merkleized tree without
     reconstructing it) but GADTs must be invariant. *)
  and 'a t = {data : 'a impl; merkleized : merkleization option} [@@deriving to_yojson]

  let empty = {data = Empty; merkleized = Some (Small (Rlp.encode_bytes ""))}

  let make (type a) (data : a impl) = {data; merkleized = None}

  let rec find_opt (k : Nibbles.t) ~(depth : int) (trie : 'a t) : 'a option =
    match trie.data with
    | Empty -> None
    | Branch (_branches, v) when depth = Nibbles.length k -> v
    | Branch (branches, _) ->
        let k_i = Nibbles.(k.$[depth]) in
        find_opt k ~depth:(depth + 1) (Iarray.get branches k_i)
    | Extension {path; ending = Value value} ->
        if depth + Nibbles.length path <> Nibbles.length k then None
        else if Nibbles.is_prefix_at_depth ~prefix:path k ~depth then Some value
        else None
    | Extension {path; ending = Subtree subtree} ->
        if depth + Nibbles.length path > Nibbles.length k then None
        else if Nibbles.is_prefix_at_depth ~prefix:path k ~depth then
          find_opt k ~depth:(depth + Nibbles.length path) subtree
        else None

  let find_opt (k : Bytes.t) (trie : 'a t) : 'a option = find_opt (Nibbles.of_bytes k) ~depth:0 trie

  let common_prefix (path : Nibbles.t) (key : Nibbles.t) : int =
    Seq.zip (Nibbles.to_seq path) (Nibbles.to_seq key)
    |> Seq.take_while (fun (n_p, n_k) -> n_p = n_k)
    |> Seq.length

  let one_branch (k_0, trie_0) : 'a t Iarray.t =
    Iarray.init branching_factor (fun i -> if i = k_0 then trie_0 else empty)
  let two_branches (k_0, trie_0) (k_1, trie_1) : 'a t Iarray.t =
    Iarray.init branching_factor (fun i -> if i = k_0 then trie_0 else if i = k_1 then trie_1 else empty)

  (* Smart constructors that compact the tree as they go. *)
  let extension ~path ~ending =
    match ending with
    | Subtree {data = Empty; _} ->
        (* Extension followed by empty; rewrite to empty. *)
        empty
    | Subtree {data = Extension {path = path'; ending}; _} ->
        (* Extension followed by extension; rewrite to single extension. *)
        make (Extension {path = Nibbles.(path ^ path'); ending})
    | Subtree subtree when Nibbles.length path = 0 ->
        (* Extension with empty path; rewrite to ending. *)
        subtree
    | _ ->
        (* No compression; leave as Extension node. *)
        make (Extension {path; ending})

  let branch ~branches ~value =
    let non_empty_branches =
      Iarray.to_seq branches
      |> Seq.mapi (fun index branch -> (index, branch))
      |> Seq.filter (fun (_index, branch) -> branch.data <> Empty)
    in
    match value with
    | Some value when Seq.is_empty non_empty_branches ->
        (* Leaf value but no branches; rewrite to extension. *)
        extension ~path:Nibbles.empty ~ending:(Value value)
    | Some _ ->
        (* Leaf value and branches; leave as Branch node. *)
        make (Branch (branches, value))
    | None -> (
      (* No leaf value. Rewrite zero-branch case to empty, one-branch case to extension. *)
      match Seq.uncons non_empty_branches with
      | None -> empty
      | Some ((ki, bi), bs) when Seq.is_empty bs -> extension ~path:(Nibbles.of_nibble ki) ~ending:(Subtree bi)
      | Some _ -> make (Branch (branches, value)) )

  (* Note that we do not optimize very hard for the case where the key is not present. Every node touched will
   be assumed to be dirtied, even if the resulting trie is identical to the original one. *)
  let rec remove key (trie : 'a t) =
    match trie.data with
    | Empty -> empty
    | Extension {path; ending = Value _v} -> if Nibbles.(path = key) then empty else trie
    | Extension {path; ending = Subtree subtree} ->
        let i = common_prefix path key in
        if i <> Nibbles.length path then trie
        else
          let _, key = Nibbles.split key i in
          let subtree = remove key subtree in
          extension ~path ~ending:(Subtree subtree)
    | Branch (branches, value) -> (
      match Nibbles.uncons key with
      | None -> branch ~branches ~value:None
      | Some (k_0, key) ->
          let branches = Iarray.mapi (fun k_i trie -> if k_0 = k_i then remove key trie else trie) branches in
          branch ~branches ~value )

  let rec graft_disjoint (path, ending) (key, value) : 'a ending =
    match (Nibbles.uncons path, Nibbles.uncons key, ending) with
    | None, None, Value _ -> Value value
    | None, None, Subtree subtree -> Subtree (add key value subtree)
    | Some (p_0, path), None, _ ->
        Subtree (make (Branch (one_branch (p_0, extension ~path ~ending), Some value)))
    | None, Some (k_0, key'), Value v ->
        Subtree (make (Branch (one_branch (k_0, extension ~path:key' ~ending:(Value value)), Some v)))
    | None, Some (_k_0, _key'), Subtree subtree -> Subtree (add key value subtree)
    | Some (p_0, path), Some (k_0, key), _ ->
        assert (p_0 <> k_0) ;
        let branches =
          two_branches (p_0, extension ~path ~ending) (k_0, extension ~path:key ~ending:(Value value))
        in
        Subtree (make (Branch (branches, None)))

  and add (key : Nibbles.t) (value : 'a) (trie : 'a t) : 'a t =
    match trie.data with
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
              extension ~path:key ~ending:(Value value)
        else extension ~path:p_0 ~ending
    | Branch (branches, branch_value) -> (
      match Nibbles.uncons key with
      | None -> make (Branch (branches, Some value))
      | Some (k_0, key) ->
          let branches =
            Iarray.mapi (fun i branch -> if i = k_0 then add key value branch else branch) branches
          in
          make (Branch (branches, branch_value)) )

  let add (key : Bytes.t) (value : 'a) (trie : 'a t) = add (Nibbles.of_bytes key) value trie

  let remove key trie = remove (Nibbles.of_bytes key) trie

  let of_seq (entries : (Bytes.t * 'a) Seq.t) : 'a t =
    entries |> Seq.fold_left (fun trie (k, v) -> add k v trie) empty

  let of_seq_i (entries : 'a Seq.t) =
    let to_kv i v = (Rlp.encode U64.(to_rlp ~$i), v) in
    of_seq (Seq.mapi to_kv entries)

  let of_map (map : 'a Bytes.Map.t) = of_seq (Bytes.Map.to_seq map)

  let rec to_seq ~(prefix : Nibbles.t) (trie : 'a t) : (Bytes.t * 'a) Seq.t =
    match trie.data with
    | Empty -> Seq.empty
    | Branch (branches, value) -> (
        let branches =
          Iarray.to_seq branches
          |> Seq.mapi (fun k_i branch ->
              let prefix = Nibbles.(prefix ^ of_nibble k_i) in
              to_seq ~prefix branch )
          |> Seq.concat
        in
        match value with None -> branches | Some value -> Seq.cons (Nibbles.to_bytes prefix, value) branches )
    | Extension {path; ending = Value v} ->
        let key = Nibbles.(to_bytes (prefix ^ path)) in
        Seq.singleton (key, v)
    | Extension {path; ending = Subtree st} ->
        let prefix = Nibbles.(prefix ^ path) in
        to_seq ~prefix st

  let to_seq (trie : 'a t) : (Bytes.t * 'a) Seq.t = to_seq ~prefix:Nibbles.empty trie

  let rec equal elt_equal l r =
    match (l, r) with
    | {merkleized = Some (Hash h_l); _}, {merkleized = Some (Hash h_r); _} -> B32.(h_l = h_r)
    | {merkleized = Some (Small s_l); _}, {merkleized = Some (Small s_r); _} -> Bytes.(s_l = s_r)
    | {merkleized = Some _; _}, {merkleized = Some _; _} -> false
    | {data = Empty; _}, {data = Empty; _} -> true
    | {data = Extension e_l; _}, {data = Extension e_r; _} ->
        Nibbles.(e_l.path = e_r.path) && ending_equal elt_equal e_l.ending e_r.ending
    | {data = Branch (b_l, v_l); _}, {data = Branch (b_r, v_r); _} ->
        Iarray.equal (equal elt_equal) b_l b_r && Option.equal elt_equal v_l v_r
    | _ -> false

  and ending_equal elt_equal l r =
    match (l, r) with
    | Value l, Value r -> elt_equal l r
    | Subtree l, Subtree r -> equal elt_equal l r
    | _ -> false

  let merkleization_to_rlp_encoded = function Hash h -> Rlp.encode_bytes (B32.to_bytes h) | Small s -> s

  (** [merkleization trie] returns the Merkleization of [trie], provided it was already Merkleized
      by a call to {!val-merkleized}. Otherwise, it raises an exception. *)
  let merkleization (node : 'a t) =
    match node.merkleized with
    | Some merkleized -> merkleized
    | None -> raise (Invalid_argument "Trying to take Merkle root of unmerkleized tree")

  (** [merkleized ~value_to_bytes trie] returns a Merkleized version of [trie], which may be equal to
      the original if this was already Merkleized. *)
  let rec merkleized ~(value_to_bytes : 'a -> Bytes.t) (node : 'a t) : 'a t =
    match node with
    | {merkleized = Some _; _} -> node
    | _ ->
        let data, encoded =
          match node.data with
          | Empty -> (Empty, Rlp.(encode_bytes ""))
          | Branch (branches, value) ->
              let branches = Iarray.map (merkleized ~value_to_bytes) branches in
              let merkleizations = Iarray.to_seq branches |> Seq.map merkleization in
              (Branch (branches, value), branch_to_rlp_encoded ~value_to_bytes merkleizations value)
          | Extension {path; ending} ->
              let ending =
                match ending with
                | Value value -> Value value
                | Subtree subtree -> Subtree (merkleized ~value_to_bytes subtree)
              in
              (Extension {path; ending}, extension_to_rlp_encoded ~value_to_bytes path ending)
        in
        let merkleized =
          if Bytes.length encoded < 32 then Small encoded else Hash (Crypto.keccak_256 encoded)
        in
        {data; merkleized = Some merkleized}

  and branch_to_rlp_encoded ~value_to_bytes (branches : merkleization Seq.t) (value : 'a option) : Bytes.t =
    let encoded_branches = Seq.map merkleization_to_rlp_encoded branches in
    let encoded_value = Rlp.encode_bytes (match value with None -> "" | Some v -> value_to_bytes v) in
    let encoded_fields = Seq.(append encoded_branches (singleton encoded_value)) in
    Rlp.encode_list (List.of_seq encoded_fields)

  and extension_to_rlp_encoded ~value_to_bytes (path : Nibbles.t) (ending : 'a ending) =
    match ending with
    | Value value ->
        let encoded_path = Rlp.encode_bytes (Nibbles.hex_prefix_encode path true) in
        let encoded_ending = Rlp.encode_bytes (value_to_bytes value) in
        Rlp.encode_list [encoded_path; encoded_ending]
    | Subtree subtree ->
        let encoded_path = Rlp.encode_bytes (Nibbles.hex_prefix_encode path false) in
        let encoded_ending = merkleization_to_rlp_encoded (merkleization subtree) in
        Rlp.encode_list [encoded_path; encoded_ending]

  (** [merkle_root trie] returns the Merkle root of [trie], provided it was already Merkleized
      by a call to [merkleized trie]. Otherwise, it raises an exception. *)
  let merkle_root (trie : 'a t) =
    match merkleization trie with Small encoded -> Crypto.keccak_256 encoded | Hash hash -> hash

  let update (k : Bytes.t) (update_fn : 'v option -> 'v option) trie =
    let entry = find_opt k trie in
    match update_fn entry with None -> remove k trie | Some v -> add k v trie

  let at (k : Bytes.t) : ('v t, 'v option) Lens.t =
    {get = (fun m -> find_opt k m); set = (fun v m -> update k (fun _ -> v) m)}
end

(** Maps from arbitrary keys [Key.t] to values [Value.t] backed by a lazily-merkleized Merkle-Patricia trie.
    The type [Make(P)(K)(V).t] is meant to efficiently represent storage and state tries by:
    1. Replicating the data in the MPT as a standard OCaml map for efficient access without e.g. re-encrypting
        the keys.
    2. Caching updates in an intermediate map of "dirty" keys which gets batch-merkleized once per block. *)
module Make (Params : sig
  val hash_keys : bool
end) (Key : sig
  include Map.OrderedType
  val to_bytes : t -> Bytes.t
end) (Value : sig
  type t

  val equal : t -> t -> bool

  val commit : t -> t
  (** {!commit} specifies an update to be applied to the value type when a value is committed from the dirty
      set into the clean set. In practice, this is useful when [t] is [Account.t], to Merkleize the account
      storage trie only when the account itself is committed into the clean set. *)

  val to_bytes : t -> Bytes.t
end) =
struct
  module Key = struct
    include Key
    module Map = Map.Make (Key)
  end

  type t = {mpt : Value.t Generic.t; clean : (Bytes.t * Value.t) Key.Map.t; dirty : Value.t option Key.Map.t}

  type merkleization = Generic.merkleization

  let empty : t = {mpt = Generic.empty; clean = Key.Map.empty; dirty = Key.Map.empty}

  let hash_key =
    if Params.hash_keys then fun (k : Key.t) -> B32.to_bytes (Crypto.keccak_256 (Key.to_bytes k))
    else fun (k : Key.t) -> Key.to_bytes k

  let find_opt (k : Key.t) (trie : t) : Value.t option =
    match Key.Map.find_opt k trie.dirty with
    | Some None -> None
    | Some (Some value) -> Some value
    | None -> Option.map snd (Key.Map.find_opt k trie.clean)

  let add (k : Key.t) (v : Value.t) (trie : t) : t =
    let dirty =
      match Key.Map.find_opt k trie.clean with
      | Some (_, v_old) when Value.equal v v_old -> Key.Map.remove k trie.dirty
      | _ -> Key.Map.add k (Some v) trie.dirty
    in
    {trie with dirty}

  let remove (k : Key.t) (trie : t) : t =
    let dirty =
      match Key.Map.find_opt k trie.clean with
      | None -> Key.Map.remove k trie.dirty
      | Some _ -> Key.Map.add k None trie.dirty
    in
    {trie with dirty}

  let add_seq (seq : (Key.t * Value.t) Seq.t) (trie : t) =
    Seq.fold_left (fun trie (k, v) -> add k v trie) trie seq
  let of_seq (seq : (Key.t * Value.t) Seq.t) : t = Seq.fold_left (fun trie (k, v) -> add k v trie) empty seq

  let to_seq (trie : t) : (Key.t * Value.t) Seq.t =
    let not_removed = function k, Some v -> Some (k, v) | _, None -> None in
    let dirty_entries : (Key.t * Value.t) Seq.t = Seq.filter_map not_removed (Key.Map.to_seq trie.dirty) in
    let clean_entries : (Key.t * Value.t) Seq.t =
      let not_dirty (k, (_, _)) = Option.is_none (Key.Map.find_opt k trie.dirty) in
      Seq.filter not_dirty (Key.Map.to_seq trie.clean) |> Seq.map (fun (k, (_kh, v)) -> (k, v))
    in
    (* Map.to_seq returns entries sorted by key, so we should do the same here. *)
    let rec merge_sort s1 s2 =
      match (Seq.uncons s1, Seq.uncons s2) with
      | Some ((k1, v1), s1'), Some ((k2, v2), s2') ->
          if Key.compare k1 k2 <= 0 then Seq.cons (k1, v1) (fun () -> merge_sort s1' s2 ())
          else Seq.cons (k2, v2) (fun () -> merge_sort s1 s2' ())
      | None, _ -> s2
      | _, None -> s1
    in
    merge_sort dirty_entries clean_entries

  let keys (trie : t) = Seq.map fst (to_seq trie)

  (** [merkle_root trie_map] returns the Merkle root of [trie_map], provided it was already Merkleized
      by a call to [merkleized trie_map]. Otherwise, it raises an exception. *)
  let merkle_root {mpt; dirty; _} =
    assert (Key.Map.is_empty dirty) ;
    Generic.merkle_root mpt

  let dirty_to_yojson value_to_yojson (map : Value.t option Key.Map.t) : Yojson.Safe.t =
    Key.Map.to_seq map
    |> Seq.map (fun (k, v) ->
        (Bytes.to_hex_string (Key.to_bytes k), match v with None -> `Null | Some v -> value_to_yojson v) )
    |> List.of_seq
    |> fun entries -> `Assoc entries

  let clean_to_yojson value_to_yojson (map : (Bytes.t * Value.t) Key.Map.t) : Yojson.Safe.t =
    Key.Map.to_seq map
    |> Seq.map (fun (k, (_, v)) -> (Bytes.to_hex_string (Key.to_bytes k), value_to_yojson v))
    |> List.of_seq
    |> fun entries -> `Assoc entries

  let to_yojson_debug value_to_yojson {mpt; clean; dirty} =
    `Assoc
      [ ("mpt", Generic.to_yojson value_to_yojson mpt)
      ; ("clean", clean_to_yojson value_to_yojson clean)
      ; ("dirty", dirty_to_yojson value_to_yojson dirty) ]

  (** [merkleized trie_map] returns a version of [trie_map] with all dirty updates committed to the
      clean entry set and the MPT back-end, which is also Merkleized. *)
  let merkleized {mpt; clean; dirty} =
    let mpt, clean =
      Key.Map.to_seq dirty
      |> Seq.fold_left
           (fun (mpt, clean) (k, entry) ->
             let kh = match Key.Map.find_opt k clean with None -> hash_key k | Some (kh, _) -> kh in
             match entry with
             | None -> (Generic.remove kh mpt, Key.Map.remove k clean)
             | Some v ->
                 let v = Value.commit v in
                 (Generic.add kh v mpt, Key.Map.add k (kh, v) clean) )
           (mpt, clean)
    in
    let mpt = Generic.merkleized ~value_to_bytes:Value.to_bytes mpt in
    let dirty = Key.Map.empty in
    {mpt; clean; dirty}

  let contains_all (l : t) (r : t) =
    to_seq r
    |> Seq.for_all (fun (k, v_r) ->
        match find_opt k l with Some v_l -> Value.(equal v_l v_r) | None -> false )

  let equal (l : t) (r : t) =
    if Key.Map.is_empty l.dirty && Key.Map.is_empty r.dirty then l.mpt.merkleized = r.mpt.merkleized
    else contains_all l r && contains_all r l

  let of_yojson
      (key_of_string : String.t -> (Key.t, string) result)
      (value_of_yojson : Yojson.Safe.t -> (Value.t, string) result) : Yojson.Safe.t -> (t, string) result =
    function
    | `Assoc fields ->
        Result.(
          let$ entries =
            List.mapM fields ~f:(fun (k, v) ->
                let$ k = key_of_string k in
                let$ v = value_of_yojson v in
                return (k, v) )
          in
          return (of_seq (List.to_seq entries)) )
    | _ -> Error "Mpt.t"

  let to_yojson (value_to_yojson : Value.t -> Yojson.Safe.t) (trie : t) : Yojson.Safe.t =
    let fields =
      to_seq trie
      |> Seq.map (fun (k, v) ->
          let k = Bytes.to_hex_string (Key.to_bytes k) in
          let v = value_to_yojson v in
          (k, v) )
      |> List.of_seq
    in
    `Assoc fields

  let at (k : Key.t) : (t, Value.t option) Lens.t =
    let get m = find_opt k m in
    let set v m = match v with None -> remove k m | Some v -> add k v m in
    Lens.{get; set}
end
