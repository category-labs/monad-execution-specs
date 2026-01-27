open Numeric
open Byte_string

module Iarray = struct
  include Stdlib.Iarray
  let to_yojson elt_to_yojson arr = `List (List.map elt_to_yojson (to_list arr))
end

(** Generic maps from byte strings to ['a] backed by a lazily-merkleized Merkle-Patricia trie. *)
module Generic = struct
  let branching_factor = 16

  type merkleization = Small of Bytes.t | Hash of B32.t [@@deriving to_yojson]
  type 'a impl =
    | Empty
    | Branch of ('a t Iarray.t * 'a option)
    | Extension of {path : Nibbles.t; ending : 'a ending}
  [@@deriving to_yojson]
  and 'a ending = Subtree of 'a t | Value of 'a [@@deriving to_yojson]

  and 'a t = {data : 'a impl; merkleized : merkleization option} [@@deriving to_yojson]

  let empty_hash = Crypto.keccak_256 (Rlp.encode (Rlp.Bytes ""))
  let empty = {data = Empty; merkleized = Some (Small (Rlp.encode_bytes ""))}

  let make (type a) (data : a impl) = {data; merkleized = None}

  let rec find_opt (k : Nibbles.t) ?(depth = 0) (trie : 'a t) : 'a option =
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

  let find_opt (k : Bytes.t) (trie : 'a t) : 'a option = find_opt (Nibbles.of_bytes k) trie

  let common_prefix (path : Nibbles.t) (key : Nibbles.t) : int =
    Seq.zip (Nibbles.to_seq path) (Nibbles.to_seq key)
    |> Seq.take_while (fun (n_p, n_k) -> n_p = n_k)
    |> Seq.length

  let one_branch (k_0, trie_0) : 'a t Iarray.t =
    Iarray.init branching_factor (fun i -> if i = k_0 then trie_0 else empty)
  let two_branches (k_0, trie_0) (k_1, trie_1) : 'a t Iarray.t =
    Iarray.init branching_factor (fun i -> if i = k_0 then trie_0 else if i = k_1 then trie_1 else empty)

  let extension ~path ~ending =
    match ending with
    | Subtree subtree when Nibbles.length path = 0 -> subtree
    | _ -> make (Extension {path; ending})

  (* Note that we do not optimize very hard for the case where the key is not present. Every node touched will
   be assumed to be dirtied, even if the resulting trie is identical to the original one. *)
  let rec remove key (trie : 'a t) =
    match trie.data with
    | Empty -> empty
    | Extension {path; ending = Value v} ->
        let i = common_prefix path key in
        if i <> Nibbles.length path then trie else empty
    | Extension {path; ending = Subtree subtree} ->
        let i = common_prefix path key in
        if i <> Nibbles.length path then trie
        else
          let _, key = Nibbles.split key i in
          let subtree = remove key subtree in
          let data =
            match subtree.data with
            | Empty -> Empty
            | Extension {path = path'; ending} -> Extension {path = Nibbles.(path ^ path'); ending}
            | Branch (_, _) -> Extension {path; ending = Subtree subtree}
          in
          make data
    | Branch (branches, v) -> (
      match Nibbles.uncons key with
      | None -> make (Branch (branches, None))
      | Some (k_0, key) ->
          let branches = Iarray.map (fun trie -> remove key trie) branches in
          let non_empty_branches =
            Iarray.to_seq branches
            |> Seq.mapi (fun index branch -> (index, branch))
            |> Seq.filter (fun (index, branch) -> branch.data <> Empty)
          in
          let data =
            match (Seq.uncons non_empty_branches, v) with
            | Some ((i, b_i), bs), Some _ -> Branch (branches, v)
            | Some ((i, b_i), bs), None -> (
              match Seq.uncons bs with
              | None -> (
                (* Exactly one non-empty branch, we can compress the trie. *)
                match b_i.data with
                | Empty -> Empty
                | Branch (_, _) -> Extension {path = Nibbles.of_nibble i; ending = Subtree b_i}
                | Extension {path; ending} -> Extension {path = Nibbles.(of_nibble i ^ path); ending} )
              (* Multiple branches, we cannot compress the trie. *)
              | Some (_, _) -> Branch (branches, v) )
            (* No branches. Compress to either empty (if value is empty) or extension ending in value. *)
            | None, Some v -> Extension {path = Nibbles.empty; ending = Value v}
            | None, None -> Empty
          in
          make data )

  let rec graft_disjoint (path, ending) (key, value) : 'a ending =
    match (Nibbles.uncons path, Nibbles.uncons key, ending) with
    | None, None, Value _ -> Value value
    | None, None, Subtree subtree -> Subtree (add key value subtree)
    | Some (p_0, path), None, _ ->
        Subtree (make (Branch (one_branch (p_0, extension ~path ~ending), Some value)))
    | None, Some (k_0, key'), Value v ->
        Subtree (make (Branch (one_branch (k_0, extension ~path:key' ~ending:(Value value)), Some v)))
    | None, Some (k_0, key'), Subtree subtree -> Subtree (add key value subtree)
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

  let add ?(hash_keys = false) (key : Bytes.t) (value : 'a) (trie : 'a t) =
    let key = if hash_keys then B32.to_bytes (Crypto.keccak_256 key) else key in
    add (Nibbles.of_bytes key) value trie

  let remove ?(hash_keys = false) key trie =
    let key = if hash_keys then B32.to_bytes (Crypto.keccak_256 key) else key in
    remove (Nibbles.of_bytes key) trie

  let of_seq ?(hash_keys = false) (entries : (Bytes.t * 'a) Seq.t) : 'a t =
    entries |> Seq.fold_left (fun trie (k, v) -> add ~hash_keys k v trie) empty

  let of_seq_i ?(hash_keys = false) (entries : 'a Seq.t) =
    let to_kv i v = (Rlp.encode U64.(to_rlp ~$i), v) in
    of_seq ~hash_keys (Seq.mapi to_kv entries)

  let of_map ?(hash_keys = false) (map : 'a Bytes.Map.t) = of_seq ~hash_keys (Bytes.Map.to_seq map)

  let rec to_seq ~(prefix : Nibbles.t) (trie : 'a t) : (Bytes.t * 'a) Seq.t =
    match trie.data with
    | Empty -> Seq.empty
    | Branch (branches, value) ->
        Iarray.to_seq branches
        |> Seq.mapi (fun k_i branch ->
            let prefix = Nibbles.(prefix ^ of_nibble k_i) in
            to_seq ~prefix branch )
        |> Seq.concat
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
        Iarray.equal (equal elt_equal) b_l b_r && Stdlib.(v_l = v_r)
    | _ -> false

  and ending_equal elt_equal l r =
    match (l, r) with Value l, Value r -> elt_equal l r | Subtree l, Subtree r -> l = r | _ -> false

  let merkleization_to_rlp_encoded = function Hash h -> Rlp.encode_bytes (B32.to_bytes h) | Small s -> s

  let rec merkleized ~(value_to_bytes : 'a -> Bytes.t) (node : 'a t) : 'a t =
    match node with
    | {merkleized = Some _} -> node
    | _ ->
        let data, encoded =
          match node.data with
          | Empty -> (Empty, Rlp.(encode_bytes ""))
          | Branch (branches, value) ->
              let branches_merkleized = Iarray.map (merkleized ~value_to_bytes) branches in
              let merkleizations =
                Iarray.to_seq branches_merkleized |> Seq.map (merkleization ~value_to_bytes)
              in
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

  and merkleization ~value_to_bytes (node : 'a t) =
    match (merkleized ~value_to_bytes node).merkleized with Some m -> m | None -> assert false

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
        let encoded_ending = merkleization_to_rlp_encoded (merkleization ~value_to_bytes subtree) in
        Rlp.encode_list [encoded_path; encoded_ending]

  let merkle_root ~value_to_bytes (trie : 'a t) =
    match merkleization ~value_to_bytes trie with
    | Small encoded -> Crypto.keccak_256 encoded
    | Hash hash -> hash

  let update (k : Bytes.t) (update_fn : 'v option -> 'v option) trie =
    let entry = find_opt k trie in
    match update_fn entry with None -> remove k trie | Some v -> add k v trie

  let at (k : Bytes.t) : ('v t, 'v option) Lens.t =
    {get = (fun m -> find_opt k m); set = (fun v m -> update k (fun _ -> v) m)}
end

module Make (Params : sig
  val hash_keys : bool
end) (Key : sig
  type t
  val of_bytes_exn : Bytes.t -> t
  val to_bytes : t -> Bytes.t
end) (Value : sig
  type t

  val equal : t -> t -> bool

  val to_bytes : t -> Bytes.t

  val of_yojson : Yojson.Safe.t -> (t, string) result
  val to_yojson : t -> Yojson.Safe.t
end) =
struct
  type nonrec t = (Key.t * Value.t) Generic.t
  type merkleization = Generic.merkleization

  let equal : t -> t -> bool = Generic.equal (fun (_, v1) (_, v2) -> Value.equal v1 v2)

  let empty : t = Generic.empty

  let hash_key =
    if Params.hash_keys then fun (k : Key.t) -> B32.to_bytes (Crypto.keccak_256 (Key.to_bytes k))
    else fun (k : Key.t) -> Key.to_bytes k

  let of_seq (seq : (Key.t * Value.t) Seq.t) : t =
    Generic.of_seq (Seq.map (fun (k, v) -> (hash_key k, (k, v))) seq)
  let to_seq (trie : t) : (Key.t * Value.t) Seq.t =
    (* TODO: it's unnecessary to reconstruct k_enc here *)
    Generic.to_seq trie |> Seq.map (fun (k_enc, (k, v)) -> (k, v))

  let find_hash_opt (k : Key.t) (h : B32.t) (trie : t) : Value.t option =
    Option.map snd (Generic.find_opt (B32.to_bytes h) trie)
  let remove_hash (k : Key.t) (h : B32.t) (trie : t) : t = Generic.remove (B32.to_bytes h) trie
  let add_hash (k : Key.t) (h : B32.t) (v : Value.t) (trie : t) : t = Generic.add (B32.to_bytes h) (k, v) trie

  let find_opt (k : Key.t) (trie : t) : Value.t option = Option.map snd (Generic.find_opt (hash_key k) trie)
  let remove (k : Key.t) (trie : t) : t = Generic.remove (hash_key k) trie
  let add (k : Key.t) (v : Value.t) (trie : t) : t = Generic.add (hash_key k) (k, v) trie

  let merkleization : t -> merkleization =
    Generic.merkleization ~value_to_bytes:(fun (_, v) -> Value.to_bytes v)
  let merkleized : t -> t = Generic.merkleized ~value_to_bytes:(fun (_, v) -> Value.to_bytes v)
  let merkle_root : t -> B32.t = Generic.merkle_root ~value_to_bytes:(fun (_, v) -> Value.to_bytes v)

  exception Value_decoding_error of string
  let of_yojson : Yojson.Safe.t -> (t, string) result = function
    | `Assoc fields -> (
      try
        Ok
          ( List.to_seq fields
          |> Seq.map (fun (k, v) ->
              let k = Key.of_bytes_exn (Bytes.of_hex_string k) in
              let v =
                match Value.of_yojson v with Ok elt -> elt | Error msg -> raise (Value_decoding_error msg)
              in
              (k, v) )
          |> of_seq )
      with Value_decoding_error err -> Error err )
    | _ -> Error "Mpt.t"

  let to_yojson (trie : t) : Yojson.Safe.t =
    let fields =
      to_seq trie
      |> Seq.map (fun (k, v) ->
          let k = Bytes.to_hex_string (Key.to_bytes k) in
          let v = Value.to_yojson v in
          (k, v) )
      |> List.of_seq
    in
    `Assoc fields

  let at (k : Key.t) : (t, Value.t option) Lens.t =
    let h = Crypto.keccak_256 (Key.to_bytes k) in
    let get m = find_hash_opt k h m in
    let set v m = match v with None -> remove_hash k h m | Some v -> add_hash k h v m in
    Lens.{get; set}
end
