open Numeric
open Byte_string

module Iarray = struct
  include Stdlib.Iarray
  let to_yojson elt_to_yojson arr = `List (List.map elt_to_yojson (to_list arr))
end

let branching_factor = 16

type merkleization = Small of Bytes.t | Hash of B32.t [@@deriving to_yojson]
type impl = Empty | Branch of (t Iarray.t * Rlp.t) | Extension of {path : Nibbles.t; ending : ending}
[@@deriving to_yojson]
and ending = Subtree of t | Value of Rlp.t [@@deriving to_yojson]

and t = {data : impl; merkleized : merkleization option} [@@deriving to_yojson]

let dump trie = Format.eprintf "%s\n" (Yojson.Safe.pretty_to_string (to_yojson trie))

let empty_hash = Crypto.keccak_256 (Rlp.encode (Rlp.Bytes ""))
let empty = {data = Empty; merkleized = Some (Small (Rlp.encode_bytes ""))}

let make data = {data; merkleized = None}

let rec find (k : Nibbles.t) ?(depth = 0) (trie : t) =
  match trie.data with
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

let one_branch (k_0, trie_0) : t Iarray.t =
  Iarray.init branching_factor (fun i -> if i = k_0 then trie_0 else empty)
let two_branches (k_0, trie_0) (k_1, trie_1) : t Iarray.t =
  Iarray.init branching_factor (fun i -> if i = k_0 then trie_0 else if i = k_1 then trie_1 else empty)

let extension ~path ~ending =
  match ending with
  | Subtree subtree when Nibbles.length path = 0 -> subtree
  | _ -> make (Extension {path; ending})

(* Note that we do not optimize very hard for the case where the key is not present. Every node touched will
   be assumed to be dirtied, even if the resulting trie is identical to the original one. *)
let rec remove key (trie : t) =
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
          | Extension {path = path'; ending} -> Extension {path = Nibbles.concat path path'; ending}
          | Branch (_, _) -> Extension {path; ending = Subtree subtree}
        in
        make data
  | Branch (branches, v) -> (
    match Nibbles.uncons key with
    | None -> make (Branch (branches, Rlp.Bytes ""))
    | Some (k_0, key) ->
        let branches = Iarray.map (fun trie -> remove key trie) branches in
        let non_empty_branches =
          Iarray.to_seq branches
          |> Seq.mapi (fun index branch -> (index, branch))
          |> Seq.filter (fun (index, branch) -> branch.data <> Empty)
        in
        let data =
          match Seq.uncons non_empty_branches with
          | Some ((i, b_i), bs) ->
              if v = Rlp.Bytes "" then
                match Seq.uncons bs with
                | None -> (
                  (* Exactly one non-empty branch, we can compress the trie. *)
                  match b_i.data with
                  | Empty -> Empty
                  | Branch (_, _) -> Extension {path = Nibbles.of_nibble i; ending = Subtree b_i}
                  | Extension {path; ending} -> Extension {path = Nibbles.(concat (of_nibble i) path); ending}
                  )
                | Some (_, _) -> Branch (branches, v)
              else Branch (branches, v)
          | None ->
              (* No branches. Compress to either empty (if value is empty) or extension ending in value. *)
              if v = Rlp.Bytes "" then Empty else Extension {path = Nibbles.empty; ending = Value v}
        in
        make data )

let rec graft_disjoint (path, ending) (key, value) : ending =
  match (Nibbles.uncons path, Nibbles.uncons key, ending) with
  | None, None, Value _ -> Value value
  | None, None, Subtree subtree -> Subtree (add key value subtree)
  | Some (p_0, path), None, _ -> Subtree (make (Branch (one_branch (p_0, extension ~path ~ending), value)))
  | None, Some (k_0, key'), Value v ->
      Subtree (make (Branch (one_branch (k_0, extension ~path:key' ~ending:(Value value)), v)))
  | None, Some (k_0, key'), Subtree subtree -> Subtree (add key value subtree)
  | Some (p_0, path), Some (k_0, key), _ ->
      assert (p_0 <> k_0) ;
      Subtree
        (make
           (Branch
              ( two_branches (p_0, extension ~path ~ending) (k_0, extension ~path:key ~ending:(Value value))
              , Rlp.Bytes "" ) ) )

and add key value (trie : t) : t =
  if value = Rlp.Bytes "" then remove key trie
  else
    (*assert (value <> Rlp.Bytes "") ;*)
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
      | None -> make (Branch (branches, value))
      | Some (k_0, key) ->
          let branches =
            Iarray.mapi (fun i branch -> if i = k_0 then add key value branch else branch) branches
          in
          make (Branch (branches, branch_value)) )

let of_seq (entries : (Bytes.t * Bytes.t) Seq.t) =
  entries
  |> Seq.map (fun (k, v) -> (Nibbles.of_bytes k, Rlp.Bytes v))
  |> Seq.fold_left (fun trie (k, v) -> add k v trie) empty

let of_seq_i (entries : Bytes.t Seq.t) =
  let to_kv i v = (Rlp.encode U64.(to_rlp ~$i), v) in
  of_seq (Seq.mapi to_kv entries)

let of_map (map : Bytes.t Bytes.Map.t) = of_seq (Bytes.Map.to_seq map)

let rec to_patricia (trie : t) : Mpt.PatriciaTrie.t =
  (* TODO: delete. For debugging purposes only. *)
  match trie.data with
  | Empty -> Mpt.PatriciaTrie.Empty
  | Branch (bs, v) -> Mpt.PatriciaTrie.Branch (Iarray.map to_patricia bs, v)
  | Extension {path; ending = Value v} -> Mpt.PatriciaTrie.Extension {path; ending = Value v}
  | Extension {path; ending = Subtree subtree} ->
      Mpt.PatriciaTrie.Extension {path; ending = Subtree (to_patricia subtree)}

let rec ( = ) l r =
  match (l, r) with
  | {merkleized = Some (Hash h_l); _}, {merkleized = Some (Hash h_r); _} -> B32.(h_l = h_r)
  | {merkleized = Some (Small s_l); _}, {merkleized = Some (Small s_r); _} -> Bytes.(s_l = s_r)
  | {merkleized = Some _; _}, {merkleized = Some _; _} -> false
  | {data = Empty; _}, {data = Empty; _} -> true
  | {data = Extension e_l; _}, {data = Extension e_r; _} ->
      Nibbles.(e_l.path = e_r.path) && ending_equal e_l.ending e_r.ending
  | {data = Branch (b_l, v_l); _}, {data = Branch (b_r, v_r); _} ->
      Iarray.equal ( = ) b_l b_r && Stdlib.(v_l = v_r)
  | _ -> false

and ending_equal l r =
  match (l, r) with Value l, Value r -> Stdlib.(l = r) | Subtree l, Subtree r -> l = r | _ -> false

let merkleization_to_rlp_encoded = function Hash h -> Rlp.encode_bytes (B32.to_bytes h) | Small s -> s

let rec merkleized (node : t) : merkleization * t =
  match node with
  | {merkleized = Some (Hash h); _} -> (Hash h, {data = node.data; merkleized = Some (Hash h)})
  | {merkleized = Some (Small s); _} -> (Small s, {data = node.data; merkleized = Some (Small s)})
  | _ ->
      let data, encoded =
        match node.data with
        | Empty -> (Empty, Rlp.(encode_bytes ""))
        | Branch (branches, value) ->
            let branches_merkleized = Iarray.map merkleized branches in
            let merkleizations = Iarray.to_seq branches_merkleized |> Seq.map fst in
            let branches = Iarray.map snd branches_merkleized in
            (Branch (branches, value), branch_to_rlp_encoded merkleizations value)
        | Extension {path; ending} ->
            let ending =
              match ending with
              | Value value -> Value value
              | Subtree subtree -> Subtree (snd (merkleized subtree))
            in
            (Extension {path; ending}, extension_to_rlp_encoded path ending)
      in
      let merkleized =
        if Bytes.length encoded < 32 then Small encoded else Hash (Crypto.keccak_256 encoded)
      in
      (merkleized, {data; merkleized = Some merkleized})

and branch_to_rlp_encoded (branches : merkleization Seq.t) (value : Rlp.t) =
  let encoded_branches = Seq.map merkleization_to_rlp_encoded branches in
  let encoded_fields = Seq.(append encoded_branches (singleton (Rlp.encode value))) in
  Rlp.encode_list (List.of_seq encoded_fields)

and extension_to_rlp_encoded (path : Nibbles.t) (ending : ending) =
  match ending with
  | Value value ->
     let encoded_path = Rlp.encode_bytes (Nibbles.hex_prefix_encode path true) in
      let encoded_ending = Rlp.encode value in
      Rlp.encode_list [encoded_path; encoded_ending]
  | Subtree subtree ->
     let encoded_path = Rlp.encode_bytes (Nibbles.hex_prefix_encode path false) in
      let merkleization, _ = merkleized subtree in
      let encoded_ending = merkleization_to_rlp_encoded merkleization in
      Rlp.encode_list [encoded_path; encoded_ending]

let merkle_root (trie : t) =
  let merkleization, trie = merkleized trie in
  let root = match merkleization with Small encoded -> Crypto.keccak_256 encoded | Hash hash -> hash in
  root
