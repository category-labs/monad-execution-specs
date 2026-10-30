(** MIP-8: Page commitment via Induced Subtree Merkle Commit (ISMC). *)

open Byte_string
open Numeric

module Page = struct
  (** MIP-8: A page is a contiguous, page-aligned group of {!words_per_page} EVM words.
      The mapping functions from slot to page information are defined as follows:
      {[
        page_index(slot) = slot >> 7
        offset(slot) = slot & 0x7f
      ]}
  *)
  let offset_bits = 7

  (** Number of 32-byte EVM words in a page. *)
  let words_per_page = 1 lsl offset_bits

  (** Mask selecting the offset bits of a slot. *)
  let offset_mask = words_per_page - 1

  (** [index_of_slot slot] is [slot >> 7], the index of the page containing [slot]. *)
  let index_of_slot (slot : B32.t) : U256.t = U256.shift_right (U256.of_repr slot) offset_bits

  (** [offset_of_slot slot] is [slot & 0x7f], the position of [slot] within its page. *)
  let offset_of_slot (slot : B32.t) : int = U256.(to_int (logand (of_repr slot) ~$offset_mask))

  (** [align slot] is the slot at offset zero of the page containing [slot]. Two slots have the
    same alignment exactly when they belong to the same page, so this serves as a canonical key
    for a page. *)
  let align (slot : B32.t) : B32.t = U256.to_repr (U256.shift_left (index_of_slot slot) offset_bits)
end

module Blake3 = Crypto.Blake3

(** The occupied words of a page keyed by offsets. *)
module Offsets = Map.Make (Int)

(** Domain-separated leaf IV. Derived once from the constant 32-byte
    domain string and used to compress every active pair-leaf to 32
    bytes, separating the leaf domain from the parent domain. *)
let leaf_iv =
  Blake3.compress Blake3.iv
    ("ultra_merkle_pair_leaf_domain___" ^ Bytes.make 32 '\x00')
    ~counter:0 ~block_len:64 ~flags:Blake3.derive_key_material

(** [page_commitment entries] is the ISMC commitment of the page with
    [(page_offset, word)] entries.

    Raises [Invalid_argument] if [entries] is empty or contains a
    duplicate/out-of-range offset. *)
let page_commitment (entries : (int * B32.t) list) : B32.t =
  if entries = [] then invalid_arg "Ismc.page_commitment: empty page" ;
  let words =
    List.fold_left
      (fun words (offset, word) ->
        if offset < 0 || offset >= Page.words_per_page then
          invalid_arg "Ismc.page_commitment: offset out of range" ;
        if Offsets.mem offset words then invalid_arg "Ismc.page_commitment: duplicate offset" ;
        Offsets.add offset word words )
      Offsets.empty entries
  in
  let occupied offset = Offsets.mem offset words in

  (* Phase 1: Data merge phase.
     A bottom-up reduction of the occupied pair-leaves. This captures the payload of
     all active data in the page. *)
  let leaf_hash i =
    let word offset = Option.value (Offsets.find_opt offset words) ~default:B32.zeros in
    Blake3.compress leaf_iv
      (B32.to_bytes (word (2 * i)) ^ B32.to_bytes (word ((2 * i) + 1)))
      ~counter:0 ~block_len:64 ~flags:Blake3.derive_key_material
  in
  let leaves =
    List.init (Page.words_per_page / 2) Fun.id
    (* Extract only occupied pair-leaves (bypassing empty branches). *)
    |> List.filter (fun i -> occupied (2 * i) || occupied ((2 * i) + 1))
    |> List.map (fun i -> (i, leaf_hash i))
  in

  let parent_hash v1 v2 =
    Blake3.compress Blake3.iv
      (B32.to_bytes v1 ^ B32.to_bytes v2)
      ~counter:0 ~block_len:64
      ~flags:Blake3.(chunk_start lor chunk_end)
  in
  let rec merge level nodes =
    (* Nodes are siblings if they share the same parent at the next level. *)
    let rec merge_siblings = function
      | (i1, v1) :: (i2, v2) :: rest when i1 lsr (level + 1) = i2 lsr (level + 1) ->
          (* Hash the two 32-byte children into a new 32-byte parent. *)
          (i1, parent_hash v1 v2) :: merge_siblings rest
      | node :: rest ->
          (* Singleton case: carry up without hashing. *)
          node :: merge_siblings rest
      | [] -> []
    in
    match nodes with
    | [(_, subtree_root)] ->
        (* Early exit: the tree is fully reduced to a single root. *)
        subtree_root
    | _ ->
        assert (level < Page.offset_bits - 1) ;
        merge (level + 1) (merge_siblings nodes)
  in
  let subtree_root = merge 0 leaves in

  (* Phase 2: Structural seal phase.
     Uniquely bind the subtree root to the exact geometric layout. *)
  let slot_bitmap_le =
    Bytes.init (Page.words_per_page / 8) (fun byte ->
        List.init 8 Fun.id
        |> List.fold_left (fun acc bit -> if occupied ((8 * byte) + bit) then acc lor (1 lsl bit) else acc) 0
        |> Char.chr )
  in
  Blake3.hash (slot_bitmap_le ^ B32.to_bytes subtree_root)
