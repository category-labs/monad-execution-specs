open Monad_lib
open Test_utils.Utils
open Numeric
open Byte_string
open Chain.Ethereum
open QCheck2

(* Expected commitments generated from the MIP-8 pseudocode transcribed over the pure-Python port
   of the official BLAKE3 reference implementation (itself validated against the official BLAKE3
   test vectors). *)

let word byte = B32.make (Char.chr byte)

let commitment_vectors =
  [ ( "single word at offset 0"
    , [(0, word 0xAA)]
    , "d377db476300e79eb7e8dd80506ef3debf224f5cb0df401a005607ef42b9b18a" )
  ; ( "single word at offset 1"
    , [(1, word 0xAA)]
    , "61042500f8403c126d1534fbb9cc3b446794596870e3d05e2485b8200ddca295" )
  ; ( "offsets 0 and 1: a single pair-leaf, no merge"
    , [(0, word 0xAA); (1, word 0xBB)]
    , "79a60857dc3cd6ed8aca49b9748141ca2086fdf1927bcc37e4f86d401d2d6da4" )
  ; ( "offsets 0 and 4: carry at level 0, merge at level 1"
    , [(0, word 0xAA); (4, word 0xBB)]
    , "51d17e6dc3e77ac22025cf1dc1e3628731326d682e75d324b2ed4cea5dac2a16" )
  ; ( "offsets 0 and 127: carried through five levels, merge at level 5"
    , [(0, word 0xAA); (127, word 0xBB)]
    , "ae488a4febdb2c70707801d0f338ab86e514ee4bdc002dd1cc4b9eff08759843" )
  ; ( "full page"
    , List.init 128 (fun k -> (k, word ((k mod 255) + 1)))
    , "37f2a5b1b95856749c4d24cf5617ae52be0d7275f844073092623b7d86a93a34" ) ]

let test_commitment_vector (name, entries, expected) =
  Alcotest.(
    test_case name `Quick (fun () ->
        check' b32 ~msg:"page commitment"
          ~expected:(B32.of_hex_string expected)
          ~actual:(Storage_ismc.page_commitment entries) ) )

let test_invalid_input name expected_message entries =
  Alcotest.(
    test_case name `Quick (fun () ->
        check_raises name (Invalid_argument expected_message) (fun () ->
            ignore (Storage_ismc.page_commitment entries) ) ) )

let test_bitmap_binding =
  Alcotest.(
    test_case "same word at different offsets commits differently" `Quick (fun () ->
        check' bool ~msg:"commitments differ" ~expected:false
          ~actual:
            B32.(
              Storage_ismc.page_commitment [(2, word 0xAA)]
              = Storage_ismc.page_commitment [(3, word 0xAA)] ) ) )

(* Property: the commitment does not depend on the order in which entries are given. *)
let gen_page_and_permutation : ((int * B32.t) list * (int * B32.t) list) Gen.t =
  Gen.(
    let* entries =
      list_size (int_range 1 30) (pair (int_range 0 127) (map (fun b -> word (1 + (b mod 255))) nat))
      |> map (List.sort_uniq (fun (o1, _) (o2, _) -> Int.compare o1 o2))
    in
    let* shuffled = shuffle_l entries in
    return (entries, shuffled) )

let permutation_invariant (entries, shuffled) =
  B32.(Storage_ismc.page_commitment entries = Storage_ismc.page_commitment shuffled)

let print_page = Print.(pair (list (pair int B32.to_hex_string)) (list (pair int B32.to_hex_string)))

(* The root must group slots into pages and commit {keccak(page_index) -> RLP(page_commitment)}
   pairs, exactly as the slot-keyed storage trie in [Account.to_rlp] commits individual slots. *)
let slot i = U256.(to_repr ~$i)

let expected_root (pages : (U256.t * (int * B32.t) list) list) =
  let mpt =
    pages
    |> List.to_seq
    |> Seq.map (fun (page_index, entries) ->
        let k = B32.to_bytes (Crypto.keccak_256 (B32.to_bytes (U256.to_repr page_index))) in
        let v = Rlp.encode (Rlp.of_bytes32 (Storage_ismc.page_commitment entries)) in
        (k, v) )
    |> Mpt.of_seq
  in
  mpt.root_hash

let test_root_groups_pages =
  let high_slot = B32.make '\xff' in
  let storage =
    B32.Map.of_seq
      (List.to_seq
         [ (slot 0, word 0x11)
         ; (slot 1, word 0x22)
         ; (slot 127, word 0x33)
         ; (slot 128, word 0x44)
         ; (high_slot, word 0x55) ] )
  in
  let expected =
    expected_root
      [ (U256.(~$0), [(0, word 0x11); (1, word 0x22); (127, word 0x33)])
      ; (U256.(~$1), [(0, word 0x44)])
      ; (Storage_ismc.page_index high_slot, [(127, word 0x55)]) ]
  in
  Alcotest.(
    test_case "slots are grouped into pages" `Quick (fun () ->
        check' b32 ~msg:"root" ~expected ~actual:(Storage_ismc.root storage) ) )

let test_root_ignores_zero_values =
  let storage = B32.Map.of_seq (List.to_seq [(slot 0, word 0x11); (slot 200, B32.zeros)]) in
  let expected = expected_root [(U256.(~$0), [(0, word 0x11)])] in
  Alcotest.(
    test_case "zero-valued slots are treated as absent" `Quick (fun () ->
        check' b32 ~msg:"root" ~expected ~actual:(Storage_ismc.root storage) ) )

let test_root_empty =
  Alcotest.(
    test_case "empty storage commits the empty trie root" `Quick (fun () ->
        check' b32 ~msg:"root"
          ~expected:(Mpt.of_seq Seq.empty).root_hash
          ~actual:(Storage_ismc.root B32.Map.empty) ) )

let () =
  Alcotest.run "MIP-8 page-ified storage commitment"
    [ ("page_commitment vectors", List.map test_commitment_vector commitment_vectors)
    ; ( "page_commitment validation"
      , [ test_invalid_input "empty page" "Storage_ismc.page_commitment: empty page" []
        ; test_invalid_input "duplicate offset" "Storage_ismc.page_commitment: duplicate offset"
            [(7, word 0xAA); (7, word 0xBB)]
        ; test_invalid_input "offset out of range" "Storage_ismc.page_commitment: offset out of range"
            [(128, word 0xAA)]
        ; test_bitmap_binding
        ; check_prop ~count:100 ~print:print_page ~name:"permutation_invariant page"
            gen_page_and_permutation permutation_invariant ] )
    ; ("root", [test_root_groups_pages; test_root_ignores_zero_values; test_root_empty]) ]
