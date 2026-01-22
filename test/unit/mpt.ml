open Monad_lib
open Test_utils.Utils
open QCheck2
open Byte_string

(* Using only three characters ensures paths have overlaps to test Patricia compression *)
let gen_path : Mpt.Nibbles.t Gen.t =
  Gen.(
    map Mpt.Nibbles.of_nibble_array (small_string ~gen:(frequencyl [(1, '\x01'); (1, '\x02'); (1, '\x03')])) )

let gen_entries : (Mpt.Nibbles.t * Rlp.t) list Gen.t =
  Gen.(
    let entry = pair gen_path (rlp ~nonempty:true) in
    small_list entry )

let gen_nibble : char Gen.t = Gen.(char_range '\x00' '\x0f')
let gen_nibbles : Mpt.Nibbles.t Gen.t = Gen.(map Mpt.Nibbles.of_nibble_array (small_string ~gen:gen_nibble))

let print_entries = Print.(list (pair Mpt.Nibbles.to_hex_string Rlp.to_string))

let round_trip_trie_ok entries =
  let open Mpt in
  let map = Nibbles.Map.of_list entries in
  let trie = Trie.of_seq (List.to_seq entries) in
  Nibbles.Map.to_seq map
  |> Seq.for_all (fun (k, v) -> match Trie.find k trie with None -> false | Some v' -> v = v')

let round_trip_patricia_ok entries =
  let open Mpt in
  let map = Nibbles.Map.of_list entries in
  let trie = Trie.of_seq (List.to_seq entries) in
  let pt = PatriciaTrie.of_trie trie in
  Nibbles.Map.to_seq map
  |> Seq.for_all (fun (k, v) -> match PatriciaTrie.find k pt with None -> false | Some v' -> v = v')

let round_trip_mpt_ok entries =
  let open Mpt in
  let map = Nibbles.Map.of_list entries in
  let trie = Trie.of_seq (List.to_seq entries) in
  let pt = PatriciaTrie.of_trie trie in
  let mpt = of_patricia pt in
  Nibbles.Map.to_seq map
  |> Seq.for_all (fun (k, v) -> match find k mpt with None -> false | Some v' -> v = v')

let round_trip_hp_ok (nibbles, flag) =
  let hp = Mpt.Nibbles.hex_prefix_encode nibbles flag in
  let nibbles', flag' = Mpt.Nibbles.hex_prefix_decode hp in
  nibbles = nibbles' && flag = flag'

let test_case_of_fixture (name, fixture) =
  let open Fixtures.TrieTest in
  let root' = (Mpt.of_seq (List.to_seq fixture.entries)).root_hash in
  Alcotest.(test_case name `Quick (fun () -> check' b32 ~msg:"Root" ~expected:fixture.root ~actual:root'))

let test_fixture_file ?(hash_keys = false) file =
  (* TODO: do something disciplined about paths *)
  let path = "../../../../third_party/tests/TrieTests/" ^ file in
  let test_fixtures =
    Result.get_ok (Fixtures.TrieTest.of_yojson ~hash_keys (Yojson.Safe.from_file ~fname:file path))
  in
  (file, List.map test_case_of_fixture test_fixtures)

let patricia_opt_vs_unopt entries =
  let open Mpt in
  let entries = List.to_seq entries in
  let from_trie = PatriciaTrie.of_trie (Trie.of_seq entries) in
  let from_entries = PatriciaTrie.of_seq entries in
  if Mpt.PatriciaTrie.(from_trie = from_entries) then true else false

let nibbles_of_hex bs =
  Mpt.Nibbles.init (String.length bs) (fun i ->
      let chr = bs.[i] in
      if chr >= '0' && chr <= '9'
      then Char.code chr - Char.code '0'
                                    else Char.code chr - Char.code 'a')
  
let patricia_test entries =
  Alcotest.test_case "entries" `Quick (fun () ->
      let open Mpt in
      let entries =
        List.to_seq entries
        |> Seq.map (fun (k_bs, v_bs) ->
            (nibbles_of_hex k_bs, Rlp.Bytes (Bytes.of_hex_string v_bs)) )
      in
      let from_trie = PatriciaTrie.of_trie (Trie.of_seq entries) in
      let from_entries = PatriciaTrie.of_seq entries in
      if Mpt.PatriciaTrie.(from_trie = from_entries) then ()
      else begin
        Format.eprintf "from_trie: " ;
        PatriciaTrie.dump from_trie ;
        Format.eprintf "from_entries: " ;
        PatriciaTrie.dump from_entries ;
        Alcotest.fail "Bad!"
      end )

module Nibbles = Mpt.Nibbles
let ns = Nibbles.of_bytes (Bytes.of_hex_string "ab")

let ns_2 = ns |> Nibbles.prepend 11 |> Nibbles.prepend 10
let () =
  Format.eprintf "{ bytes = \"%s\"; start = %d; length = %d }\n" (Bytes.to_hex_string ns_2.bytes) ns_2.start
    ns_2.length ;
  assert (Nibbles.(ns_2 = Nibbles.of_bytes (Bytes.of_hex_string "abab")))

let () = assert (Nibbles.(ns.$[0]) = 10)
let () = assert (Nibbles.(ns.$[1]) = 11)

let () =
  let open Alcotest in
  run "Tests on MPT data structures"
    [ (*( "Hex-prefix round-trip"
      , [ check_prop
            ~print:Print.(pair byte_string bool)
            ~name:"round_trip_hp_ok ns"
            Gen.(pair gen_nibbles bool)
            round_trip_hp_ok ] )
    ; ( "Trie round-trip"
      , [ check_prop ~count:100 ~print:print_entries ~name:"round_trip_trie_ok entries" gen_entries
            round_trip_trie_ok ] )
    ; ( "Patricia round-trip"
      , [ check_prop ~count:100 ~print:print_entries ~name:"round_trip_patricia_ok entries" gen_entries
            round_trip_patricia_ok ] )
    ; ( "MPT round-trip"
      , [ check_prop ~count:1000 ~print:print_entries ~name:"round_trip_mpt_ok entries" gen_entries
            round_trip_mpt_ok ] )
    ; test_fixture_file ~hash_keys:true "hex_encoded_securetrie_test.json"
    ; test_fixture_file ~hash_keys:true "trietest_secureTrie.json"
    ; test_fixture_file ~hash_keys:true "trieanyorder_secureTrie.json"
    ; test_fixture_file "trietest.json"
    ; test_fixture_file "trieanyorder.json" *)
      ( "Patricia opt vs unopt"
      , [ check_prop ~count:10000 ~print:print_entries ~name:"round_trip_trie_ok entries" gen_entries
            patricia_opt_vs_unopt ] )
    ]
(*
      ("Examples", [patricia_test [("010", "61"); ("011", "61"); ("0", "61")]]) ]
      ( "Examples"
      , [ patricia_test []
        ; patricia_test [("ab", "ff")]
        ; patricia_test [("ab", "ff"); ("abab", "ff")]
        ; patricia_test [("abab", "ff"); ("abab", "ff"); ("abcd", "ff")] ] ) ]
       *)
