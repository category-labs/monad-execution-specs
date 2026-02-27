open Monad_lib
open Byte_string
open Test_utils.Utils
open QCheck2

module Nibbles = Mpt.Nibbles

let gen_nibble : char Gen.t = Gen.(char_range '\x00' '\x0f')
let gen_nibbles : Nibbles.t Gen.t = Gen.(map Nibbles.of_nibble_array (small_string ~gen:gen_nibble))

let round_trip_hp_ok ((nibbles, flag) : Nibbles.t * bool) =
  let hp = Nibbles.hex_prefix_encode nibbles flag in
  let nibbles', flag' = Nibbles.hex_prefix_decode hp in
  nibbles = nibbles' && flag = flag'

let test_case_of_fixture (name, fixture) =
  let open Fixtures.TrieTest in
  let trie =
    List.fold_left
      (fun trie (k, v) -> if Bytes.(v = empty) then Mpt.Generic.remove k trie else Mpt.Generic.add k v trie)
      Mpt.Generic.empty fixture.entries
    |> Mpt.Generic.merkleized ~value_to_bytes:Fun.id
  in
  let root' = Mpt.Generic.merkle_root trie in
  Alcotest.(test_case name `Quick (fun () -> check' b32 ~msg:"Root" ~expected:fixture.root ~actual:root'))

let test_fixture_file ?(hash_keys = false) file =
  (* TODO: do something disciplined about paths *)
  let path = "../../../../third_party/tests/TrieTests/" ^ file in
  let test_fixtures =
    Result.get_ok (Fixtures.TrieTest.of_yojson ~hash_keys (Yojson.Safe.from_file ~fname:file path))
  in
  (file, List.map test_case_of_fixture test_fixtures)

let () =
  let open Alcotest in
  run "Tests on MPT data structures"
    [ ( "Hex-prefix round-trip"
      , [ check_prop
            ~print:Print.(pair Nibbles.to_hex_string bool)
            ~name:"round_trip_hp_ok ns"
            Gen.(pair gen_nibbles bool)
            round_trip_hp_ok ] )
    ; test_fixture_file ~hash_keys:true "hex_encoded_securetrie_test.json"
    ; test_fixture_file ~hash_keys:true "trietest_secureTrie.json"
    ; test_fixture_file ~hash_keys:true "trieanyorder_secureTrie.json"
    ; test_fixture_file "trietest.json"
    ; test_fixture_file "trieanyorder.json" ]
