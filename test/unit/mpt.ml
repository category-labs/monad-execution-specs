open Monad_lib
open Numeric
open Test_utils.Utils
open QCheck2

(* Using only three characters ensures paths have overlaps to test Patricia compression *)
let gen_path : Mpt.Nibbles.t Gen.t =
  Gen.(small_string ~gen:(frequencyl [(1, '\x01'); (1, '\x02'); (1, '\x03')]))

let gen_entries : (Mpt.Nibbles.t * Rlp.t) list Gen.t =
  Gen.(
    let entry = pair gen_path (rlp ~nonempty:true) in
    small_list entry )

let gen_nibble : char Gen.t = Gen.(char_range '\x00' '\x0f')
let gen_nibbles : Mpt.Nibbles.t Gen.t = Gen.(small_string ~gen:gen_nibble)

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

open Yojson.Safe
open Yojson.Safe.Util

let ( .$() ) json key = member key json

let hex_or_string str = if String.starts_with ~prefix:"0x" str then Bytes.of_hex_string str else str

let load_mpt_entries ~hash_keys (entries : Yojson.Safe.t) =
  let of_kv (k, v) =
    let k = hex_or_string k in
    let k = if hash_keys then U256.to_bytes_be (Crypto.keccak_256 k) else k in
    let v = Option.map hex_or_string (to_string_option v) in
    (k, Rlp.Bytes (Option.value v ~default:Bytes.empty))
  in
  match entries with
  | `Assoc kv -> List.map of_kv kv
  | `List kv -> List.map (fun[@warning "-8"] (`List [k; v] : t) -> of_kv (to_string k, v)) kv
  | _ -> assert false

let load_mpt_test_case ~hash_keys (name, params) =
  let entries = load_mpt_entries ~hash_keys params.$("in") in
  let root = to_string params.$("root") |> U256.of_string in
  let root' = (Mpt.make entries).root_hash in
  Alcotest.(test_case name `Quick (fun () -> check' u256 ~msg:"Root" ~expected:root ~actual:root'))

let load_mpt_test_fixtures ?(hash_keys = false) file =
  (* TODO: do something disciplined about paths *)
  let path = "../../../../third_party/tests/TrieTests/" ^ file in
  let test_cases = to_assoc (from_file ~fname:file path) |> List.map (load_mpt_test_case ~hash_keys) in
  (file, test_cases)

let () =
  let open Alcotest in
  run "Tests on MPT data structures"
    [ ( "Hex-prefix round-trip"
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
    ; load_mpt_test_fixtures ~hash_keys:true "hex_encoded_securetrie_test.json"
    ; load_mpt_test_fixtures ~hash_keys:true "trietest_secureTrie.json"
    ; load_mpt_test_fixtures ~hash_keys:true "trieanyorder_secureTrie.json"
    ; load_mpt_test_fixtures "trietest.json"
    ; load_mpt_test_fixtures "trieanyorder.json" ]
