open Monad_lib
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
  let map = Mpt.Nibbles.Map.of_list entries in
  let trie = Mpt.Trie.of_seq (List.to_seq entries) in
  Mpt.Nibbles.Map.to_seq map
  |> Seq.for_all (fun (k, v) ->
      match Mpt.Trie.find k trie with
      | None ->
          Format.printf "Key %s not found" (Mpt.Nibbles.to_hex_string k) ;
          false
      | Some v' ->
          if v = v' then true
          else (
            Format.printf "Entries for %s contain different values\nv: %s\nv': %s\n"
              (Mpt.Nibbles.to_hex_string k) (Rlp.to_string v) (Rlp.to_string v') ;
            false ) )

let round_trip_patricia_ok entries =
  let map = Mpt.Nibbles.Map.of_list entries in
  let trie = Mpt.Trie.of_seq (List.to_seq entries) in
  let pt = Mpt.PatriciaTrie.of_trie trie in
  Mpt.Nibbles.Map.to_seq map
  |> Seq.for_all (fun (k, v) -> match Mpt.PatriciaTrie.find k pt with None -> false | Some v' -> v = v')

let round_trip_mpt_ok entries =
  let map = Mpt.Nibbles.Map.of_list entries in
  let mpt = Mpt.(List.to_seq entries |> Trie.of_seq |> PatriciaTrie.of_trie |> of_patricia) in
  Mpt.Nibbles.Map.to_seq map
  |> Seq.for_all (fun (k, v) -> match Mpt.find k mpt with None -> false | Some v' -> v = v')

let round_trip_hp_ok (nibbles, flag) =
  let hp = Mpt.Nibbles.hex_prefix_encode nibbles flag in
  let nibbles', flag' = Mpt.Nibbles.hex_prefix_decode hp in
  nibbles = nibbles' && flag = flag'

let () =
  let open Alcotest in
  run "Unit tests on MPT data structures"
    [ ( "Hex-prefix round-trip"
      , [ check_prop
            ~print:Print.(pair byte_string bool)
            ~name:"round_trip_hp_ok ns"
            Gen.(pair gen_nibbles bool)
            round_trip_hp_ok ] )
    ; ( "Trie round-trip"
      , [check_prop ~print:print_entries ~name:"round_trip_trie_ok entries" gen_entries round_trip_trie_ok] )
    ; ( "Patricia round-trip"
      , [ check_prop ~print:print_entries ~name:"round_trip_patricia_ok entries" gen_entries
            round_trip_patricia_ok ] )
    ; ( "MPT round-trip"
      , [ check_prop ~print:print_entries ~name:"round_trip_mpt_ok entries" gen_entries
            round_trip_mpt_ok ] )
    ]

