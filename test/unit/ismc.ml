open Monad_lib
open Test_utils.Utils
open Numeric
open Byte_string

let word v = U256.(to_repr ~$v)

(* Reference vectors below produced using scripts/page_commit_reference.py
   See also monad/category/execution/monad/db/test_storage_page.cpp *)
let commitments =
  [ ("slot 0", [(0, word 1)], "80218c63919cd8c68aa9a5c0117bb8b46eb02099a7ce0b47a36e7b21658cc9f9")
  ; ("slot 127", [(127, word 1)], "39a2175f8fac8fbf447383b46ff40e03673b388c05c87e50ed7b3f1a810c98d8")
  ; ( "full page"
    , List.init 128 (fun k -> (k, word (k + 1)))
    , "e5a642261a2c2dedebd68ebd42237f2210d1eee94553d677d425dc3a46c7a687" )
  ; ("slot 1", [(1, word 1)], "2319a6bc09c31c06709668fba861f15750009799edf2e6c867d4f0a88774c8a6")
  ; ( "slots 0 and 1"
    , [(0, word 1); (1, word 2)]
    , "46906319c63bef972eab21b85ebaadda0b3d1648c8cd333be15f61b7dbc96e4e" )
  ; ( "slots 1 and 2"
    , [(1, word 1); (2, word 2)]
    , "b296d2d2a298cb9c83db33a288253dbea080c104541d78ae61803b888d33da3e" ) ]

let test_commitment (name, entries, expected) =
  Alcotest.(
    test_case name `Quick (fun () ->
        check' b32 ~msg:"page commitment" ~expected:(B32.of_hex_string expected)
          ~actual:(Ismc.page_commitment entries) ) )

let test_invalid_input name expected_message entries =
  Alcotest.(
    test_case name `Quick (fun () ->
        check_raises name (Invalid_argument expected_message) (fun () ->
            ignore (Ismc.page_commitment entries) ) ) )

let () =
  Alcotest.run "MIP-8 ISMC storage commitment"
    [ ("page_commitment expected", List.map test_commitment commitments)
    ; ( "page_commitment validation"
      , [ test_invalid_input "empty page" "Ismc.page_commitment: empty page" []
        ; test_invalid_input "duplicate offset" "Ismc.page_commitment: duplicate offset"
            [(7, word 1); (7, word 2)]
        ; test_invalid_input "offset out of range" "Ismc.page_commitment: offset out of range" [(128, word 1)]
        ] ) ]
