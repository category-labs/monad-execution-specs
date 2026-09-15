open Monad_lib
open Test_utils.Utils
open Numeric
open Byte_string

let word v = U256.(to_repr ~$v)

let commitments =
  (* From page_commit_cross_check_with_reference in
     category/execution/monad/db/test_storage_page.cpp *)
  [ ("slot 0", [(0, word 1)], "80218c63919cd8c68aa9a5c0117bb8b46eb02099a7ce0b47a36e7b21658cc9f9")
  ; ("slot 127", [(127, word 1)], "39a2175f8fac8fbf447383b46ff40e03673b388c05c87e50ed7b3f1a810c98d8")
  ; ( "full page"
    , List.init 128 (fun k -> (k, word (k + 1)))
    , "e5a642261a2c2dedebd68ebd42237f2210d1eee94553d677d425dc3a46c7a687" ) ]

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
      , [ test_invalid_input "empty page" "ISMC.page_commitment: empty page" []
        ; test_invalid_input "duplicate offset" "ISMC.page_commitment: duplicate offset"
            [(7, word 1); (7, word 2)]
        ; test_invalid_input "offset out of range" "ISMC.page_commitment: offset out of range" [(128, word 1)]
        ] ) ]
