open Monad_lib
open Test_utils.Utils
open QCheck2

let test_encoding obj encoded =
  Alcotest.(
    test_case
      (Format.sprintf "Encode %s" (Rlp.to_string obj))
      `Quick
      (fun () -> check' string ~msg:"Encoding" ~expected:encoded ~actual:Rlp.(encode obj)) )

let test_decoding encoded obj =
  Alcotest.(
    test_case
      (Format.sprintf "Decode 0x%s" (Bytes.to_hex_string encoded))
      `Quick
      (fun () -> check' rlp ~msg:"Decoding" ~expected:obj ~actual:Rlp.(decode encoded)) )

let examples =
  [ (Rlp.(Bytes "dog"), Bytes.of_chars ['\x83'; 'd'; 'o'; 'g'])
  ; ( Rlp.(List [Bytes "cat"; Bytes "dog"])
    , Bytes.of_chars ['\xc8'; '\x83'; 'c'; 'a'; 't'; '\x83'; 'd'; 'o'; 'g'] )
  ; (Rlp.(Bytes Bytes.empty), Bytes.of_chars ['\x80'])
  ; (Rlp.(Bytes (Bytes.of_chars ['\x00'])), Bytes.of_chars ['\x00'])
  ; (Rlp.(Bytes (Bytes.of_chars ['\x0f'])), Bytes.of_chars ['\x0f'])
  ; ( Rlp.(List [List []; List [List []]; List [List []; List [List []]]])
    , Bytes.of_chars ['\xc7'; '\xc0'; '\xc1'; '\xc0'; '\xc3'; '\xc0'; '\xc1'; '\xc0'] ) ]

let () =
  let open Alcotest in
  run "Unit tests on RLP encodings"
    [ ("Encoding examples", List.map (fun (obj, encoded) -> test_encoding obj encoded) examples)
    ; ("Decoding examples", List.map (fun (obj, encoded) -> test_decoding encoded obj) examples)
    ; ( "Round-trip"
      , [ check_prop ~print:Print.rlp ~name:"x = decode (encode x)" Gen.rlp (fun obj ->
              Rlp.(obj = decode (encode obj)) ) ] ) ]
