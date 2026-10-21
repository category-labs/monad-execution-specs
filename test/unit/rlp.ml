open Monad_lib
open Monad_lib.Byte_string

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
      (fun () ->
        match Rlp.decode encoded with
        | Ok actual -> check' rlp ~msg:"Decoding" ~expected:obj ~actual
        | Error _ -> fail "Valid encoding was rejected" ) )

let examples =
  [ (Rlp.(Bytes "dog"), Bytes.of_chars ['\x83'; 'd'; 'o'; 'g'])
  ; ( Rlp.(List [Bytes "cat"; Bytes "dog"])
    , Bytes.of_chars ['\xc8'; '\x83'; 'c'; 'a'; 't'; '\x83'; 'd'; 'o'; 'g'] )
  ; (Rlp.(Bytes Bytes.empty), Bytes.of_chars ['\x80'])
  ; (Rlp.(Bytes (Bytes.of_chars ['\x00'])), Bytes.of_chars ['\x00'])
  ; (Rlp.(Bytes (Bytes.of_chars ['\x0f'])), Bytes.of_chars ['\x0f'])
  ; ( Rlp.(List [List []; List [List []]; List [List []; List [List []]]])
    , Bytes.of_chars ['\xc7'; '\xc0'; '\xc1'; '\xc0'; '\xc3'; '\xc0'; '\xc1'; '\xc0'] ) ]

(* RLP is a canonical encoding: every value has exactly one valid byte string (YP App. B). A decoder
   must therefore never accept a byte string that its own encoder would not have produced. If it does,
   two distinct byte strings decode to the same value -- which makes transaction hashes malleable, and
   makes any two clients that disagree about which spellings are acceptable disagree about block
   validity. *)
let is_canonical (bs : Bytes.t) : bool =
  match Rlp.decode bs with Error _ -> true | Ok obj -> Bytes.(Rlp.encode obj = bs)

(* Non-canonical spellings that must be rejected: accepting one would allow the same object to
   have more than one encoding. *)
let non_canonical_encodings =
  [ ("single byte 0x00", "8100")
  ; ("single byte 0x01", "8101")
  ; ("single byte 0x7f", "817f")
  ; ("long form, 1-byte payload", "b801ff")
  ; ("long form, empty payload", "b800")
  ; ("leading zero in length", "b90001ff")
  ; ("list, non-optimal length", "f80100") ]

let test_non_canonical (name, hex) =
  let encoded = Bytes.of_hex_string hex in
  Alcotest.(
    test_case (Format.sprintf "%s (0x%s)" name hex) `Quick (fun () ->
        match Rlp.decode encoded with
        | Error Rlp.Non_canonical -> ()
        | Error _ -> fail "Wrong error for noncanonical input"
        | Ok obj ->
            failf "Accepted non-canonical encoding 0x%s as %s, which re-encodes to 0x%s" hex
              (Rlp.to_string obj)
              Bytes.(to_hex_string Rlp.(encode obj)) ) )

let error_name = function
  | Rlp.Empty_input -> "empty input"
  | Truncated_input -> "truncated input"
  | Non_canonical -> "noncanonical input"
  | Length_overflow -> "length overflow"
  | Trailing_bytes -> "trailing bytes"

let test_error (name, hex, expected) =
  Alcotest.test_case name `Quick (fun () ->
      match Rlp.decode (Bytes.of_hex_string hex) with
      | Error actual -> Alcotest.(check string) "Error" (error_name expected) (error_name actual)
      | Ok _ -> Alcotest.fail "Malformed input was accepted" )

let malformed_encodings =
  Rlp.
    [ ("empty", "", Empty_input)
    ; ("missing single byte", "81", Truncated_input)
    ; ("truncated string", "836162", Truncated_input)
    ; ("truncated list", "c1", Truncated_input)
    ; ("truncated nested list", "c1c1", Truncated_input)
    ; ("nested noncanonical byte", "c28100", Non_canonical)
    ; ("missing long string length", "b8", Truncated_input)
    ; ("missing long list length", "f8", Truncated_input)
    ; ("truncated length field", "b900", Truncated_input)
    ; ("missing long string payload", "b838", Truncated_input)
    ; ("missing long list payload", "f838", Truncated_input)
    ; ("unrepresentable string length", "bfffffffffffffffff", Length_overflow)
    ; ("unrepresentable list length", "ffffffffffffffffff", Length_overflow)
    ; ("trailing byte", "8080", Trailing_bytes)
    ; ("malformed trailing byte", "80c1", Trailing_bytes) ]

let test_stream () =
  let encoded = Rlp.encode (Rlp.Bytes "dog") ^ Rlp.encode (Rlp.List []) in
  ( match Rlp.decode_first encoded with
  | Ok (first, rest) ->
      Alcotest.(check rlp) "First object" (Rlp.Bytes "dog") first ;
      Alcotest.(check string) "Remainder" (Rlp.encode (Rlp.List [])) rest
  | Error _ -> Alcotest.fail "Valid stream prefix was rejected" ) ;
  ( match Rlp.decode_all encoded with
  | Ok objects -> Alcotest.(check (list rlp)) "Objects" [Rlp.Bytes "dog"; Rlp.List []] objects
  | Error _ -> Alcotest.fail "Valid stream was rejected" ) ;
  (match Rlp.decode_all Bytes.empty with Ok [] -> () | _ -> Alcotest.fail "Empty stream must succeed") ;
  match Rlp.decode_all (encoded ^ "\xc1") with
  | Error Rlp.Truncated_input -> ()
  | _ -> Alcotest.fail "Stream must propagate a later decoding error"

let test_long_payload size =
  let obj = Rlp.Bytes (String.make size 'a') in
  test_decoding (Rlp.encode obj) obj

let test_long_list size =
  let obj = Rlp.List (List.init size (fun _ -> Rlp.Bytes "")) in
  test_decoding (Rlp.encode obj) obj

let test_integer_lengths () =
  List.iter
    (fun (encoded, expected) ->
      match Rlp.decode_be encoded with
      | Ok actual -> Alcotest.(check string) "Integer" (Z.to_string expected) (Z.to_string actual)
      | Error _ -> Alcotest.fail "Minimal integer encoding was rejected" )
    [("", Z.zero); ("\x01", Z.one); ("\x01\x00", Z.of_int 256)] ;
  List.iter
    (fun encoded ->
      match Rlp.decode_be encoded with
      | Error Rlp.Non_canonical -> ()
      | _ -> Alcotest.fail "Leading zero was accepted" )
    ["\x00"; "\x00\x01"]

let decode_first_progress bs =
  match Rlp.decode_first bs with
  | Error _ -> true
  | Ok (obj, rest) -> Bytes.length rest < Bytes.length bs && Bytes.equal (Rlp.encode obj ^ rest) bs

let () =
  let open Alcotest in
  run "Unit tests on RLP encodings"
    [ ("Encoding examples", List.map (fun (obj, encoded) -> test_encoding obj encoded) examples)
    ; ("Decoding examples", List.map (fun (obj, encoded) -> test_decoding encoded obj) examples)
    ; ("Non-canonical encodings", List.map test_non_canonical non_canonical_encodings)
    ; ("Malformed encodings", List.map test_error malformed_encodings)
    ; ("Streams", [test_case "Prefix, remainder, and error propagation" `Quick test_stream])
    ; ("Length boundaries", List.map test_long_payload [0; 1; 55; 56; 255; 256])
    ; ("List length boundaries", List.map test_long_list [55; 56; 255; 256])
    ; ("Integer lengths", [test_case "Minimal big-endian representation" `Quick test_integer_lengths])
    ; ( "Streaming progress"
      , [ check_prop ~print:Print.byte_string ~name:"accepted prefixes consume bytes and preserve the suffix"
            Gen.(string_size ~gen:uint8 (int_range 0 64))
            decode_first_progress
        ; check_prop
            ~print:Print.(pair rlp rlp)
            ~name:"decode_first stops after the first object"
            Gen.(pair (rlp ~nonempty:false) (rlp ~nonempty:false))
            (fun (first, second) ->
              let suffix = Rlp.encode second in
              match Rlp.decode_first (Rlp.encode first ^ suffix) with
              | Error _ -> false
              | Ok (decoded, rest) -> Rlp.equal decoded first && Bytes.equal rest suffix ) ] )
    ; ( "Round-trip"
      , [ check_prop ~print:Print.rlp ~name:"x = decode (encode x)" (Gen.rlp ~nonempty:false) (fun obj ->
              match Rlp.decode (Rlp.encode obj) with Ok actual -> Rlp.(obj = actual) | Error _ -> false ) ] )
    ; ( "Canonicality"
      , [ check_prop ~print:Print.byte_string ~name:"b = encode (decode b), for every accepted b"
            Gen.(string_size ~gen:(map Char.chr (int_range 0 255)) (int_range 0 12))
            is_canonical ] ) ]
