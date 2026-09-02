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

(** [Rlp.decode] currently signals failure by raising (Assert_failure, Invalid_argument, Z.Overflow)
    rather than returning a result, so any exception counts as a rejection here. Written this way the
    tests below stay valid if the decoder is later changed to return a proper [result]. *)
let decode_opt (bs : Bytes.t) : Rlp.t option = try Some Rlp.(decode bs) with _ -> None

(* RLP is a canonical encoding: every value has exactly one valid byte string (YP App. B). A decoder
   must therefore never accept a byte string that its own encoder would not have produced. If it does,
   two distinct byte strings decode to the same value -- which makes transaction hashes malleable, and
   makes any two clients that disagree about which spellings are acceptable disagree about block
   validity. *)
let is_canonical (bs : Bytes.t) : bool =
  match decode_opt bs with None -> true | Some obj -> Bytes.(Rlp.encode obj = bs)

(* Non-canonical spellings: each of these decodes successfully, but re-encoding the result produces a
   different byte string, so the decoder is not a bijection. Every one must be rejected. *)
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
        match decode_opt encoded with
        | None -> ()
        | Some obj ->
            failf "Accepted non-canonical encoding 0x%s as %s, which re-encodes to 0x%s" hex
              (Rlp.to_string obj)
              Bytes.(to_hex_string Rlp.(encode obj)) ) )

let () =
  let open Alcotest in
  run "Unit tests on RLP encodings"
    [ ("Encoding examples", List.map (fun (obj, encoded) -> test_encoding obj encoded) examples)
    ; ("Decoding examples", List.map (fun (obj, encoded) -> test_decoding encoded obj) examples)
    ; ("Non-canonical encodings", List.map test_non_canonical non_canonical_encodings)
    ; ( "Round-trip"
      , [ check_prop ~print:Print.rlp ~name:"x = decode (encode x)" (Gen.rlp ~nonempty:false) (fun obj ->
              Rlp.(obj = decode (encode obj)) ) ] )
    ; ( "Canonicality"
      , [ check_prop ~print:Print.byte_string ~name:"b = encode (decode b), for every accepted b"
            Gen.(string_size ~gen:(map Char.chr (int_range 0 255)) (int_range 0 12))
            is_canonical ] ) ]
