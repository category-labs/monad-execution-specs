open Monad_lib
open Test_utils.Utils
open Byte_string

(* Official BLAKE3 test vectors, from
   https://github.com/BLAKE3-team/BLAKE3/blob/master/test_vectors/test_vectors.json.
   The input of each case is [input_len] bytes of the repeating sequence 0, 1, ..., 250, 0, 1, ...
   and the expected output is the first 32 bytes of the extended output. *)

let input len = Bytes.init len (fun i -> Char.chr (i mod 251))

(* let derive_key_context = "BLAKE3 2019-12-27 16:29:52 test vectors context" *)

let hash_vectors =
  [ (0, "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262")
  ; (1, "2d3adedff11b61f14c886e35afa036736dcd87a74d27b5c1510225d0f592e213")
  ; (2, "7b7015bb92cf0b318037702a6cdd81dee41224f734684c2c122cd6359cb1ee63")
  ; (3, "e1be4d7a8ab5560aa4199eea339849ba8e293d55ca0a81006726d184519e647f")
  ; (4, "f30f5ab28fe047904037f77b6da4fea1e27241c5d132638d8bedce9d40494f32")
  ; (5, "b40b44dfd97e7a84a996a91af8b85188c66c126940ba7aad2e7ae6b385402aa2")
  ; (6, "06c4e8ffb6872fad96f9aaca5eee1553eb62aed0ad7198cef42e87f6a616c844")
  ; (7, "3f8770f387faad08faa9d8414e9f449ac68e6ff0417f673f602a646a891419fe")
  ; (8, "2351207d04fc16ade43ccab08600939c7c1fa70a5c0aaca76063d04c3228eaeb")
  ; (63, "e9bc37a594daad83be9470df7f7b3798297c3d834ce80ba85d6e207627b7db7b")
  ; (64, "4eed7141ea4a5cd4b788606bd23f46e212af9cacebacdc7d1f4c6dc7f2511b98")
  ; (65, "de1e5fa0be70df6d2be8fffd0e99ceaa8eb6e8c93a63f2d8d1c30ecb6b263dee")
  ; (127, "d81293fda863f008c09e92fc382a81f5a0b4a1251cba1634016a0f86a6bd640d")
  ; (128, "f17e570564b26578c33bb7f44643f539624b05df1a76c81f30acd548c44b45ef")
  ; (129, "683aaae9f3c5ba37eaaf072aed0f9e30bac0865137bae68b1fde4ca2aebdcb12")
  ; (1023, "10108970eeda3eb932baac1428c7a2163b0e924c9a9e25b35bba72b28f70bd11")
  ; (1024, "42214739f095a406f3fc83deb889744ac00df831c10daa55189b5d121c855af7") ]

let test_hash (len, expected) =
  Alcotest.(
    test_case (Format.sprintf "hash, input length %d" len) `Quick (fun () ->
        check' b32 ~msg:"hash" ~expected:(B32.of_hex_string expected) ~actual:(Crypto.Blake3.hash (input len)) ) )

let () = Alcotest.run "BLAKE3" [("hash", List.map test_hash hash_vectors)]
