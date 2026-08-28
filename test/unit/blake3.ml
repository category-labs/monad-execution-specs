open Monad_lib
open Test_utils.Utils
open Byte_string

(* Official BLAKE3 test vectors, from
   https://github.com/BLAKE3-team/BLAKE3/blob/master/test_vectors/test_vectors.json.
   The input of each case is [input_len] bytes of the repeating pattern 0, 1, ..., 250, 0, 1, ...;
   the expected output is the first 32 bytes of the extended output in the given mode. Lengths span
   the block-boundary edge cases of a single 1024-byte chunk. *)

let input len = Bytes.init len (fun i -> Char.chr (i mod 251))

let derive_key_context = "BLAKE3 2019-12-27 16:29:52 test vectors context"

let hash_vectors =
  [ (0, "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262")
  ; (1, "2d3adedff11b61f14c886e35afa036736dcd87a74d27b5c1510225d0f592e213")
  ; (2, "7b7015bb92cf0b318037702a6cdd81dee41224f734684c2c122cd6359cb1ee63")
  ; (3, "e1be4d7a8ab5560aa4199eea339849ba8e293d55ca0a81006726d184519e647f")
  ; (4, "f30f5ab28fe047904037f77b6da4fea1e27241c5d132638d8bedce9d40494f32")
  ; (63, "e9bc37a594daad83be9470df7f7b3798297c3d834ce80ba85d6e207627b7db7b")
  ; (64, "4eed7141ea4a5cd4b788606bd23f46e212af9cacebacdc7d1f4c6dc7f2511b98")
  ; (65, "de1e5fa0be70df6d2be8fffd0e99ceaa8eb6e8c93a63f2d8d1c30ecb6b263dee")
  ; (127, "d81293fda863f008c09e92fc382a81f5a0b4a1251cba1634016a0f86a6bd640d")
  ; (128, "f17e570564b26578c33bb7f44643f539624b05df1a76c81f30acd548c44b45ef")
  ; (1023, "10108970eeda3eb932baac1428c7a2163b0e924c9a9e25b35bba72b28f70bd11")
  ; (1024, "42214739f095a406f3fc83deb889744ac00df831c10daa55189b5d121c855af7") ]

let derive_key_vectors =
  [ (0, "2cc39783c223154fea8dfb7c1b1660f2ac2dcbd1c1de8277b0b0dd39b7e50d7d")
  ; (1, "b3e2e340a117a499c6cf2398a19ee0d29cca2bb7404c73063382693bf66cb06c")
  ; (2, "1f166565a7df0098ee65922d7fea425fb18b9943f19d6161e2d17939356168e6")
  ; (3, "440aba35cb006b61fc17c0529255de438efc06a8c9ebf3f2ddac3b5a86705797")
  ; (4, "f46085c8190d69022369ce1a18880e9b369c135eb93f3c63550d3e7630e91060")
  ; (63, "b6451e30b953c206e34644c6803724e9d2725e0893039cfc49584f991f451af3")
  ; (64, "a5c4a7053fa86b64746d4bb688d06ad1f02a18fce9afd3e818fefaa7126bf73e")
  ; (65, "51fd05c3c1cfbc8ed67d139ad76f5cf8236cd2acd26627a30c104dfd9d3ff8a8")
  ; (127, "c91c090ceee3a3ac81902da31838012625bbcd73fcb92e7d7e56f78deba4f0c3")
  ; (128, "81720f34452f58a0120a58b6b4608384b5c51d11f39ce97161a0c0e442ca0225")
  ; (1023, "74a16c1c3d44368a86e1ca6df64be6a2f64cce8f09220787450722d85725dea5")
  ; (1024, "7356cd7720d5b66b6d0697eb3177d9f8d73a4a5c5e968896eb6a689684302706") ]

let test_hash (len, expected) =
  Alcotest.(
    test_case (Format.sprintf "hash, input length %d" len) `Quick (fun () ->
        check' b32 ~msg:"hash" ~expected:(B32.of_hex_string expected) ~actual:(Blake3.hash (input len)) ) )

let test_derive_key (len, expected) =
  Alcotest.(
    test_case (Format.sprintf "derive_key, input length %d" len) `Quick (fun () ->
        check' b32 ~msg:"derive_key"
          ~expected:(B32.of_hex_string expected)
          ~actual:(Blake3.derive_key ~context:derive_key_context (input len)) ) )

let test_multi_chunk_rejected =
  Alcotest.(
    test_case "inputs beyond a single chunk are rejected" `Quick (fun () ->
        check_raises "hash of 1025 bytes"
          (Invalid_argument "Blake3: only single-chunk inputs (at most 1024 bytes) are supported")
          (fun () -> ignore (Blake3.hash (input 1025))) ) )

let () =
  Alcotest.run "BLAKE3"
    [ ("hash", List.map test_hash hash_vectors @ [test_multi_chunk_rejected])
    ; ("derive_key", List.map test_derive_key derive_key_vectors) ]
