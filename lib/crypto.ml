(** Cryptographic functions.

    Bindings to external libraries (keccak, secp256k1, SHA-256, RIPEMD-160)
    and native implementations (BLAKE2b, BLAKE3). *)

open Numeric
open Byte_string

(** [keccak_256 bytes] computes the Keccak-256 digest of a byte array. *)
let keccak_256 (input : Bytes.t) : B32.t =
  let bytes = Digestif.KECCAK_256.(to_raw_string (digest_string input)) in
  (* Never fails as Keccak-256 is guaranteed to produce 32 bytes. *)
  Byte_string.B32.of_bytes_exn bytes

(** The Keccak-256 encoding of the empty byte array. *)
let keccak_256_empty = keccak_256 Bytes.empty

let secp256k1b = U256.(~$7)
let secp256k1p = U256.(~@"0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F")

(* YP (315) *)
let secp256k1n = U256.(~@"0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141")

let context = Libsecp256k1.External.Context.create ()

type signature = {r : U256.t; s : U256.t; y_parity : U8.t}

(* The spec only ever verifies signatures, so the signing-related components of YP appendix F are absent:
   YP (309), YP (310), YP (316), YP (319), YP (320), YP (325). *)

(** [ecrecover sign hash] recovers the address that signed a message from the signature [sign] and the signed
    hash [hash]. This is equivalent to ECDSARECOVER (YP (311)) followed by sender address extraction
    (YP (323)). *)
let ecrecover {r; s; y_parity} (msg_hash : B32.t) : B20.t option =
  Option.(
    let$ () = ensure U8.(y_parity = zero || y_parity = one) in
    let is_square =
      U256.(
        one
        = exp_mod
            (exp_mod r ~$3 ~modulo:secp256k1p + secp256k1b)
            ((secp256k1p - ~$1) / ~$2)
            ~modulo:secp256k1p )
    in
    let$ () = ensure is_square in
    Libsecp256k1.External.(
      let r = U256.to_repr r in
      let s = U256.to_repr s in
      let y_parity = U8.to_repr y_parity in
      let signature_i = function
        | i when i < 32 -> B32.(r.$(i))
        | i when i < 64 -> B32.(s.$(i - 32))
        | _ -> U8.Repr.(y_parity.$(0))
      in
      let$ signature =
        Result.to_option (Sign.read_recoverable context (Bigstring.init Sign.recoverable_bytes signature_i))
      in
      let$ result_bigstring =
        (msg_hash :> string)
        |> Bigstring.of_string
        |> Sign.recover context ~signature
        |> Result.to_option
        |> Option.map (Key.to_bytes ~compress:false context)
      in
      let public_key_i i = result_bigstring.{i + 1} in
      let public_key = Bytes.init 64 public_key_i in
      return (B20.of_bytes32_truncating (keccak_256 public_key)) ) )

(* YP (229) *)
let sha_256 (bs : Bytes.t) : B32.t = B32.of_bytes_exn Digestif.SHA256.(to_raw_string (digest_string bs))

(* YP (230) *)
let ripemd_160 (bs : Bytes.t) : B20.t = B20.of_bytes_exn Digestif.RMD160.(to_raw_string (digest_string bs))

(* For performance, blake2 uses native Uint64.t instead of the Zarith-backed U64.t. *)
(* RFC 7693 §2.1 *)
let blake2b_iv =
  [| 0x6A09E667F3BCC908L
   ; 0xBB67AE8584CAA73BL
   ; 0x3C6EF372FE94F82BL
   ; 0xA54FF53A5F1D36F1L
   ; 0x510E527FADE682D1L
   ; 0x9B05688C2B3E6C1FL
   ; 0x1F83D9ABFB41BD6BL
   ; 0x5BE0CD19137E2179L |]

(* RFC 7693 §2.7 *)
let blake2b_sigma =
  [| [|0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15|]
   ; [|14; 10; 4; 8; 9; 15; 13; 6; 1; 12; 0; 2; 11; 7; 5; 3|]
   ; [|11; 8; 12; 0; 5; 2; 15; 13; 10; 14; 3; 6; 7; 1; 9; 4|]
   ; [|7; 9; 3; 1; 13; 12; 11; 14; 2; 6; 5; 10; 4; 0; 15; 8|]
   ; [|9; 0; 5; 7; 2; 4; 10; 15; 14; 1; 11; 12; 6; 8; 3; 13|]
   ; [|2; 12; 6; 10; 0; 11; 8; 3; 4; 13; 7; 5; 15; 14; 1; 9|]
   ; [|12; 5; 1; 15; 14; 13; 4; 10; 0; 7; 6; 3; 9; 2; 8; 11|]
   ; [|13; 11; 7; 14; 12; 1; 3; 9; 5; 0; 15; 4; 8; 6; 2; 10|]
   ; [|6; 15; 14; 9; 11; 3; 0; 8; 12; 2; 13; 7; 1; 4; 10; 5|]
   ; [|10; 2; 8; 4; 7; 6; 1; 5; 15; 11; 9; 14; 3; 12; 13; 0|] |]

let rotr64 x (n : int) = Uint64.(logor (shift_right x n) (shift_left x Stdlib.(64 - n)))

(** [blake2f ~rounds ~h ~m ~t0 ~t1 ~final_block] computes [rounds] rounds of the
    BLAKE2b compression function F (RFC 7693 §3.2) and returns the updated hash state.
    Unfortunately, this is not exposed by any off-the-shelf library. *)
let blake2f ~rounds ~(h : Uint64.t Iarray.t) ~(m : Uint64.t Iarray.t) ~t0 ~t1 ~final_block =
  let open Uint64 in
  let ( .$() ) = Iarray.get in
  let v = Array.append (Iarray.to_array h) blake2b_iv in
  v.(12) <- logxor v.(12) t0 ;
  v.(13) <- logxor v.(13) t1 ;
  if final_block then v.(14) <- lognot v.(14) ;
  let g a b c d x y =
    v.(a) <- v.(a) + v.(b) + x ;
    v.(d) <- rotr64 (logxor v.(d) v.(a)) 32 ;
    v.(c) <- v.(c) + v.(d) ;
    v.(b) <- rotr64 (logxor v.(b) v.(c)) 24 ;
    v.(a) <- v.(a) + v.(b) + y ;
    v.(d) <- rotr64 (logxor v.(d) v.(a)) 16 ;
    v.(c) <- v.(c) + v.(d) ;
    v.(b) <- rotr64 (logxor v.(b) v.(c)) 63
  in
  for i = 0 to Stdlib.(rounds - 1) do
    let s = blake2b_sigma.(i mod 10) in
    g 0 4 8 12 m.$(s.(0)) m.$(s.(1)) ;
    g 1 5 9 13 m.$(s.(2)) m.$(s.(3)) ;
    g 2 6 10 14 m.$(s.(4)) m.$(s.(5)) ;
    g 3 7 11 15 m.$(s.(6)) m.$(s.(7)) ;
    g 0 5 10 15 m.$(s.(8)) m.$(s.(9)) ;
    g 1 6 11 12 m.$(s.(10)) m.$(s.(11)) ;
    g 2 7 8 13 m.$(s.(12)) m.$(s.(13)) ;
    g 3 4 9 14 m.$(s.(14)) m.$(s.(15))
  done ;
  Iarray.init 8 (fun i -> logxor (logxor h.$(i) v.(i)) v.(Stdlib.(i + 8)))

(** OCaml implementation of the BLAKE3 function based on the reference implementation
    {:https://github.com/BLAKE3-team/BLAKE3/blob/master/reference_impl/reference_impl.rs}.
    Only single-chunk inputs (up to 1024 bytes) are supported. *)
module Blake3 = struct
  let chunk_start = 0x01
  let chunk_end = 0x02
  let parent = 0x04
  let root = 0x08
  let keyed_hash = 0x10
  let derive_key_context = 0x20
  let derive_key_material = 0x40

  (* To keep Ocaml's 63-bit int within 32-bits. *)
  let mask32 = 0xFFFFFFFF

  (* Little-endian decoding of the 32-bit word at byte offset [i]. *)
  let word32_at (bs : Bytes.t) (i : int) =
    Char.code bs.[i]
    lor (Char.code bs.[i + 1] lsl 8)
    lor (Char.code bs.[i + 2] lsl 16)
    lor (Char.code bs.[i + 3] lsl 24)

  let words_of_b32 (bs : B32.t) = Array.init 8 (fun i -> word32_at (B32.to_bytes bs) (4 * i))
  let b32_of_words (ws : int iarray) =
    B32.init (fun i -> Char.chr ((Iarray.get ws (i / 4) lsr (8 * (i mod 4))) land 0xFF))

  let iv_words : int iarray =
    [|0x6A09E667; 0xBB67AE85; 0x3C6EF372; 0xA54FF53A; 0x510E527F; 0x9B05688C; 0x1F83D9AB; 0x5BE0CD19|]

  let iv = b32_of_words iv_words

  let msg_permutation = [|2; 6; 3; 10; 7; 0; 4; 13; 1; 11; 12; 5; 9; 14; 15; 8|]

  let rotr32 x (n : int) = (x lsr n) lor (x lsl (32 - n)) land mask32

  (* The mixing function, G, which mixes either a column or a diagonal. *)
  let g v a b c d x y =
    v.(a) <- (v.(a) + v.(b) + x) land mask32 ;
    v.(d) <- rotr32 (v.(d) lxor v.(a)) 16 ;
    v.(c) <- (v.(c) + v.(d)) land mask32 ;
    v.(b) <- rotr32 (v.(b) lxor v.(c)) 12 ;
    v.(a) <- (v.(a) + v.(b) + y) land mask32 ;
    v.(d) <- rotr32 (v.(d) lxor v.(a)) 8 ;
    v.(c) <- (v.(c) + v.(d)) land mask32 ;
    v.(b) <- rotr32 (v.(b) lxor v.(c)) 7

  let round v m =
    (* Mix the columns. *)
    g v 0 4 8 12 m.(0) m.(1) ;
    g v 1 5 9 13 m.(2) m.(3) ;
    g v 2 6 10 14 m.(4) m.(5) ;
    g v 3 7 11 15 m.(6) m.(7) ;
    (* Mix the diagonals. *)
    g v 0 5 10 15 m.(8) m.(9) ;
    g v 1 6 11 12 m.(10) m.(11) ;
    g v 2 7 8 13 m.(12) m.(13) ;
    g v 3 4 9 14 m.(14) m.(15)

  (** BLAKE3 compression function. *)
  let compress (cv : B32.t) (block : Bytes.t) ~(counter : int) ~(block_len : int) ~(flags : int) : B32.t =
    assert (Bytes.length block = 64) ;
    let m = ref (Array.init 16 (fun i -> word32_at block (4 * i))) in
    let v =
      Array.append (words_of_b32 cv)
        [| Iarray.get iv_words 0
         ; Iarray.get iv_words 1
         ; Iarray.get iv_words 2
         ; Iarray.get iv_words 3
         ; counter land mask32
         ; (counter lsr 32) land mask32
         ; block_len
         ; flags |]
    in
    for round_number = 0 to 6 do
      round v !m ;
      if round_number < 6 then m := Array.init 16 (fun i -> !m.(msg_permutation.(i)))
    done ;
    b32_of_words (Iarray.init 8 (fun i -> v.(i) lxor v.(i + 8)))

  (* Hash [input] as a single root chunk keyed by [key]: chunk counter and output counter are both zero,
     and the final block carries the [root] flag. *)
  let hash_single_chunk ~(key : B32.t) ~(base_flags : int) (input : Bytes.t) : B32.t =
    assert (Bytes.length input <= 1024) ;
    let number_of_blocks = max 1 ((Bytes.length input + 63) / 64) in
    let rec go cv i =
      let last = i = number_of_blocks - 1 in
      let block = Bytes.sub_with_zero_padding input (i * 64) 64 in
      let block_len = if last then Bytes.length input - (i * 64) else 64 in
      let flags =
        base_flags lor (if i = 0 then chunk_start else 0) lor if last then chunk_end lor root else 0
      in
      let cv = compress cv block ~counter:0 ~block_len ~flags in
      if last then cv else go cv (i + 1)
    in
    go key 0

  (** BLAKE3 of [input] in the basic unkeyed hash mode. *)
  let hash (input : Bytes.t) : B32.t = hash_single_chunk ~key:iv ~base_flags:0 input
end
