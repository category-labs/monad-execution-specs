(** Bindings to cryptographic functions in external libraries. *)

open Numeric
open Byte_string

external blake3_hash : string -> string = "caml_blake3"

let blake3 (input : Bytes.t) : B32.t = B32.of_bytes_exn (blake3_hash input)

(** [keccak_256 bytes] computes the Keccak-256 digest of a byte array. *)
let keccak_256 (input : Bytes.t) : B32.t =
  let bytes = Digestif.KECCAK_256.(to_raw_string (digest_string input)) in
  (* Never fails as Keccak-256 is guaranteed to produce 32 bytes. *)
  Byte_string.B32.of_bytes_exn bytes

(** The Keccak-256 encoding of the empty byte array. *)
let keccak_256_empty = keccak_256 Bytes.empty

let secp256k1b = U256.(~$7)
let secp256k1p = U256.(~@"0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F")
let secp256k1n = U256.(~@"0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141")

let context = Libsecp256k1.External.Context.create ()

type signature = {r : U256.t; s : U256.t; y_parity : U8.t}

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

module Secp = struct
  open Libsecp256k1.External
  type sk = Key.secret Key.t
  type pk = Key.public Key.t
  type signature = Sign.plain Sign.t

  let sk_of_bytes (sk : B32.t) : sk option =
    Result.to_option (Key.read_sk context (Bigstring.of_string (B32.to_bytes sk)))
  let sk_to_bytes (sk : sk) : B32.t =
    Bigstring.to_string (Key.to_bytes context ~compress:false sk) |> B32.of_bytes_exn

  let pk_of_bytes (pk : B33.t) : pk option =
    Result.to_option (Key.read_pk context (Bigstring.of_string (B33.to_bytes pk)))
  let pk_to_bytes (pk : pk) : B33.t =
    Bigstring.to_string (Key.to_bytes context ~compress:true pk) |> B33.of_bytes_exn

  let signature_of_bytes (signature : Bytes.t) : signature option =
    Result.to_option (Sign.read context (Bigstring.of_string signature))
  let signature_to_bytes (signature : signature) : Bytes.t =
    Bigstring.to_string (Sign.to_bytes context signature)

  let sign (sk : sk) (msg : Bytes.t) : signature =
    let digest = Bigstring.of_string (B32.to_bytes (blake3 msg)) in
    Sign.sign_exn context ~sk digest

  let verify (pk : pk) ~(msg : Bytes.t) ~(signature : signature) : bool =
    let digest = Bigstring.of_string (B32.to_bytes (blake3 msg)) in
    Sign.verify_exn context ~pk ~msg:digest ~signature

  let gen_keypair (secret : B32.t) : pk * sk =
    let sk = Key.read_sk_exn context (Bigstring.of_string (B32.to_bytes secret)) in
    let pk = Key.neuterize_exn context sk in
    (pk, sk)

  let address_of_pubkey (pk : pk) : B20.t =
    let uncompressed = Key.to_bytes ~compress:false context pk in
    let public_key = Bytes.init 64 (fun i -> Bigstring.get uncompressed (i + 1)) in
    B20.of_bytes32_truncating (keccak_256 public_key)
end

module Bls = struct
  open Bls12_381_signature
  type nonrec sk = sk
  type pk = MinPk.pk
  type signature = MinPk.signature

  let sk_of_secret (secret : B32.t) : sk = generate_sk (Bytes.to_bytes (B32.to_bytes secret))
  let sk_of_bytes (sk : B32.t) : sk option = sk_of_bytes_opt (Bytes.to_bytes (B32.to_bytes sk))
  let sk_to_bytes (sk : sk) : B32.t = sk_to_bytes sk |> Stdlib.Bytes.to_string |> B32.of_bytes_exn

  let pk_of_bytes (pk : B48.t) : pk option = MinPk.pk_of_bytes_opt (Bytes.to_bytes (B48.to_bytes pk))
  let pk_to_bytes (pk : pk) : B48.t = MinPk.pk_to_bytes pk |> Stdlib.Bytes.to_string |> B48.of_bytes_exn

  let signature_of_bytes (signature : Bytes.t) : signature option =
    MinPk.signature_of_bytes_opt (Bytes.to_bytes signature)
  let signature_to_bytes (signature : signature) : Bytes.t =
    MinPk.signature_to_bytes signature |> Stdlib.Bytes.to_string

  let sign (sk : sk) (msg : Bytes.t) : signature =
    let msg = Bytes.to_bytes msg in
    MinPk.Pop.sign sk msg

  let verify (pk : pk) ~(msg : Bytes.t) ~(signature : signature) : bool =
    let msg = Bytes.to_bytes msg in
    MinPk.Pop.verify pk msg signature

  let gen_keypair (secret : B32.t) : pk * sk =
    let sk = generate_sk (Bytes.to_bytes (B32.to_bytes secret)) in
    let pk = MinPk.derive_pk sk in
    (pk, sk)

  let address_of_pubkey (pk : pk) : B20.t =
    Bls12_381.G1.of_compressed_bytes_exn (MinPk.pk_to_bytes pk)
    |> Bls12_381.G1.to_bytes
    |> Stdlib.Bytes.to_string
    |> keccak_256
    |> B20.of_bytes32_truncating
end

let sha_256 (bs : Bytes.t) : B32.t = B32.of_bytes_exn Digestif.SHA256.(to_raw_string (digest_string bs))

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
