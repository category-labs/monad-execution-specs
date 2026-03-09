(** Bindings to cryptographic functions in external libraries. *)

open Numeric
open Byte_string

(** [keccak_256 bytes] computes the Keccak-256 digest of a byte array. *)
let keccak_256 (input : Bytes.t) : B32.t =
  let bytes = Digestif.KECCAK_256.(to_raw_string (digest_string input)) in
  (* Never fails as Keccak-256 is guaranteed to produce 32 bytes. *)
  Byte_string.B32.of_bytes_exn bytes

(** The Keccak-256 encoding of the empty byte array. *)
let keccak_256_empty = keccak_256 Bytes.empty

let () = assert (B32.(keccak_256_empty = ~@"c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"))

let secp256k1b = U256.(~$7)
let secp256k1p = U256.(~@"0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F")
let secp256k1n = U256.(~@"0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141")

let context = Secp256k1.Context.(create [Verify; Sign])

type signature = {r : U256.t; s : U256.t; y_parity : U8.t}

let buffer_init n b_i : (char, Bigarray.int8_unsigned_elt, Bigarray.c_layout) Bigarray.Array1.t =
  Bigarray.Array1.init Bigarray.char Bigarray.C_layout n b_i
let buffer_of_bytes (str : Bytes.t) = buffer_init (Bytes.length str) (fun i -> str.[i])
let buffer_of_b32 (str : B32.t) = buffer_of_bytes (B32.to_bytes str)

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
    Secp256k1.(
      let r = U256.to_repr r in
      let s = U256.to_repr s in
      let y_parity = Char.chr (U8.to_int y_parity) in
      let signature_i = function
        | i when i < 32 -> B32.(r.$(i))
        | i when i < 64 -> B32.(s.$(i - 32))
        | _ -> y_parity
      in
      let$ signature =
        Result.to_option
          (Sign.read_recoverable context ~recid:(Char.code y_parity) (buffer_init 65 signature_i))
      in
      let result_bigstring =
        msg_hash
        |> buffer_of_b32
        |> Sign.msg_of_bytes_exn
        |> (fun msg -> Sign.recover_exn context ~signature ~msg)
        |> Key.to_bytes ~compress:false context
      in
      let public_key_i i = result_bigstring.{i + 1} in
      let public_key = Bytes.init 64 public_key_i in
      return (B20.of_bytes32_truncating (keccak_256 public_key)) ) )

let sha_256 (bs : Bytes.t) : B32.t = B32.of_bytes_exn Digestif.SHA256.(to_raw_string (digest_string bs))

let ripemd_160 (bs : Bytes.t) : B20.t = B20.of_bytes_exn Digestif.RMD160.(to_raw_string (digest_string bs))
