(** Bindings to cryptographic functions in external libraries. *)

open Numeric
open Byte_string

let times_hashed: (Bytes.t, bool) Hashtbl.t = Hashtbl.create 100_000

let hashes : B32.t Bytes.Map.t ref = ref Bytes.Map.empty

let redundant_bytes_hashed = ref 0

let reset () =
  Hashtbl.reset times_hashed;
  let r = !redundant_bytes_hashed in
  redundant_bytes_hashed := 0;
  r

let target_input = Bytes.of_hex_string
"f869a020ae969e9a3e589d5f55bf39fc2428b31e3ec8ffcb7107dd2d1c5503fa1bdfb8b846f8440180a056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421a06c029a231254fadb724d63be769f75eedd66362df034a3e663252b49d062a666"

(** [keccak_256 bytes] computes the Keccak-256 digest of a byte array. *)
let keccak_256 (input : Bytes.t) : B32.t =
  (*
  (if Hashtbl.mem times_hashed input
  then (redundant_bytes_hashed := !redundant_bytes_hashed + Bytes.length input)
  else Hashtbl.replace times_hashed input true);
   *)
  let bytes = Digestif.KECCAK_256.(to_raw_string (digest_string input)) in
  (* Never fails as Keccak-256 is guaranteed to produce 32 bytes. *)
  Byte_string.B32.of_bytes_exn bytes

(** The Keccak-256 encoding of the empty byte array. *)
let keccak_256_empty = keccak_256 Bytes.empty

let keccak_256_char = Iarray.init 256 (fun i -> keccak_256 (Bytes.of_char (Char.chr i)))

let keccak_256 (input : Bytes.t) : B32.t =
  (*
  let hash = ref B32.zeros in
   hashes := Bytes.Map.update input (fun entry -> match entry with
      | None -> hash := keccak_256 input; Some !hash
      | Some h -> hash := h; entry) !hashes;
   !hash
   *)
  B32.init (fun i ->
      if i >= Bytes.length input then '\x00' else input.[i])
(*
  if input = "" then keccak_256_empty
  else if Bytes.length input = 1 then Iarray.get keccak_256_char (Char.code input.[0])
  else keccak_256 input
 *)

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
      let result_bigstring =
        (msg_hash :> string)
        |> Bigstring.of_string
        |> Sign.recover_exn context ~signature
        |> Key.to_bytes ~compress:false context
      in
      let public_key_i i = result_bigstring.{i + 1} in
      let public_key = Bytes.init 64 public_key_i in
      return (B20.of_bytes32_truncating (keccak_256 public_key)) ) )

let sha_256 (bs : Bytes.t) : B32.t = B32.of_bytes_exn Digestif.SHA256.(to_raw_string (digest_string bs))

let ripemd_160 (bs : Bytes.t) : B20.t = B20.of_bytes_exn Digestif.RMD160.(to_raw_string (digest_string bs))
