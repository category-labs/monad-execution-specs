(** A pure implementation of the
    {{:https://github.com/BLAKE3-team/BLAKE3/blob/master/reference_impl/reference_impl.rs}BLAKE3 hash
    function}, exposing the bare compression function required by the MIP-8 Induced Subtree Merkle
    Commit.

    Chaining values are represented by their canonical serialization: eight 32-bit words encoded
    little-endian into a {!B32.t}. Only single-chunk inputs (at most 1024 bytes) are supported by
    {!hash} and {!derive_key}, which suffices for MIP-8. *)

open Byte_string

(* Compression flags, see table 3 of the BLAKE3 paper. *)
let chunk_start = 0x01
let chunk_end = 0x02
let parent = 0x04
let root = 0x08
let keyed_hash = 0x10
let derive_key_context = 0x20
let derive_key_material = 0x40

let mask32 = 0xFFFFFFFF

(* Little-endian decoding of the 32-bit word at byte offset [i]. *)
let word32_at (bs : Bytes.t) (i : int) =
  Char.code bs.[i]
  lor (Char.code bs.[i + 1] lsl 8)
  lor (Char.code bs.[i + 2] lsl 16)
  lor (Char.code bs.[i + 3] lsl 24)

let words_of_b32 (bs : B32.t) = Array.init 8 (fun i -> word32_at (B32.to_bytes bs) (4 * i))
let b32_of_words (ws : int array) = B32.init (fun i -> Char.chr ((ws.(i / 4) lsr (8 * (i mod 4))) land 0xFF))

let iv_words = [|0x6A09E667; 0xBB67AE85; 0x3C6EF372; 0xA54FF53A; 0x510E527F; 0x9B05688C; 0x1F83D9AB; 0x5BE0CD19|]

(** The BLAKE3 initialization vector; the initial chaining value of the unkeyed hash mode. *)
let iv = b32_of_words iv_words

let msg_permutation = [|2; 6; 3; 10; 7; 0; 4; 13; 1; 11; 12; 5; 9; 14; 15; 8|]

let quarter_round v a b c d x y =
  let rotr w n = ((w lsr n) lor (w lsl (32 - n))) land mask32 in
  v.(a) <- (v.(a) + v.(b) + x) land mask32 ;
  v.(d) <- rotr (v.(d) lxor v.(a)) 16 ;
  v.(c) <- (v.(c) + v.(d)) land mask32 ;
  v.(b) <- rotr (v.(b) lxor v.(c)) 12 ;
  v.(a) <- (v.(a) + v.(b) + y) land mask32 ;
  v.(d) <- rotr (v.(d) lxor v.(a)) 8 ;
  v.(c) <- (v.(c) + v.(d)) land mask32 ;
  v.(b) <- rotr (v.(b) lxor v.(c)) 7

let round v m =
  (* Columns. *)
  quarter_round v 0 4 8 12 m.(0) m.(1) ;
  quarter_round v 1 5 9 13 m.(2) m.(3) ;
  quarter_round v 2 6 10 14 m.(4) m.(5) ;
  quarter_round v 3 7 11 15 m.(6) m.(7) ;
  (* Diagonals. *)
  quarter_round v 0 5 10 15 m.(8) m.(9) ;
  quarter_round v 1 6 11 12 m.(10) m.(11) ;
  quarter_round v 2 7 8 13 m.(12) m.(13) ;
  quarter_round v 3 4 9 14 m.(14) m.(15)

(** The bare BLAKE3 compression function, truncated to the first 8 of its 16 output words, i.e. the
    chaining value [compress(cv, block, counter, block_len, flags)] of the paper. [block] must be exactly
    64 bytes; callers are responsible for zero-padding shorter blocks and passing their true [block_len]. *)
let compress (cv : B32.t) (block : Bytes.t) ~(counter : int) ~(block_len : int) ~(flags : int) : B32.t =
  assert (Bytes.length block = 64) ;
  let m = ref (Array.init 16 (fun i -> word32_at block (4 * i))) in
  let v =
    Array.append (words_of_b32 cv)
      [| iv_words.(0); iv_words.(1); iv_words.(2); iv_words.(3); counter land mask32
       ; (counter lsr 32) land mask32; block_len; flags |]
  in
  for round_number = 0 to 6 do
    round v !m ;
    if round_number < 6 then m := Array.init 16 (fun i -> !m.(msg_permutation.(i)))
  done ;
  b32_of_words (Array.init 8 (fun i -> v.(i) lxor v.(i + 8)))

(* Hash [input] as a single root chunk keyed by [key]: chunk counter and output counter are both zero,
   and the final block carries the [root] flag. *)
let hash_single_chunk ~(key : B32.t) ~(base_flags : int) (input : Bytes.t) : B32.t =
  if Bytes.length input > 1024 then
    invalid_arg "Blake3: only single-chunk inputs (at most 1024 bytes) are supported" ;
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

(** BLAKE3-256 of [input] in the basic unkeyed hash mode. *)
let hash (input : Bytes.t) : B32.t = hash_single_chunk ~key:iv ~base_flags:0 input

(** BLAKE3-256 of [key_material] in the key-derivation mode with context string [context]. MIP-8 does not
    use this mode directly, but it allows the [derive_key_material] compression flag to be validated
    against the official BLAKE3 test vectors. *)
let derive_key ~(context : Bytes.t) (key_material : Bytes.t) : B32.t =
  let context_key = hash_single_chunk ~key:iv ~base_flags:derive_key_context context in
  hash_single_chunk ~key:context_key ~base_flags:derive_key_material key_material
