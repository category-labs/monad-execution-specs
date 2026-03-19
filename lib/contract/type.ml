(** Solidity encodings of OCaml values. *)

open Byte_string
open Numeric

(** Right-associative tuples. This is useful as syntactic sugar. *)
module Tuple = struct
  type 'a t = [] : unit t | ( :: ) : 'a * 'b t -> ('a * 'b) t
end

type alignment = Left | Right

(* It's tempting to encode whether a type is static or dynamic as a phantom parameter. However, because
   GADTs cannot have a variance, it becomes very hard to express that "every static type is a dynamic type". *)
type 'a typ =
  | Tuple : 'a tup -> 'a typ
  | Fixed_bytes : {alignment : alignment; byte_width : int} -> Bytes.t typ
    (* Explicit alignment allows us to use a right-aligned Fixed_bytes type to represent integers. *)
  | Bytes : Bytes.t typ
  | Array : 'a typ -> 'a list typ
  | Map :
      {name : string; repr : 'repr typ; encode : 'a -> 'repr; decode : 'repr -> ('a, string) result}
      -> 'a typ

and 'a tup = [] : unit Tuple.t tup | ( :: ) : 'a typ * 'b Tuple.t tup -> ('a * 'b) Tuple.t tup

let rec type_name : type a. a typ -> string =
  let rec tuple_names : type a. a tup -> string list = function
    | [] -> []
    | ty :: tys -> type_name ty :: tuple_names tys
  in
  function
  | Tuple tup -> Format.sprintf "(%s)" (String.concat "," (tuple_names tup))
  | Fixed_bytes {alignment = Left; byte_width} -> Format.sprintf "bytes%d" byte_width
  | Fixed_bytes {alignment = Right; byte_width} -> Format.sprintf "bytesr%d" byte_width
  | Bytes -> "bytes"
  | Array typ -> Format.sprintf "%s[]" (type_name typ)
  | Map m -> m.name

let bytes_to_words (size : int) = (size + 31) / 32
let bytes_to_padded_bytes (size : int) = bytes_to_words size * 32

type kind = Static of {word_width : int} | Dynamic
let rec kind : type a. a typ -> kind =
  let concat (k_0 : kind) (k_1 : kind) =
    match (k_0, k_1) with
    | Static s_0, Static s_1 -> Static {word_width = s_0.word_width + s_1.word_width}
    | _ -> Dynamic
  in
  let rec tuple_kind : type a. a tup -> kind = function
    | [] -> Static {word_width = 0}
    | hd :: tl -> concat (kind hd) (tuple_kind tl)
  in
  function
  | Tuple tup -> tuple_kind tup
  | Fixed_bytes {byte_width; _} -> Static {word_width = bytes_to_words byte_width}
  | Bytes | Array _ -> Dynamic
  | Map m -> kind m.repr

let rec tuple_header_word_width : type a. a tup -> int = function
  | [] -> 0
  | elt :: elts -> (
    match kind elt with
    | Dynamic -> 1 + tuple_header_word_width elts
    | Static {word_width} -> word_width + tuple_header_word_width elts )

(* Optional versions of types. *)
let option : type a. empty:a -> a typ -> a option typ =
 fun ~empty typ ->
  let repr = typ in
  let encode = function None -> empty | Some elt -> elt in
  let decode e = Ok (if e = empty then None else Some e) in
  let name = Format.sprintf "Option<%s>" (type_name typ) in
  Map {repr; encode; decode; name}

let align (alignment : alignment) (bs : Bytes.t) : B32.t list =
  let padded_bytes = bytes_to_padded_bytes (Bytes.length bs) in
  let padded_words = padded_bytes / 32 in
  match alignment with
  | Left -> List.init padded_words (fun i -> B32.sub_with_zero_padding bs (i * 32))
  | Right ->
      let d = padded_bytes - Bytes.length bs in
      if d = 0 then List.init padded_words (fun i -> B32.sub_with_zero_padding bs (i * 32))
      else
        let header = B32.init (fun i -> if i < d then '\x00' else bs.[i - d]) in
        header :: List.init (padded_words - 1) (fun i -> B32.sub_with_zero_padding bs (32 - d + (i * 32)))

let rec enc : type a. a typ -> a -> B32.t list =
 fun typ v ->
  match typ with
  | Tuple tup -> enc_tup tup v
  | Fixed_bytes {alignment; byte_width} ->
      assert (Bytes.length v = byte_width) ;
      align alignment v
  | Bytes ->
      let len = U256.(to_repr ~$(Bytes.length v)) in
      len :: align Left v
  | Array typ ->
      let len = U256.(to_repr ~$(List.length v)) in
      let rec loop elts = match elts with List.[] -> List.[] | elt :: elts -> enc typ elt :: loop elts in
      len :: List.concat (loop v)
  | Map {repr; encode; _} -> enc repr (encode v)

and enc_tup : type a. a tup -> a -> B32.t list =
 fun tup elts ->
  let header_word_width = tuple_header_word_width tup in
  let rec loop : type a. a tup -> a -> int -> B32.t list * B32.t list =
   fun (tup : a tup) (elts : a) running_tails_len ->
    match (tup, elts) with
    | [], [] -> ([], [])
    | hd :: tup, elt :: elts -> (
      (* TODO: the list concatenations here have quadratic overhead. Revisit if it becomes an issue. *)
      match kind hd with
      | Static _ ->
          let heads, tails = loop tup elts running_tails_len in
          (enc hd elt @ heads, tails)
      | Dynamic ->
          let head = U256.(to_repr ~$Stdlib.((header_word_width * 32) + running_tails_len)) in
          let tail = enc hd elt in
          let tail_words = List.length tail in
          let heads, tails = loop tup elts (running_tails_len + (tail_words * 32)) in
          (head :: heads, tail @ tails) )
  in
  let headers, tails = loop tup elts 0 in
  headers @ tails

let enc_bytes (typ : 'a typ) (v : 'a) = Bytes.(concat empty (List.map B32.to_bytes (enc typ v)))

(* Decoding operates over word iterators, which are constructed from either a byte string or the storage. *)
module Input_view = struct
  (* A view is a sequence of 32-byte words followed by optionally a sub-32-byte tail. While a storage-derived
     view is always aligned, views obtained from a message's input data may have a tail. In case of e.g. input
     data of length 33, this allows us to differentiate between three cases:
     * dec returns Ok(v, view) and view is empty: decoding was successful.
     * dec returns Ok(v, view) and view is non-empty: decoding was successful but some (potentially unaligned)
       bytes are left over.
     * dec returns Error: decoding failed (either because input data was too short or malformed. *)
  type chunk = Word of B32.t | Tail of Bytes.t
  type t = chunk Seq.t

  let of_bytes (bs : Bytes.t) : t =
    Seq.unfold
      (fun i ->
        if i + 32 <= Bytes.length bs then Some (Word (B32.sub bs i), i + 32)
        else if i < Bytes.length bs then Some (Tail (Bytes.sub bs i (Bytes.length bs - i)), Bytes.length bs)
        else None )
      0

  let of_storage (s : Chain.Ethereum.Storage.t) ~(offset : U256.t) : t =
    Seq.unfold
      (fun addr ->
        let word = Chain.Ethereum.Storage.find (U256.to_repr addr) s in
        let addr = U256.(addr + one) in
        Some (Word word, addr) )
      offset

  let take_word (view : t) : (B32.t * t) option =
    match Seq.uncons view with Some (Word w, view) -> Some (w, view) | _ -> None

  let take_words (n_words : int) (view : t) : (Bytes.t * t) option =
    Option.(
      let rec loop n_words view =
        if n_words <= 0 then Some (List.[], view)
        else
          let$ w, view = take_word view in
          let w = B32.to_bytes w in
          let$ ws, view = loop (n_words - 1) view in
          return (List.(w :: ws), view)
      in
      let$ words, view = loop n_words view in
      return (Bytes.(concat empty words), view) )
end

type decode_error =
  | Input_too_short
  | Input_too_long
  | Length_overflow
  | Map_error of {name : string; message : string}

type 'a decoder = Input_view.t -> ('a * Input_view.t, decode_error) result

let dec_length : int decoder =
 fun view ->
  Result.(
    let$ header, view = Option.or_fail Input_too_short (Input_view.take_word view) in
    let$ length = Option.or_fail Length_overflow U256.(to_int_opt (of_repr header)) in
    return (length, view) )

let rec dec : type a. a typ -> a decoder =
 fun typ view ->
  let open Result in
  match typ with
  | Tuple tup -> dec_tuple tup view
  | Bytes ->
      let$ len, view = dec_length view in
      dec (Fixed_bytes {alignment = Left; byte_width = len}) view
  | Array elt_typ ->
      let$ len, view = dec_length view in
      let rec loop len view =
        if len <= 0 then return (List.[], view)
        else
          let$ elt, view = dec elt_typ view in
          let$ elts, view = loop (len - 1) view in
          return (List.(elt :: elts), view)
      in
      loop len view
  | Fixed_bytes {alignment; byte_width} -> (
      let n_words = bytes_to_padded_bytes byte_width / 32 in
      let$ bytes, view = Option.or_fail Input_too_short (Input_view.take_words n_words view) in
      match alignment with
      | Left -> Ok (Bytes.sub bytes 0 byte_width, view)
      | Right -> Ok (Bytes.sub bytes (Bytes.length bytes - byte_width) byte_width, view) )
  | Map {repr; decode; name; _} -> (
      let$ r, view = dec repr view in
      match decode r with Ok v -> return (v, view) | Error message -> fail (Map_error {name; message}) )

and dec_tuple : type a. a tup -> a decoder =
 fun tup view ->
  let open Result in
  let rec loop : type a. a tup -> Input_view.t -> Input_view.t -> (a * Input_view.t, decode_error) result =
   fun tup head_view tail_view ->
    match tup with
    | [] -> Ok ([], tail_view)
    | hd :: tup -> (
      match kind hd with
      | Static _ ->
          let$ hd_elt, head_view = dec hd head_view in
          let$ tl_elts, tail_view = loop tup head_view tail_view in
          Ok (Tuple.(hd_elt :: tl_elts), tail_view)
      | Dynamic ->
          let$ _tail_offset, head_view = dec_length head_view in
          (* We could carry our own count of the tail position to double-check against tail_offset. As it
             stands, we can decode malformed tuples. Note that the C++ implementation of the staking contract
             also ignores tuple headers. *)
          let$ hd_elt, tail_view = dec hd tail_view in
          let$ tl_elts, tl_elts_len = loop tup head_view tail_view in
          Ok (Tuple.(hd_elt :: tl_elts), tl_elts_len) )
  in
  let header_word_width = tuple_header_word_width tup in
  let tail_view = Seq.drop header_word_width view in
  loop tup view tail_view

(* Decode a byte-string as the indicated type and fail if any bytes remain unconsumed. *)
let dec_bytes ?(allow_trailing = false) (typ : 'a typ) (bytes : Bytes.t) =
  Result.(
    let$ v, view = dec typ (Input_view.of_bytes bytes) in
    let$ () = ensure (allow_trailing || Seq.is_empty view) ~or_error:Input_too_long in
    return v )

(* The Solidity ABI treats addresses as integers in that they are right-aligned. *)
module Address = struct
  include Chain.Ethereum.Address
  let t : t typ =
    Map
      { repr = Fixed_bytes {alignment = Right; byte_width}
      ; encode = (fun addr -> to_bytes addr)
      ; decode = (fun bs -> Result.Option.or_fail "input too short" (of_bytes bs))
      ; name = "address" }

  let t_option : t option typ = option ~empty:zero t
end

module Fixed_bytes (M : sig
  type t
  val to_bytes : t -> Bytes.t
  val of_bytes : Bytes.t -> t option
  val byte_width : int
end) =
struct
  open M
  let t : t typ =
    Map
      { repr = Fixed_bytes {alignment = Left; byte_width}
      ; encode = (fun bs -> to_bytes bs)
      ; decode = (fun bs -> Result.Option.or_fail "input too short" (of_bytes bs))
      ; name = Format.sprintf "bytes%d" byte_width }
end

module B33 = struct
  include B33
  include Fixed_bytes (B33)
end

module B48 = struct
  include B48
  include Fixed_bytes (B48)
end

module Fixed_uint (M : sig
  module Repr : sig
    type t
    val to_bytes : t -> Bytes.t
    val of_bytes : Bytes.t -> t option
  end
  type t
  val byte_width : int
  val to_repr : t -> Repr.t
  val of_repr : Repr.t -> t
  val zero : t
end) =
struct
  open M
  let t : t typ =
    Map
      { repr = Fixed_bytes {alignment = Right; byte_width}
      ; encode = (fun x -> Repr.to_bytes (to_repr x))
      ; decode =
          (fun bs ->
            match Repr.of_bytes bs with None -> Error "input too short" | Some bs -> Ok (of_repr bs) )
      ; name = Format.sprintf "uint%d" (byte_width * 8) }

  let t_option : t option typ = option ~empty:zero t
end

module U256 = struct
  include U256
  include Fixed_uint (U256)
end

module U64 = struct
  include U64
  include Fixed_uint (U64)
end

module U8 = struct
  include U8
  include Fixed_uint (U8)
end

module U32 = struct
  include U32
  include Fixed_uint (U32)
end

(* abicoder v1 is unclear on how to treat a bool field with spurious bits.
   The Solidity compiler emits ISZERO so we use the same logic here. *)
let bool : bool typ =
  Map
    { repr = U8.t
    ; encode = (fun b -> if b then U8.one else U8.zero)
    ; decode = (fun u8 -> Ok U8.(u8 <> zero))
    ; name = "bool" }

let unit : unit typ = Map {repr = Tuple []; encode = (fun () -> []); decode = (fun [] -> Ok ()); name = "unit"}

(* TODO: the aligned/packed distinction is awkward: aligned types are most naturally encoded and decoded from
   storage, since it's word-aligned, and packed types are most naturally encoded and decoded from straight
   byte arrays. However, most (all?) usages of packed types in the staking contract are in the storage, and
   most usages of aligned types are in function input/outputs. *)
module Packed : sig
  val t : ?name:string -> 'a typ -> 'a typ
end = struct
  let rec packed_width : type a. a typ -> int option = function
    | Fixed_bytes {byte_width; _} -> Some byte_width
    | Bytes -> None
    | Array _ -> None
    | Tuple [] -> Some 0
    | Tuple (ty :: tys) ->
        Option.(
          let$ ty_w = packed_width ty in
          let$ tys_w = packed_width (Tuple tys) in
          return (ty_w + tys_w) )
    | Map {repr; _} -> packed_width repr

  let rec encode_packed : type a. a typ -> a -> Bytes.t list =
   fun ty v ->
    match ty with
    | Fixed_bytes {byte_width; _} ->
        assert (Bytes.length v = byte_width) ;
        [v]
    | Tuple [] -> []
    | Tuple (ty :: tys) -> ( match v with v :: vs -> encode_packed ty v @ encode_packed (Tuple tys) vs )
    | Map {repr; encode; _} -> encode_packed repr (encode v)
    | Bytes | Array _ ->
        (* This cannot happen as we only pack static types. *)
        assert false

  let rec decode_packed : type a. a typ -> offset:int -> Bytes.t -> (a * int, string) result =
   fun ty ~offset bs ->
    match ty with
    | Fixed_bytes {byte_width; _} ->
        (* This cannot fail as `decode_packed` is only called when the decoded byte-string is known to be
           long enough. *)
        assert (Bytes.length bs - offset >= byte_width) ;
        Ok (Bytes.sub bs offset byte_width, offset + byte_width)
    | Tuple [] -> Ok ([], offset)
    | Tuple (ty :: tys) ->
        Result.(
          let$ v, offset = decode_packed ty ~offset bs in
          let$ vs, offset = decode_packed (Tuple tys) ~offset bs in
          return (Tuple.(v :: vs), offset) )
    | Map {repr; decode; _} ->
        Result.(
          let$ r, offset = decode_packed repr ~offset bs in
          let$ r = decode r in
          return (r, offset) )
    | Bytes | Array _ ->
        (* This cannot happen as we only pack static types. *)
        assert false

  let t : type a. ?name:string -> a typ -> a typ =
   fun ?name ty ->
    let byte_width =
      match packed_width ty with
      | Some w -> w
      | None -> failwith (Format.sprintf "Packing non-static type %s" (type_name ty))
    in
    let repr = Fixed_bytes {alignment = Left; byte_width} in
    let encode v = Bytes.(concat empty (encode_packed ty v)) in
    let decode bs = Result.map fst (decode_packed ty ~offset:0 bs) in
    let name = match name with None -> Format.sprintf "Packed<%s>" (type_name ty) | Some name -> name in
    Map {repr; encode; decode; name}
end
