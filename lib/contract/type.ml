(** Solidity encodings of OCaml values.

    Each codec carries typed encoding/decoding operations and layout metadata.
    Combinators preserve their agreement; the interface hides the records.
    Tuple values are ordinary OCaml products, not heterogeneous GADT lists. *)

open Byte_string
open Numeric

type alignment = Left | Right
type fixed_bytes = {alignment : alignment; byte_width : int}
type kind = Static of {word_width : int} | Dynamic

let bytes_to_words (size : int) = (size + 31) / 32
let bytes_to_padded_bytes (size : int) = bytes_to_words size * 32

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

type 'a packed =
  { width : int
  ; encode_packed : 'a -> Bytes.t list
  ; decode_packed : offset:int -> Bytes.t -> ('a * int, string) result }

type 'a typ =
  {name : string; layout : kind; encode : 'a -> B32.t list; decode : 'a decoder; packed : 'a packed option}

(* Tuple encoders share the enclosing header size and accumulated tail size.
   Decoders keep separate head/tail views, as in the original ABI decoder. *)
type 'a tup =
  { names : string list
  ; layout : kind
  ; header_words : int
  ; encode_parts : int -> 'a -> int -> B32.t list * B32.t list
  ; decode_parts : Input_view.t -> Input_view.t -> ('a * Input_view.t, decode_error) result
  ; encode_topics : 'a -> B32.t list
  ; packed : 'a packed option }

type ('a, 'repr) mapping =
  {name : string; repr : 'repr typ; encode : 'a -> 'repr; decode : 'repr -> ('a, string) result}

let type_name (typ : 'a typ) = typ.name
let kind (typ : 'a typ) = typ.layout
let enc (typ : 'a typ) = typ.encode
let dec (typ : 'a typ) = typ.decode
let tuple_to_canonical_type_names tup = tup.names
let tuple_header_word_width tup = tup.header_words
let encode_indexed_parameters tup = tup.encode_topics

let enc_tup tup v =
  let heads, tails = tup.encode_parts tup.header_words v 0 in
  heads @ tails

let dec_tuple tup view = tup.decode_parts view (Seq.drop tup.header_words view)

let tuple tup =
  { name = Format.sprintf "(%s)" (String.concat "," tup.names)
  ; layout = tup.layout
  ; encode = enc_tup tup
  ; decode = dec_tuple tup
  ; packed = tup.packed }

let mapped (m : ('a, 'repr) mapping) : 'a typ =
  let decode view =
    Result.(
      let$ r, view = dec m.repr view in
      match m.decode r with
      | Ok v -> Ok (v, view)
      | Error message -> Error (Map_error {name = m.name; message}) )
  in
  let packed =
    Option.map
      (fun p ->
        { width = p.width
        ; encode_packed = (fun v -> p.encode_packed (m.encode v))
        ; decode_packed =
            (fun ~offset bs ->
              Result.(
                let$ r, offset = p.decode_packed ~offset bs in
                let$ v = m.decode r in
                Ok (v, offset) ) ) } )
      m.repr.packed
  in
  {name = m.name; layout = m.repr.layout; encode = (fun v -> enc m.repr (m.encode v)); decode; packed}

let fixed_bytes {alignment; byte_width} =
  let decode view =
    Result.(
      let n_words = bytes_to_padded_bytes byte_width / 32 in
      let$ bs, view = Option.or_fail Input_too_short (Input_view.take_words n_words view) in
      match alignment with
      | Left -> Ok (Bytes.sub bs 0 byte_width, view)
      | Right -> Ok (Bytes.sub bs (Bytes.length bs - byte_width) byte_width, view) )
  in
  { name = Format.sprintf (match alignment with Left -> "bytes%d" | Right -> "bytesr%d") byte_width
  ; layout = Static {word_width = bytes_to_words byte_width}
  ; encode =
      (fun v ->
        assert (Bytes.length v = byte_width) ;
        align alignment v )
  ; decode
  ; packed =
      Some
        { width = byte_width
        ; encode_packed =
            (fun v ->
              assert (Bytes.length v = byte_width) ;
              [v] )
        ; decode_packed =
            (fun ~offset bs ->
              assert (Bytes.length bs - offset >= byte_width) ;
              Ok (Bytes.sub bs offset byte_width, offset + byte_width) ) } }

let bytes =
  { name = "bytes"
  ; layout = Dynamic
  ; encode = (fun v -> U256.(to_repr ~$(Bytes.length v)) :: align Left v)
  ; decode =
      (fun view ->
        Result.(
          let$ len, view = dec_length view in
          dec (fixed_bytes {alignment = Left; byte_width = len}) view ) )
  ; packed = None }

let array typ =
  let encode v =
    let len = U256.(to_repr ~$(List.length v)) in
    let rec loop = function [] -> [] | elt :: elts -> enc typ elt :: loop elts in
    len :: List.concat (loop v)
  in
  let decode view =
    Result.(
      let$ len, view = dec_length view in
      let rec loop len view =
        if len <= 0 then Ok ([], view)
        else
          let$ elt, view = dec typ view in
          let$ elts, view = loop (len - 1) view in
          Ok (elt :: elts, view)
      in
      loop len view )
  in
  {name = Format.sprintf "%s[]" (type_name typ); layout = Dynamic; encode; decode; packed = None}

let tup0 =
  { names = []
  ; layout = Static {word_width = 0}
  ; header_words = 0
  ; encode_parts = (fun _ () _ -> ([], []))
  ; decode_parts = (fun _ tail -> Ok ((), tail))
  ; encode_topics = (fun () -> [])
  ; packed =
      Some {width = 0; encode_packed = (fun () -> []); decode_packed = (fun ~offset _ -> Ok ((), offset))} }

let cons hd tl =
  let layout =
    match (kind hd, tl.layout) with
    | Static a, Static b -> Static {word_width = a.word_width + b.word_width}
    | _ -> Dynamic
  in
  let head_words = match kind hd with Static s -> s.word_width | Dynamic -> 1 in
  let encode_parts header_words (elt, elts) running_tails_len =
    match kind hd with
    | Static _ ->
        let heads, tails = tl.encode_parts header_words elts running_tails_len in
        (enc hd elt @ heads, tails)
    | Dynamic ->
        let head = U256.(to_repr ~$Stdlib.((header_words * 32) + running_tails_len)) in
        let tail = enc hd elt in
        let tail_words = List.length tail in
        let heads, tails = tl.encode_parts header_words elts (running_tails_len + (tail_words * 32)) in
        (head :: heads, tail @ tails)
  in
  let decode_parts head_view tail_view =
    Result.(
      match kind hd with
      | Static _ ->
          let$ elt, head_view = dec hd head_view in
          let$ elts, tail_view = tl.decode_parts head_view tail_view in
          Ok ((elt, elts), tail_view)
      | Dynamic ->
          let$ _tail_offset, head_view = dec_length head_view in
          (* Preserve the existing decoder's ignored tuple offsets. *)
          let$ elt, tail_view = dec hd tail_view in
          let$ elts, tail_view = tl.decode_parts head_view tail_view in
          Ok ((elt, elts), tail_view) )
  in
  let packed =
    match (hd.packed, tl.packed) with
    | Some a, Some b ->
        Some
          { width = a.width + b.width
          ; encode_packed = (fun (v, vs) -> a.encode_packed v @ b.encode_packed vs)
          ; decode_packed =
              (fun ~offset bs ->
                Result.(
                  let$ v, offset = a.decode_packed ~offset bs in
                  let$ vs, offset = b.decode_packed ~offset bs in
                  Ok ((v, vs), offset) ) ) }
    | _ -> None
  in
  { names = type_name hd :: tl.names
  ; layout
  ; header_words = head_words + tl.header_words
  ; encode_parts
  ; decode_parts
  ; encode_topics =
      (fun (v, vs) ->
        let words = enc hd v in
        assert (List.length words = 1) ;
        List.hd words :: tl.encode_topics vs )
  ; packed }

(* Reassociate the OCaml value without changing the ABI tuple's field layout. *)
let map_tuple ~encode ~decode tup =
  { tup with
    encode_parts = (fun header v tails -> tup.encode_parts header (encode v) tails)
  ; decode_parts =
      (fun heads tails -> Result.map (fun (v, rest) -> (decode v, rest)) (tup.decode_parts heads tails))
  ; encode_topics = (fun v -> tup.encode_topics (encode v))
  ; packed =
      Option.map
        (fun p ->
          { p with
            encode_packed = (fun v -> p.encode_packed (encode v))
          ; decode_packed =
              (fun ~offset bs ->
                Result.map (fun (v, offset) -> (decode v, offset)) (p.decode_packed ~offset bs) ) } )
        tup.packed }

let enc_bytes typ v = Bytes.(concat empty (List.map B32.to_bytes (enc typ v)))

let dec_bytes ?(allow_trailing = false) typ bytes =
  Result.(
    let$ v, view = dec typ (Input_view.of_bytes bytes) in
    let$ () = ensure (allow_trailing || Seq.is_empty view) ~or_error:Input_too_long in
    return v )

let option ~empty typ =
  let repr = typ in
  let encode = function None -> empty | Some elt -> elt in
  let decode e = Ok (if e = empty then None else Some e) in
  let name = Format.sprintf "Option<%s>" (type_name typ) in
  mapped {repr; encode; decode; name}

let tup1 x1 = map_tuple ~encode:(fun x1 -> (x1, ())) ~decode:(fun (x1, ()) -> x1) (cons x1 tup0)

let tup2 (x1, x2) =
  map_tuple
    ~encode:(fun (x1, x2) -> (x1, (x2, ())))
    ~decode:(fun (x1, (x2, ())) -> (x1, x2))
    (cons x1 (cons x2 tup0))

let tup3 (x1, x2, x3) =
  map_tuple
    ~encode:(fun (x1, x2, x3) -> (x1, (x2, (x3, ()))))
    ~decode:(fun (x1, (x2, (x3, ()))) -> (x1, x2, x3))
    (cons x1 (cons x2 (cons x3 tup0)))

let tup4 (x1, x2, x3, x4) =
  map_tuple
    ~encode:(fun (x1, x2, x3, x4) -> (x1, (x2, (x3, (x4, ())))))
    ~decode:(fun (x1, (x2, (x3, (x4, ())))) -> (x1, x2, x3, x4))
    (cons x1 (cons x2 (cons x3 (cons x4 tup0))))

let tup5 (x1, x2, x3, x4, x5) =
  map_tuple
    ~encode:(fun (x1, x2, x3, x4, x5) -> (x1, (x2, (x3, (x4, (x5, ()))))))
    ~decode:(fun (x1, (x2, (x3, (x4, (x5, ()))))) -> (x1, x2, x3, x4, x5))
    (cons x1 (cons x2 (cons x3 (cons x4 (cons x5 tup0)))))

let tup6 (x1, x2, x3, x4, x5, x6) =
  map_tuple
    ~encode:(fun (x1, x2, x3, x4, x5, x6) -> (x1, (x2, (x3, (x4, (x5, (x6, ())))))))
    ~decode:(fun (x1, (x2, (x3, (x4, (x5, (x6, ())))))) -> (x1, x2, x3, x4, x5, x6))
    (cons x1 (cons x2 (cons x3 (cons x4 (cons x5 (cons x6 tup0))))))

let tup7 (x1, x2, x3, x4, x5, x6, x7) =
  map_tuple
    ~encode:(fun (x1, x2, x3, x4, x5, x6, x7) -> (x1, (x2, (x3, (x4, (x5, (x6, (x7, ()))))))))
    ~decode:(fun (x1, (x2, (x3, (x4, (x5, (x6, (x7, ()))))))) -> (x1, x2, x3, x4, x5, x6, x7))
    (cons x1 (cons x2 (cons x3 (cons x4 (cons x5 (cons x6 (cons x7 tup0)))))))

let tup12 (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) =
  map_tuple
    ~encode:(fun (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
      (x1, (x2, (x3, (x4, (x5, (x6, (x7, (x8, (x9, (x10, (x11, (x12, ())))))))))))) )
    ~decode:(fun (x1, (x2, (x3, (x4, (x5, (x6, (x7, (x8, (x9, (x10, (x11, (x12, ())))))))))))) ->
      (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) )
    (cons x1
       (cons x2
          (cons x3
             (cons x4 (cons x5 (cons x6 (cons x7 (cons x8 (cons x9 (cons x10 (cons x11 (cons x12 tup0))))))))) ) ) )

(* The Solidity ABI treats addresses as integers in that they are right-aligned. *)
module Address = struct
  include Chain.Ethereum.Address
  let t : t typ =
    mapped
      { repr = fixed_bytes {alignment = Right; byte_width}
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
    mapped
      { repr = fixed_bytes {alignment = Left; byte_width}
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
    mapped
      { repr = fixed_bytes {alignment = Right; byte_width}
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
  mapped
    { repr = U8.t
    ; encode = (fun b -> if b then U8.one else U8.zero)
    ; decode = (fun u8 -> Ok U8.(u8 <> zero))
    ; name = "bool" }

let unit : unit typ =
  mapped {repr = tuple tup0; encode = (fun () -> ()); decode = (fun () -> Ok ()); name = "unit"}

(* Packed encoding uses the same type-specific operations, without ABI word padding. *)
module Packed = struct
  let t ?name (ty : 'a typ) =
    let p =
      match ty.packed with
      | Some p -> p
      | None -> failwith (Format.sprintf "Packing non-static type %s" (type_name ty))
    in
    let repr = fixed_bytes {alignment = Left; byte_width = p.width} in
    let encode v = Bytes.(concat empty (p.encode_packed v)) in
    let decode bs = Result.map fst (p.decode_packed ~offset:0 bs) in
    let name = match name with None -> Format.sprintf "Packed<%s>" (type_name ty) | Some name -> name in
    mapped {repr; encode; decode; name}
end
