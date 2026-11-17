open Byte_string
open Numeric

type decode_error =
  | Input_too_short
  | Input_too_long
  | Length_overflow
  | Map_error of {name : string; message : string}

module Input_view = struct
  (* A view is a "materialized" sequence of bytes [start],[remaining] followed by a (possibly empty, possibly
     infinite) sequence of 32-byte words [chunks]. This can represent either a calldata view (the calldata as
     the initial bytes followed by an empty sequence of words) or a storage view (as empty bytes followed by
     an infinite sequence of storage words). *)
  type t = {start : int; remaining : Bytes.t; chunks : B32.t Seq.t}

  let of_bytes (bs : Bytes.t) : t =
    let start = 0 in
    let remaining = bs in
    let chunks = Seq.empty in
    {start; remaining; chunks}

  let of_storage (s : Chain.Ethereum.Storage.t) ~(offset : U256.t) : t =
    let start = 0 in
    let remaining = Bytes.empty in
    let chunks =
      Seq.unfold
        (fun addr ->
          let word = Chain.Ethereum.Storage.find (U256.to_repr addr) s in
          let addr = U256.(addr + one) in
          Some (word, addr) )
        offset
    in
    {start; remaining; chunks}

  let take_bytes (n_bytes : int) (view : t) : (Bytes.t * t) option =
    let rec loop n pieces {start; remaining; chunks} =
      let available = Bytes.length remaining - start in
      if n <= available then
        let piece = Bytes.sub remaining start n in
        Some (List.rev (piece :: pieces), {start = start + n; remaining; chunks})
      else
        let piece = Bytes.sub remaining start available in
        match Seq.uncons chunks with
        | None -> None
        | Some (chunk, chunks) ->
            let remaining = B32.to_bytes chunk in
            loop (n - available) (piece :: pieces) {start = 0; remaining; chunks}
    in
    if n_bytes <= 0 then Some (Bytes.empty, view)
    else
      Option.(
        let$ pieces, view = loop n_bytes [] view in
        return (Bytes.(concat empty pieces), view) )

  let take_word (view : t) : (B32.t * t) option =
    Option.(
      let$ bs, view = take_bytes 32 view in
      (* Cannot fail as bs is exactly 32 bytes wide. *)
      return (B32.of_bytes_exn bs, view) )

  let drop_bytes (n_bytes : int) (view : t) : t option =
    let rec loop n {start; remaining; chunks} =
      let available = Bytes.length remaining - start in
      if n <= available then Some {start = start + n; remaining; chunks}
      else
        match Seq.uncons chunks with
        | None -> None
        | Some (chunk, chunks) -> loop (n - available) {start = 0; remaining = B32.to_bytes chunk; chunks}
    in
    loop (max n_bytes 0) view

  let is_empty ({start; remaining; chunks} : t) : bool =
    start >= Bytes.length remaining && Seq.is_empty chunks
end

type alignment = Left | Right

type encoding = Abi | Packed

type kind = Static of {abi_word_width : int; packed_byte_width : int} | Dynamic

type 'a typ =
  { name : string
  ; kind : kind
  ; read : encoding -> Input_view.t -> ('a * Input_view.t, decode_error) result
  ; write : encoding -> 'a -> Bytes.t }

let name {name; _} = name
let kind {kind; _} = kind
let read {read; _} = read
let write {write; _} = write

let bytes_to_whole_words (n_bytes : int) = (n_bytes + 31) / 32
let bytes_to_padded_bytes (n_bytes : int) = 32 * bytes_to_whole_words n_bytes

let padding_byte_width (n_bytes : int) = (32 - (n_bytes mod 32)) mod 32

let read_fixed (enc : encoding) (alignment : alignment) (byte_width : int) (view : Input_view.t) :
    (Bytes.t * Input_view.t, decode_error) result =
  let take n view = Result.Option.or_fail Input_too_short (Input_view.take_bytes n view) in
  let skip n view = Result.Option.or_fail Input_too_short (Input_view.drop_bytes n view) in
  Result.(
    match enc with
    | Packed -> take byte_width view
    | Abi -> (
        (* We don't check that the padding bytes are indeed zero. *)
        let padding = padding_byte_width byte_width in
        match alignment with
        | Left ->
            let$ bs, view = take byte_width view in
            let$ view = skip padding view in
            return (bs, view)
        | Right ->
            let$ view = skip padding view in
            take byte_width view ) )

let write_fixed (enc : encoding) (alignment : alignment) (bs : Bytes.t) : Bytes.t =
  match enc with
  | Packed -> bs
  | Abi -> (
      let padding = Bytes.make (padding_byte_width (Bytes.length bs)) '\x00' in
      match alignment with Left -> bs ^ padding | Right -> padding ^ bs )

module type FIXED_BYTES = sig
  type t
  val byte_width : int
  val of_bytes_exn : Bytes.t -> t
  val to_bytes : t -> Bytes.t
end

let fixed_bytes (module M : FIXED_BYTES) (alignment : alignment) : M.t typ =
  let open M in
  let name =
    match alignment with
    | Left -> Format.sprintf "bytes%d" byte_width
    | Right -> Format.sprintf "bytesr%d" byte_width
  in
  let kind = Static {abi_word_width = bytes_to_whole_words byte_width; packed_byte_width = byte_width} in
  let read enc view =
    Result.(
      let$ bs, view = read_fixed enc alignment byte_width view in
      return (of_bytes_exn bs, view) )
  in
  let write enc (bs : t) = write_fixed enc alignment (to_bytes bs) in
  {name; kind; read; write}

let map ~(name : string) ~(encode : 'a -> 'r) ~(decode : 'r -> ('a, string) result) (repr : 'r typ) : 'a typ =
  let kind = repr.kind in
  let read enc view =
    Result.(
      Result.(
        let$ r, view = repr.read enc view in
        match decode r with Ok v -> return (v, view) | Error message -> fail (Map_error {name; message}) ) )
  in
  let write enc v = repr.write enc (encode v) in
  {name; kind; read; write}

(* A type to represent Solidity's internal encoding of lengths. These must fit in an OCaml int, otherwise an
   error is returned when decoding them.
   This type is never used directly, but it's used internally when encoding/decoding dynamic types. *)
let length : int typ =
  map ~name:"length"
    ~encode:(fun i -> U256.(to_repr (of_int i)))
    ~decode:(fun bs -> Result.Option.or_fail "length overflow" U256.(to_int_opt (of_repr bs)))
    (fixed_bytes (module B32) Left)

let bytes : Bytes.t typ =
  let read enc view =
    Result.(
      let$ n, view = length.read enc view in
      read_fixed enc Left n view )
  in
  let write enc bs = length.write enc (Bytes.length bs) ^ write_fixed enc Left bs in
  {name = "bytes"; kind = Dynamic; read; write}

(* When encoding dynamic arrays or tuples, the Solidity ABI specifies that static fields are encoded in-place
   and dynamic fields are encoded as an offset, with their payload appended as a tail.
   [arrange_fields enc fields] is responsible for laying out the encoded fields [fields] according to this
   convention. *)
let arrange_fields (enc : encoding) (fields : (kind * Bytes.t) list) : Bytes.t =
  let head_byte_width =
    List.fold_left
      (fun n (kind, bs) -> match kind with Static _ -> n + Bytes.length bs | Dynamic -> n + U256.byte_width)
      0 fields
  in
  let heads, tails, _ =
    List.fold_left
      (fun (heads, tails, offset) (kind, bs) ->
        match kind with
        | Static _ -> (bs :: heads, tails, offset)
        | Dynamic -> (length.write enc offset :: heads, bs :: tails, offset + Bytes.length bs) )
      ([], [], head_byte_width) fields
  in
  Bytes.(concat empty (List.rev_append heads (List.rev tails)))

let write_field (typ : 'a typ) (enc : encoding) (v : 'a) : kind * Bytes.t = (typ.kind, typ.write enc v)

(* Decoding state for a sequence of fields. [base] is the start of the sequence, which offsets are relative to,
   [head] is the next unread head slot, and [tails_end] is the end of the last tail read, if any. Like the
   Solidity decoder, we follow offsets without checking that they are canonical. *)
type cursor = {base : Input_view.t; head : Input_view.t; tails_end : Input_view.t option}

let cursor (view : Input_view.t) : cursor = {base = view; head = view; tails_end = None}

(* Where the sequence ends: after the last tail if there is a dynamic field, after the head otherwise. This is
   exact for canonically encoded input. *)
let finish (c : cursor) : Input_view.t = match c.tails_end with Some view -> view | None -> c.head

let read_field (typ : 'a typ) (enc : encoding) (c : cursor) : ('a * cursor, decode_error) result =
  Result.(
    match typ.kind with
    | Static _ ->
        let$ v, head = typ.read enc c.head in
        return (v, {c with head})
    | Dynamic ->
        let$ offset, head = length.read enc c.head in
        let$ tail = Option.or_fail Input_too_short (Input_view.drop_bytes offset c.base) in
        let$ v, tails_end = typ.read enc tail in
        return (v, {c with head; tails_end = Some tails_end}) )

(* An array is represented as its length followed by its elements, laid out as a sequence according to the
   Solidity ABI's head/tail separation. For static elements, this is a plain concatenation. *)
let array (elt : 'a typ) : 'a list typ =
  let name = Format.sprintf "%s[]" elt.name in
  let kind = Dynamic in
  let read enc view =
    Result.(
      Result.(
        let$ n, view = length.read enc view in
        let rec loop n acc c =
          if n <= 0 then return (List.rev acc, c)
          else
            let$ v, c = read_field elt enc c in
            loop (n - 1) (v :: acc) c
        in
        let$ vs, c = loop n [] (cursor view) in
        return (vs, finish c) ) )
  in
  let write enc vs =
    length.write enc (List.length vs) ^ arrange_fields enc (List.map (write_field elt enc) vs)
  in
  {name; kind; read; write}

(* A tuple keeps its fields' names and encodings next to its ['a typ], because function signatures and event
   topics need them individually. It also keeps their kinds and a field-by-field reader, so that it can be
   extended with further fields by [(@:)]. *)
type 'a tup =
  { typ : 'a typ
  ; field_type_names : string list
  ; field_kinds : kind list
  ; write_fields : encoding -> 'a -> (kind * Bytes.t) list
  ; read_fields : encoding -> cursor -> ('a * cursor, decode_error) result }

let field_type_names {field_type_names; _} = field_type_names
let write_fields (t : 'a tup) (enc : encoding) (v : 'a) : Bytes.t list = List.map snd (t.write_fields enc v)

let tuple (t : 'a tup) : 'a typ = t.typ

let tuple_kind (kinds : kind list) : kind =
  List.fold_left
    (fun acc kind ->
      match (acc, kind) with
      | Static a, Static b ->
          Static
            { abi_word_width = a.abi_word_width + b.abi_word_width
            ; packed_byte_width = a.packed_byte_width + b.packed_byte_width }
      | _ -> Dynamic )
    (Static {abi_word_width = 0; packed_byte_width = 0})
    kinds

let make_tuple
    ~(names : string list)
    ~(kinds : kind list)
    ~(write_fields : encoding -> 'a -> (kind * Bytes.t) list)
    ~(read_fields : encoding -> cursor -> ('a * cursor, decode_error) result) : 'a tup =
  let typ =
    { name = Format.sprintf "(%s)" (String.concat "," names)
    ; kind = tuple_kind kinds
    ; write = (fun enc v -> arrange_fields enc (write_fields enc v))
    ; read =
        (fun enc view ->
          Result.(
            let$ v, c = read_fields enc (cursor view) in
            return (v, finish c) ) ) }
  in
  {typ; field_type_names = names; field_kinds = kinds; write_fields; read_fields}

let nil : unit tup =
  make_tuple ~names:[] ~kinds:[] ~write_fields:(fun _ () -> []) ~read_fields:(fun _ c -> Ok ((), c))

(* [a @: rest] prepends a field of type [a] to the tuple [rest]. Since [(@:)] is right-associative,
   [a @: b @: nil] is the type [a * (b * unit)]. *)
let ( @: ) (a : 'a typ) (rest : 'b tup) : ('a * 'b) tup =
  make_tuple ~names:(a.name :: rest.field_type_names) ~kinds:(a.kind :: rest.field_kinds)
    ~write_fields:(fun enc (x, xs) -> write_field a enc x :: rest.write_fields enc xs)
    ~read_fields:(fun enc c ->
      Result.(
        let$ x, c = read_field a enc c in
        let$ xs, c = rest.read_fields enc c in
        return ((x, xs), c) ) )

(* [map_tuple ~encode ~decode t] is the tuple [t] with its values transformed by [encode] when writing and by
   [decode] when reading. Its fields, and therefore its encoding, are those of [t]. This is used to convert
   between the nested pairs built by [(@:)] and flat OCaml tuples. *)
let map_tuple ~(encode : 'a -> 'r) ~(decode : 'r -> 'a) (t : 'r tup) : 'a tup =
  make_tuple ~names:t.field_type_names ~kinds:t.field_kinds
    ~write_fields:(fun enc v -> t.write_fields enc (encode v))
    ~read_fields:(fun enc c ->
      Result.(
        let$ r, c = t.read_fields enc c in
        return (decode r, c) ) )

let tup0 : unit tup = nil

let tup1 (a1 : 'a1 typ) : 'a1 tup =
  map_tuple ~encode:(fun x1 -> (x1, ())) ~decode:(fun (x1, ()) -> x1) (a1 @: nil)

let tup2 (a1 : 'a1 typ) (a2 : 'a2 typ) : ('a1 * 'a2) tup =
  map_tuple ~encode:(fun (x1, x2) -> (x1, (x2, ()))) ~decode:(fun (x1, (x2, ())) -> (x1, x2)) (a1 @: a2 @: nil)

let tup3 (a1 : 'a1 typ) (a2 : 'a2 typ) (a3 : 'a3 typ) : ('a1 * 'a2 * 'a3) tup =
  map_tuple
    ~encode:(fun (x1, x2, x3) -> (x1, (x2, (x3, ()))))
    ~decode:(fun (x1, (x2, (x3, ()))) -> (x1, x2, x3))
    (a1 @: a2 @: a3 @: nil)

let tup4 (a1 : 'a1 typ) (a2 : 'a2 typ) (a3 : 'a3 typ) (a4 : 'a4 typ) : ('a1 * 'a2 * 'a3 * 'a4) tup =
  map_tuple
    ~encode:(fun (x1, x2, x3, x4) -> (x1, (x2, (x3, (x4, ())))))
    ~decode:(fun (x1, (x2, (x3, (x4, ())))) -> (x1, x2, x3, x4))
    (a1 @: a2 @: a3 @: a4 @: nil)

let tup5 (a1 : 'a1 typ) (a2 : 'a2 typ) (a3 : 'a3 typ) (a4 : 'a4 typ) (a5 : 'a5 typ) :
    ('a1 * 'a2 * 'a3 * 'a4 * 'a5) tup =
  map_tuple
    ~encode:(fun (x1, x2, x3, x4, x5) -> (x1, (x2, (x3, (x4, (x5, ()))))))
    ~decode:(fun (x1, (x2, (x3, (x4, (x5, ()))))) -> (x1, x2, x3, x4, x5))
    (a1 @: a2 @: a3 @: a4 @: a5 @: nil)

let tup6 (a1 : 'a1 typ) (a2 : 'a2 typ) (a3 : 'a3 typ) (a4 : 'a4 typ) (a5 : 'a5 typ) (a6 : 'a6 typ) :
    ('a1 * 'a2 * 'a3 * 'a4 * 'a5 * 'a6) tup =
  map_tuple
    ~encode:(fun (x1, x2, x3, x4, x5, x6) -> (x1, (x2, (x3, (x4, (x5, (x6, ())))))))
    ~decode:(fun (x1, (x2, (x3, (x4, (x5, (x6, ())))))) -> (x1, x2, x3, x4, x5, x6))
    (a1 @: a2 @: a3 @: a4 @: a5 @: a6 @: nil)

let tup7
    (a1 : 'a1 typ) (a2 : 'a2 typ) (a3 : 'a3 typ) (a4 : 'a4 typ) (a5 : 'a5 typ) (a6 : 'a6 typ) (a7 : 'a7 typ) :
    ('a1 * 'a2 * 'a3 * 'a4 * 'a5 * 'a6 * 'a7) tup =
  map_tuple
    ~encode:(fun (x1, x2, x3, x4, x5, x6, x7) -> (x1, (x2, (x3, (x4, (x5, (x6, (x7, ()))))))))
    ~decode:(fun (x1, (x2, (x3, (x4, (x5, (x6, (x7, ()))))))) -> (x1, x2, x3, x4, x5, x6, x7))
    (a1 @: a2 @: a3 @: a4 @: a5 @: a6 @: a7 @: nil)

let tup8
    (a1 : 'a1 typ)
    (a2 : 'a2 typ)
    (a3 : 'a3 typ)
    (a4 : 'a4 typ)
    (a5 : 'a5 typ)
    (a6 : 'a6 typ)
    (a7 : 'a7 typ)
    (a8 : 'a8 typ) : ('a1 * 'a2 * 'a3 * 'a4 * 'a5 * 'a6 * 'a7 * 'a8) tup =
  map_tuple
    ~encode:(fun (x1, x2, x3, x4, x5, x6, x7, x8) -> (x1, (x2, (x3, (x4, (x5, (x6, (x7, (x8, ())))))))))
    ~decode:(fun (x1, (x2, (x3, (x4, (x5, (x6, (x7, (x8, ())))))))) -> (x1, x2, x3, x4, x5, x6, x7, x8))
    (a1 @: a2 @: a3 @: a4 @: a5 @: a6 @: a7 @: a8 @: nil)

let tup9
    (a1 : 'a1 typ)
    (a2 : 'a2 typ)
    (a3 : 'a3 typ)
    (a4 : 'a4 typ)
    (a5 : 'a5 typ)
    (a6 : 'a6 typ)
    (a7 : 'a7 typ)
    (a8 : 'a8 typ)
    (a9 : 'a9 typ) : ('a1 * 'a2 * 'a3 * 'a4 * 'a5 * 'a6 * 'a7 * 'a8 * 'a9) tup =
  map_tuple
    ~encode:(fun (x1, x2, x3, x4, x5, x6, x7, x8, x9) ->
      (x1, (x2, (x3, (x4, (x5, (x6, (x7, (x8, (x9, ()))))))))) )
    ~decode:(fun (x1, (x2, (x3, (x4, (x5, (x6, (x7, (x8, (x9, ()))))))))) ->
      (x1, x2, x3, x4, x5, x6, x7, x8, x9) )
    (a1 @: a2 @: a3 @: a4 @: a5 @: a6 @: a7 @: a8 @: a9 @: nil)

let tup10
    (a1 : 'a1 typ)
    (a2 : 'a2 typ)
    (a3 : 'a3 typ)
    (a4 : 'a4 typ)
    (a5 : 'a5 typ)
    (a6 : 'a6 typ)
    (a7 : 'a7 typ)
    (a8 : 'a8 typ)
    (a9 : 'a9 typ)
    (a10 : 'a10 typ) : ('a1 * 'a2 * 'a3 * 'a4 * 'a5 * 'a6 * 'a7 * 'a8 * 'a9 * 'a10) tup =
  map_tuple
    ~encode:(fun (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) ->
      (x1, (x2, (x3, (x4, (x5, (x6, (x7, (x8, (x9, (x10, ())))))))))) )
    ~decode:(fun (x1, (x2, (x3, (x4, (x5, (x6, (x7, (x8, (x9, (x10, ())))))))))) ->
      (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) )
    (a1 @: a2 @: a3 @: a4 @: a5 @: a6 @: a7 @: a8 @: a9 @: a10 @: nil)

let tup11
    (a1 : 'a1 typ)
    (a2 : 'a2 typ)
    (a3 : 'a3 typ)
    (a4 : 'a4 typ)
    (a5 : 'a5 typ)
    (a6 : 'a6 typ)
    (a7 : 'a7 typ)
    (a8 : 'a8 typ)
    (a9 : 'a9 typ)
    (a10 : 'a10 typ)
    (a11 : 'a11 typ) : ('a1 * 'a2 * 'a3 * 'a4 * 'a5 * 'a6 * 'a7 * 'a8 * 'a9 * 'a10 * 'a11) tup =
  map_tuple
    ~encode:(fun (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11) ->
      (x1, (x2, (x3, (x4, (x5, (x6, (x7, (x8, (x9, (x10, (x11, ()))))))))))) )
    ~decode:(fun (x1, (x2, (x3, (x4, (x5, (x6, (x7, (x8, (x9, (x10, (x11, ()))))))))))) ->
      (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11) )
    (a1 @: a2 @: a3 @: a4 @: a5 @: a6 @: a7 @: a8 @: a9 @: a10 @: a11 @: nil)

let tup12
    (a1 : 'a1 typ)
    (a2 : 'a2 typ)
    (a3 : 'a3 typ)
    (a4 : 'a4 typ)
    (a5 : 'a5 typ)
    (a6 : 'a6 typ)
    (a7 : 'a7 typ)
    (a8 : 'a8 typ)
    (a9 : 'a9 typ)
    (a10 : 'a10 typ)
    (a11 : 'a11 typ)
    (a12 : 'a12 typ) : ('a1 * 'a2 * 'a3 * 'a4 * 'a5 * 'a6 * 'a7 * 'a8 * 'a9 * 'a10 * 'a11 * 'a12) tup =
  map_tuple
    ~encode:(fun (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
      (x1, (x2, (x3, (x4, (x5, (x6, (x7, (x8, (x9, (x10, (x11, (x12, ())))))))))))) )
    ~decode:(fun (x1, (x2, (x3, (x4, (x5, (x6, (x7, (x8, (x9, (x10, (x11, (x12, ())))))))))))) ->
      (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) )
    (a1 @: a2 @: a3 @: a4 @: a5 @: a6 @: a7 @: a8 @: a9 @: a10 @: a11 @: a12 @: nil)

let unit : unit typ = {(tuple nil) with name = "unit"}

let option ~(equal : 'a -> 'a -> bool) ~(empty : 'a) (typ : 'a typ) : 'a option typ =
  map
    ~name:(Format.sprintf "Option<%s>" typ.name)
    ~encode:(function None -> empty | Some v -> v)
    ~decode:(fun v -> Ok (if equal empty v then None else Some v))
    typ

(* The Solidity ABI treats addresses as integers in that they are right-aligned. Defined outside [Address]
   because [Chain.Ethereum.Address] has its own [map]. *)
let address : Chain.Ethereum.Address.t typ =
  map ~name:"address" ~encode:Fun.id ~decode:Result.return (fixed_bytes (module Chain.Ethereum.Address) Right)

module Address = struct
  include Chain.Ethereum.Address
  let t : t typ = address
  let t_option : t option typ = option ~equal ~empty:zero t
end

module B33 = struct
  include B33
  let t = fixed_bytes (module B33) Left
end

module B48 = struct
  include B48
  let t = fixed_bytes (module B48) Left
end

module type UINT = sig
  module Repr : FIXED_BYTES
  type t
  val to_repr : t -> Repr.t
  val of_repr : Repr.t -> t
end

let uint (module M : UINT) : M.t typ =
  let open M in
  map
    ~name:(Format.sprintf "uint%d" (Repr.byte_width * 8))
    ~encode:(fun x -> to_repr x)
    ~decode:(fun r -> Ok (of_repr r))
    (fixed_bytes (module Repr) Right)

module U256 = struct
  include U256
  let t = uint (module U256)
end

module U64 = struct
  include U64
  let t = uint (module U64)
end

module U8 = struct
  include U8
  let t = uint (module U8)
end

module U32 = struct
  include U32
  let t = uint (module U32)
end

let bool : bool typ =
  (* abicoder v1 is unclear on how to treat a bool field with spurious bits. The Solidity compiler emits
     ISZERO so we use the same logic here. *)
  map ~name:"bool"
    ~encode:(fun b -> if b then U256.one else U256.zero)
    ~decode:(fun u -> Ok U256.(u <> zero))
    U256.t

let packed ?(name : string option) (ty : 'a typ) : 'a typ =
  let packed_byte_width =
    match ty.kind with
    | Static {packed_byte_width; _} -> packed_byte_width
    | Dynamic -> failwith (Format.sprintf "Packing non-static type %s" ty.name)
  in
  let name = match name with None -> Format.sprintf "Packed<%s>" ty.name | Some name -> name in
  let kind = Static {abi_word_width = bytes_to_whole_words packed_byte_width; packed_byte_width} in
  let read enc view =
    Result.(
      let$ bs, view = read_fixed enc Left packed_byte_width view in
      let$ v, _ = ty.read Packed (Input_view.of_bytes bs) in
      return (v, view) )
  in
  let write enc v = write_fixed enc Left (ty.write Packed v) in
  {name; kind; read; write}

let enc_bytes (typ : 'a typ) (v : 'a) : Bytes.t = typ.write Abi v

let enc (typ : 'a typ) (v : 'a) : B32.t list =
  let bs = enc_bytes typ v in
  (* This never fails because enc_bytes always produces word-aligned outputs. *)
  List.init (Bytes.length bs / 32) (fun i -> B32.sub bs (i * 32))

let dec (typ : 'a typ) (view : Input_view.t) : ('a * Input_view.t, decode_error) result = typ.read Abi view

let dec_bytes (typ : 'a typ) (bytes : Bytes.t) : ('a, decode_error) result =
  Result.(
    let$ v, view = dec typ (Input_view.of_bytes bytes) in
    let$ () = ensure (Input_view.is_empty view) ~or_error:Input_too_long in
    return v )
