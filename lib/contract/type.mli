(** Solidity encodings of OCaml values. *)

open Byte_string
open Numeric

type decode_error =
  | Input_too_short
  | Input_too_long
  | Length_overflow
  | Map_error of {name : string; message : string}

(** Byte iterators, constructed from either a byte string or the storage. *)
module Input_view : sig
  type t
  val of_bytes : Bytes.t -> t
  val of_storage : Chain.Ethereum.Storage.t -> offset:U256.t -> t

  val take_bytes : int -> t -> (Bytes.t * t) option
  val take_word : t -> (B32.t * t) option
  val drop_bytes : int -> t -> t option

  val is_empty : t -> bool
end

type alignment = Left | Right

(** The encoding scheme to use for reading and writing a type. [Abi] is the Solidity ABI encoding, where every
    primitive value is padded to a whole number of 32-byte words. It is used for calldata, return data and logs.
    [Packed] concatenates primitive values without padding. It is used for the storage representation of the
    datatypes used by the staking contract.
    For the most part, we do not use encodings explicitly when reading/writing, instead always preferring the
    [Abi] encoding and resorting to the {!packed} type constructor when a specific type should use the
    [Packed] representation. *)
type encoding = Abi | Packed

(** Following the Solidity ABI, types are either static (when the byte width is fixed) or dynamic (when the
    byte width may vary across elements of the same type). Note that the abi-encoded word width of a static
    type may not match its packed-encoding byte width: this is the case for e.g. a tuple of two bools, which
    has an abi-encoded word width of 2 but a packed-encoded byte width of 32. *)
type kind = Static of {abi_word_width : int; packed_byte_width : int} | Dynamic

val bytes_to_padded_bytes : int -> int

type 'a typ
val name : 'a typ -> string
val kind : 'a typ -> kind
val read : 'a typ -> encoding -> Input_view.t -> ('a * Input_view.t, decode_error) result
val write : 'a typ -> encoding -> 'a -> Bytes.t

val bytes : Bytes.t typ
(** The type [bytes] corresponds to Solidity's dynamically-sized [bytes]. *)

module type FIXED_BYTES = sig
  type t
  val byte_width : int
  val of_bytes_exn : Bytes.t -> t
  val to_bytes : t -> Bytes.t
end

val fixed_bytes : (module M : FIXED_BYTES) -> alignment -> M.t typ
(** The type [fixed_bytes BS Left] corresponds to Solidity's [bytes<BS.byte_width>] type. The type
    [fixed_bytes BS Right] is a right-aligned version of it that is used as the underlying representation of
    Solidity's numeric types such as [int<64>] (which is backed by [fixed_bytes B8 Right]).
    Note that unlike Solidity's fixed bytes type, these can have byte widths greater than 32. *)

module Address : sig
  include module type of Chain.Ethereum.Address
  val t : t typ
end

module B33 : sig
  include module type of B33
  val t : t typ
end

module B48 : sig
  include module type of B48
  val t : t typ
end

module type UINT = sig
  module Repr : FIXED_BYTES
  type t
  val to_repr : t -> Repr.t
  val of_repr : Repr.t -> t
end

val uint : (module M : UINT) -> M.t typ
(** The type [uint M] corresponds to Solidity's [uint<8*M.Repr.byte_width>] type. *)

module U256 : sig
  include module type of U256
  val t : t typ
end

module U64 : sig
  include module type of U64
  val t : t typ
end

module U8 : sig
  include module type of U8
  val t : t typ
end

module U32 : sig
  include module type of U32
  val t : t typ
end

val bool : bool typ

val unit : unit typ

val option : equal:('a -> 'a -> bool) -> empty:'a -> 'a typ -> 'a option typ
(** The type [option ~equal ~empty typ] has the same representation as [typ] except when the underlying object
    is equal to [empty], it is read as [None]. Conversely, [None] is stored as [empty]. *)

val array : 'a typ -> 'a list typ
(** The type [array typ] corresponds to Solidity's [typ\[\]] dynamic array type. *)

type 'a tup
val field_type_names : 'a tup -> string list
val write_fields : 'a tup -> encoding -> 'a -> Bytes.t list

val nil : unit tup
val ( @: ) : 'a typ -> 'b tup -> ('a * 'b) tup

(* Tuple constructors - not strictly necessary as tuples can be built with the [@:] operator but these avoid
   constructing long chains of nested, right-associated 2-tuples. *)
val tup0 : unit tup
val tup1 : 'a1 typ -> 'a1 tup
val tup2 : 'a1 typ -> 'a2 typ -> ('a1 * 'a2) tup
val tup3 : 'a1 typ -> 'a2 typ -> 'a3 typ -> ('a1 * 'a2 * 'a3) tup
val tup4 : 'a1 typ -> 'a2 typ -> 'a3 typ -> 'a4 typ -> ('a1 * 'a2 * 'a3 * 'a4) tup
val tup5 : 'a1 typ -> 'a2 typ -> 'a3 typ -> 'a4 typ -> 'a5 typ -> ('a1 * 'a2 * 'a3 * 'a4 * 'a5) tup
val tup6 :
  'a1 typ -> 'a2 typ -> 'a3 typ -> 'a4 typ -> 'a5 typ -> 'a6 typ -> ('a1 * 'a2 * 'a3 * 'a4 * 'a5 * 'a6) tup
val tup7 :
     'a1 typ
  -> 'a2 typ
  -> 'a3 typ
  -> 'a4 typ
  -> 'a5 typ
  -> 'a6 typ
  -> 'a7 typ
  -> ('a1 * 'a2 * 'a3 * 'a4 * 'a5 * 'a6 * 'a7) tup
val tup8 :
     'a1 typ
  -> 'a2 typ
  -> 'a3 typ
  -> 'a4 typ
  -> 'a5 typ
  -> 'a6 typ
  -> 'a7 typ
  -> 'a8 typ
  -> ('a1 * 'a2 * 'a3 * 'a4 * 'a5 * 'a6 * 'a7 * 'a8) tup
val tup9 :
     'a1 typ
  -> 'a2 typ
  -> 'a3 typ
  -> 'a4 typ
  -> 'a5 typ
  -> 'a6 typ
  -> 'a7 typ
  -> 'a8 typ
  -> 'a9 typ
  -> ('a1 * 'a2 * 'a3 * 'a4 * 'a5 * 'a6 * 'a7 * 'a8 * 'a9) tup
val tup10 :
     'a1 typ
  -> 'a2 typ
  -> 'a3 typ
  -> 'a4 typ
  -> 'a5 typ
  -> 'a6 typ
  -> 'a7 typ
  -> 'a8 typ
  -> 'a9 typ
  -> 'a10 typ
  -> ('a1 * 'a2 * 'a3 * 'a4 * 'a5 * 'a6 * 'a7 * 'a8 * 'a9 * 'a10) tup
val tup11 :
     'a1 typ
  -> 'a2 typ
  -> 'a3 typ
  -> 'a4 typ
  -> 'a5 typ
  -> 'a6 typ
  -> 'a7 typ
  -> 'a8 typ
  -> 'a9 typ
  -> 'a10 typ
  -> 'a11 typ
  -> ('a1 * 'a2 * 'a3 * 'a4 * 'a5 * 'a6 * 'a7 * 'a8 * 'a9 * 'a10 * 'a11) tup
val tup12 :
     'a1 typ
  -> 'a2 typ
  -> 'a3 typ
  -> 'a4 typ
  -> 'a5 typ
  -> 'a6 typ
  -> 'a7 typ
  -> 'a8 typ
  -> 'a9 typ
  -> 'a10 typ
  -> 'a11 typ
  -> 'a12 typ
  -> ('a1 * 'a2 * 'a3 * 'a4 * 'a5 * 'a6 * 'a7 * 'a8 * 'a9 * 'a10 * 'a11 * 'a12) tup

val tuple : 'a tup -> 'a typ

val map : name:string -> encode:('a -> 'r) -> decode:('r -> ('a, string) result) -> 'r typ -> 'a typ
(** [map ~name ~encode ~decode repr] creates a new type with underlying representation given by [repr].
    Encoding/decoding is done by encoding/decoding the underlying repr modulo the user-provided transformations
    [encode] and [decode]. *)

val packed : ?name:string -> 'a typ -> 'a typ
(** [packed ty] creates a new type which is identical to [ty] except that it is always encoded and decoded
    according to the [Packed] representation. Only static types can be packed. Calling [packed] on a dynamic
    type results in a runtime error. *)

val enc_bytes : 'a typ -> 'a -> Bytes.t
(** [enc_bytes] ABI-encodes the object [v] into a byte-string according to the type description [typ]. The
    length of the resulting byte-string is always a multiple of 32. *)

val dec_bytes : 'a typ -> Bytes.t -> ('a, decode_error) result
(** [dec_bytes] tries to ABI-decode the input [bytes] as an instance of [typ]. If there are trailing bytes,
    an error is returned. *)

val enc : 'a typ -> 'a -> B32.t list
(** [enc] ABI-encodes the object [v] into a word sequence according to the type description [typ]. *)

val dec : 'a typ -> Input_view.t -> ('a * Input_view.t, decode_error) result
(** [dec] tries to ABI-decode an instance of [typ] from the input view [view]. *)
