(** Typed Solidity codecs. Construction through these combinators keeps each
    codec's type name, layout, encoder and decoder consistent. *)
open Byte_string

type alignment = Left | Right
type fixed_bytes = {alignment : alignment; byte_width : int}
type kind = Static of {word_width : int} | Dynamic
module Input_view : sig
  type chunk = Word of B32.t | Tail of Bytes.t
  type t = chunk Seq.t
  val of_bytes : Bytes.t -> t
  val of_storage : Chain.Ethereum.Storage.t -> offset:Numeric.U256.t -> t
  val take_word : t -> (B32.t * t) option
  val take_words : int -> t -> (Bytes.t * t) option
end

type decode_error =
  | Input_too_short
  | Input_too_long
  | Length_overflow
  | Map_error of {name : string; message : string}
type 'a decoder = Input_view.t -> ('a * Input_view.t, decode_error) result

type 'a typ
type 'a tup

type ('a, 'repr) mapping =
  {name : string; repr : 'repr typ; encode : 'a -> 'repr; decode : 'repr -> ('a, string) result}

val type_name : 'a typ -> string
val kind : 'a typ -> kind
val enc : 'a typ -> 'a -> B32.t list
val dec : 'a typ -> 'a decoder
val enc_bytes : 'a typ -> 'a -> Bytes.t
val dec_bytes : ?allow_trailing:bool -> 'a typ -> Bytes.t -> ('a, decode_error) result
val fixed_bytes : fixed_bytes -> Bytes.t typ
val bytes : Bytes.t typ
val array : 'a typ -> 'a list typ
val mapped : ('a, 'repr) mapping -> 'a typ
val option : empty:'a -> 'a typ -> 'a option typ

val tuple : 'a tup -> 'a typ
(** [tupN] describes N fields whose values are an ordinary N-tuple (unit
    for zero fields; the value itself for one). [tuple] embeds them as one
    ABI value. Function inputs and event parameters take [tup] directly. *)

val tup0 : unit tup
val tup1 : 'a1 typ -> 'a1 tup
val tup2 : 'a1 typ * 'a2 typ -> ('a1 * 'a2) tup
val tup3 : 'a1 typ * 'a2 typ * 'a3 typ -> ('a1 * 'a2 * 'a3) tup
val tup4 : 'a1 typ * 'a2 typ * 'a3 typ * 'a4 typ -> ('a1 * 'a2 * 'a3 * 'a4) tup
val tup5 : 'a1 typ * 'a2 typ * 'a3 typ * 'a4 typ * 'a5 typ -> ('a1 * 'a2 * 'a3 * 'a4 * 'a5) tup
val tup6 :
  'a1 typ * 'a2 typ * 'a3 typ * 'a4 typ * 'a5 typ * 'a6 typ -> ('a1 * 'a2 * 'a3 * 'a4 * 'a5 * 'a6) tup
val tup7 :
     'a1 typ * 'a2 typ * 'a3 typ * 'a4 typ * 'a5 typ * 'a6 typ * 'a7 typ
  -> ('a1 * 'a2 * 'a3 * 'a4 * 'a5 * 'a6 * 'a7) tup
val tup12 :
     'a1 typ
     * 'a2 typ
     * 'a3 typ
     * 'a4 typ
     * 'a5 typ
     * 'a6 typ
     * 'a7 typ
     * 'a8 typ
     * 'a9 typ
     * 'a10 typ
     * 'a11 typ
     * 'a12 typ
  -> ('a1 * 'a2 * 'a3 * 'a4 * 'a5 * 'a6 * 'a7 * 'a8 * 'a9 * 'a10 * 'a11 * 'a12) tup

val cons : 'a typ -> 'b tup -> ('a * 'b) tup
(** General tuple composition, for field counts not covered by [tupN]. *)

val map_tuple : encode:('a -> 'b) -> decode:('b -> 'a) -> 'b tup -> 'a tup
val tuple_to_canonical_type_names : 'a tup -> string list
val tuple_header_word_width : 'a tup -> int
val encode_indexed_parameters : 'a tup -> 'a -> B32.t list
val enc_tup : 'a tup -> 'a -> B32.t list
val dec_tuple : 'a tup -> 'a decoder
val dec_length : int decoder
val bytes_to_words : int -> int
val bytes_to_padded_bytes : int -> int
val align : alignment -> Bytes.t -> B32.t list

module Address : sig
  include module type of Chain.Ethereum.Address
  val t : t typ
  val t_option : t option typ
end
module Fixed_bytes (M : sig
  type t
  val to_bytes : t -> Bytes.t
  val of_bytes : Bytes.t -> t option
  val byte_width : int
end) : sig
  val t : M.t typ
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
end) : sig
  val t : M.t typ
  val t_option : M.t option typ
end
module B33 : sig
  include module type of Byte_string.B33
  val t : t typ
end
module B48 : sig
  include module type of Byte_string.B48
  val t : t typ
end
module U256 : sig
  include module type of Numeric.U256
  val t : t typ
  val t_option : t option typ
end
module U64 : sig
  include module type of Numeric.U64
  val t : t typ
  val t_option : t option typ
end
module U8 : sig
  include module type of Numeric.U8
  val t : t typ
  val t_option : t option typ
end
module U32 : sig
  include module type of Numeric.U32
  val t : t typ
  val t_option : t option typ
end
val bool : bool typ
val unit : unit typ
module Packed : sig
  val t : ?name:string -> 'a typ -> 'a typ
end
