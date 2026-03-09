(** Generic number types backed by Zarith unbounded integers. The functor {!Numeric.Make} can be instantiated
    with a choice of signedness and bit width to produce an opaque type representing (un)signed integers of
    the corresponding width.

    Note that the {!Numeric.Make} functor is applicative, therefore multiple instantiations with the same
    parameter result in interchangeable numeric types.
 *)

open Byte_string

exception Domain_error of Z.t
exception Invalid_operation

module Make (Byte_width : Traits.Byte_width.SIG) (Signedness : Traits.Signedness.SIG) = struct
  module Impl : sig
    type t

    val signed : bool

    val max_t : t option
    val min_t : t option

    val in_range : Z.t -> bool

    val of_z_opt : Z.t -> t option
    val of_z_truncating : (Z.t -> t) option

    val to_z : t -> Z.t

    val testbit : t -> int -> bool
  end = struct
    type t = Z.t

    let signed = match Signedness.signedness with `Signed -> true | `Unsigned -> false

    let bit_width = match Byte_width.byte_width with `Fixed n -> Some (8 * n) | `Variable -> None

    let max_t =
      match (bit_width, signed) with
      | None, _ -> None
      | Some bits, true -> Some Z.((~$2 ** Stdlib.(bits - 1)) - one)
      | Some bits, false -> Some Z.((~$2 ** bits) - one)

    let min_t =
      match (bit_width, signed) with
      | _, false -> Some Z.zero
      | Some bits, true -> Some Z.(zero - (~$2 ** Stdlib.(bits - 1)))
      | None, true -> None

    let in_range =
      let big_enough = match min_t with None -> fun _x -> true | Some min_t -> fun x -> Z.(geq x min_t) in
      let small_enough = match max_t with None -> fun _x -> true | Some max_t -> fun x -> Z.(leq x max_t) in
      fun x -> big_enough x && small_enough x

    let of_z_opt (x : Z.t) = if not (in_range x) then None else Some x

    let of_z_truncating =
      match (bit_width, signed) with
      | None, _ -> None
      | Some bits, true -> Some (fun x -> Z.signed_extract x 0 bits)
      | Some bits, false -> Some (fun x -> Z.extract x 0 bits)

    let to_z x = x

    let testbit x i = Z.testbit x i
  end

  include Impl

  let of_z_exn (x : Z.t) = match of_z_opt x with None -> raise (Domain_error x) | Some x -> x

  let zero = of_z_exn Z.zero
  let one = of_z_exn Z.one

  (** [byte ~index-le x] extracts the [i]-th byte from the Little-endian representation of [x]. *)
  let byte ~index_le x =
    let le_bytes = Z.to_bits (to_z x) in
    if index_le >= String.length le_bytes then '\x00' else le_bytes.[index_le]

  let significant_bytes x = (Z.numbits (to_z x) + 7) / 8

  let of_bool b = if b then one else zero

  let of_byte c = of_z_exn (Z.of_int (Char.code c))
  let of_int i = of_z_exn (Z.of_int i)
  let ( ~$ ) = of_int

  let to_int x = Z.to_int (to_z x)
  let to_int_opt x =
    let x = to_z x in
    if Z.fits_int x then Some (Z.to_int x) else None

  let of_uint64 i = of_z_exn (Z.of_int64_unsigned i)
  let of_int64 i = of_z_exn (Z.of_int64 i)
  let to_uint64 x = Z.to_int64_unsigned (to_z x)
  let to_int64 x = Z.to_int64 (to_z x)

  let hash x = Z.hash (to_z x)

  include Comparable.Make (struct
    type t = Impl.t

    (* Will be signed or unsigned depending on the signedness of the module *)
    let compare (x : t) (y : t) = Z.compare (to_z x) (to_z y)
  end)

  let is_zero x = x = zero
  module Hashtbl = Hashtbl.Make (struct
    type t = Impl.t
    let hash = hash
    let equal = equal
  end)

  let to_string x = Z.to_string (to_z x)
  let to_hex_string x = Z.format "%#x" (to_z x)

  let of_string s = of_z_exn (Z.of_string s)
  let ( ~@ ) = of_string

  (* JSON conversions. *)
  let of_yojson (x : Yojson.Safe.t) =
    let parse_error str = Error (Format.sprintf "Cannot parse %s as numeric" str) in
    match x with
    | `String str -> ( try Ok (of_string str) with _ -> parse_error str )
    | `Int i -> Ok (of_int i)
    | `Intlit lit -> ( try Ok (of_string lit) with _ -> parse_error lit )
    | _ -> Error "Expected int or string"
  let of_yojson_exn (x : Yojson.Safe.t) = Result.get_ok (of_yojson x)
  let to_yojson (x : t) : Yojson.Safe.t = `String (to_hex_string x)

  (* JSON conversions for t-indexed maps. *)
  module Map : sig
    include module type of Map

    val of_yojson : (Yojson.Safe.t -> ('elt, string) result) -> Yojson.Safe.t -> ('elt t, string) result
    val to_yojson : ('elt -> Yojson.Safe.t) -> 'elt t -> Yojson.Safe.t
  end = struct
    include Map

    exception Value_decoding_error of string

    let of_yojson elt_of_yojson (json : Yojson.Safe.t) : ('elt t, string) result =
      match json with
      | `Assoc pairs -> (
        try
          Ok
            ( List.to_seq pairs
            |> Seq.map (fun (k, v) ->
                ( of_string k
                , match elt_of_yojson v with Ok elt -> elt | Error msg -> raise (Value_decoding_error msg) ) )
            |> Map.of_seq )
        with Value_decoding_error err -> Error err )
      | _ -> Error "map"

    let to_yojson elt_to_yojson (map : 'elt t) : Yojson.Safe.t =
      to_seq map
      |> Seq.map (fun (k, v) -> (to_hex_string k, elt_to_yojson v))
      |> List.of_seq
      |> fun entries -> `Assoc entries
  end

  let of_z_after_op = match of_z_truncating with Some of_z -> of_z | None -> of_z_exn

  let lift_1 f = fun x -> of_z_after_op (f (to_z x))

  let lift_2 (f : Z.t -> Z.t -> Z.t) = fun x y -> of_z_after_op (f (to_z x) (to_z y))

  let logand = lift_2 Z.logand
  let logor = lift_2 Z.logor
  let logxor = lift_2 Z.logxor
  let lognot = lift_1 Z.lognot

  let ( + ) = lift_2 Z.( + )
  let ( - ) = lift_2 Z.( - )
  let ( * ) = lift_2 Z.( * )
  let ( / ) = lift_2 Z.( / )

  (* Will be signed or unsigned depending on the signedness of the module. *)
  let modulo = lift_2 Z.rem

  let addmod x y m = of_z_after_op Z.(rem (to_z x + to_z y) (to_z m))
  let mulmod x y m = of_z_after_op Z.(rem (to_z x * to_z y) (to_z m))

  let shift_left x (shift : int) = of_z_after_op (Z.shift_left (to_z x) shift)
  let shift_right x shift = of_z_after_op (Z.shift_right (to_z x) shift)

  let ( ** ) base exp = of_z_after_op (Z.pow (to_z base) exp)

  let exp x y =
    match to_int_opt y with
    | Some y -> x ** y
    | None ->
        let rec loop acc mul y =
          if y = zero then acc
          else
            let acc = if modulo y ~$2 = ~$1 then acc * mul else acc in
            let mul = mul * mul in
            let y = y / ~$2 in
            loop acc mul y
        in
        loop ~$1 x y

  (* Not constant-time. *)
  let exp_mod ~(modulo : t) (x : t) (y : t) = of_z_after_op (Z.powm (to_z x) (to_z y) (to_z modulo))

  (* YP (331) *)
  let minus_1_64th (x : t) : t = x - (x / ~$64)

  (** [bytes_to_whole_words x] computes {m ceil(x / 32)}. *)
  let bytes_to_whole_words (x : t) =
    let q, r = Z.div_rem (to_z x) (Z.of_int 32) in
    of_z_exn q + if Z.(equal r zero) then zero else one
end

module UintBase = Make (Traits.Byte_width.Variable) (Traits.Signedness.Unsigned)
module IntegerBase = Make (Traits.Byte_width.Variable) (Traits.Signedness.Signed)
module Uint = struct
  include UintBase

  let as_signed (x : t) : IntegerBase.t = IntegerBase.of_z_exn (to_z x)

  let of_bytes_be (bs : Bytes.t) =
    (* This will never throw, as Z.of_bits always returns a positive integer. *)
    of_z_exn (Z.of_bits (Bytes.reverse bs))
  let to_bytes_be (x : t) =
    let bytes_le = Z.to_bits (to_z x) in
    let sig_bytes = significant_bytes x in
    (* Z.to_bits may return more bytes than we need because it does the conversion one limb at a
       time. When limbs are 64 bits, this means we get e.g. 24 bytes for a 160-bit number. The
       code below handles truncating and reversing. *)
    let byte_i i = bytes_le.[Stdlib.(sig_bytes - i - 1)] in
    Bytes.init sig_bytes byte_i

  let of_rlp (rlp : Rlp.t) : t option = match rlp with Bytes bs -> Some (of_bytes_be bs) | List _ -> None
  let to_rlp (x : t) : Rlp.t = Rlp.Bytes (to_bytes_be x)
end
module Integer = struct
  include IntegerBase

  let as_unsigned_exn (x : t) : Uint.t = Uint.of_z_exn (to_z x)
end

(** Helper functor to create pairs of signed and unsigned types for a given bit width, together with conversion
    functions via two's complement. *)
module TwosComplement (B : sig
  val byte_width : [> `Fixed of int]
end) =
struct
  module S = Make (B) (Traits.Signedness.Signed)
  module U = Make (B) (Traits.Signedness.Unsigned)
  let max_unsigned = U.(Option.get max_t)
  let min_unsigned = U.(Option.get min_t)
  let max_signed = S.(Option.get max_t)
  let min_signed = S.(Option.get min_t)
  let bit_width, byte_width =
    match B.byte_width with
    | `Fixed n ->
        assert (n > 0) ;
        (n * 8, n)

  module Signed = struct
    include S
    module Repr = Byte_string.Fixed (B)
    let bit_width, byte_width = (bit_width, byte_width)
    let max_t, min_t = (max_signed, min_signed)
    let of_z_truncating = Option.get of_z_truncating

    let of_repr (bs : Repr.t) : t =
      (* This should never throw, as Repr.t is guaranteed to have the same byte-width as t. *)
      let x_abs = Z.of_bits (Repr.reverse bs :> string) in
      let negative = Z.testbit x_abs Stdlib.(bit_width - 1) in
      if negative then of_z_exn Z.(zero - x_abs) else of_z_exn x_abs

    let to_repr (x : t) : Repr.t =
      let z_bytes = Z.to_bits (to_z x) in
      let z_n_bytes = String.length z_bytes in
      Repr.init (fun i ->
          (* Z.to_bits may return more bytes than we need because it does the conversion one limb at a
                 time. When limbs are 64 bits, this means we get e.g. 24 bytes for a 160-bit number. The
                 code below handles truncating, reversing and optionally zero-padding *)
          let le_i = Stdlib.(byte_width - i - 1) in
          if Stdlib.(le_i >= z_n_bytes) then '\x00' else z_bytes.[le_i] )

    (** [as_unsigned x] reinterprets the binary representation of [x] (in two's complement) as an unsigned
        integer of the same bit-width. *)
    let as_unsigned (x : t) : U.t =
      let x = to_z x in
      U.of_z_exn Z.(if geq x zero then x else U.to_z max_unsigned + x + one)
  end

  module Unsigned = struct
    include U
    module Repr = Byte_string.Fixed (B)
    let bit_width, byte_width = (bit_width, byte_width)
    let max_t, min_t = (max_unsigned, min_unsigned)
    let of_z_truncating = Option.get of_z_truncating

    let of_repr (bs : Repr.t) : t =
      (* This should never throw, as Repr.t is guaranteed to have the same byte-width as t. *)
      of_z_exn (Z.of_bits (Byte_string.Bytes.reverse (bs :> string)))

    let to_repr (x : t) : Repr.t =
      let z_bytes = Z.to_bits (to_z x) in
      let z_n_bytes = String.length z_bytes in
      Repr.init (fun i ->
          (* Z.to_bits may return more bytes than we need because it does the conversion one limb at a
                 time. When limbs are 64 bits, this means we get e.g. 24 bytes for a 160-bit number. The
                 code below handles truncating, reversing and optionally zero-padding *)
          let le_i = Stdlib.(byte_width - i - 1) in
          if Stdlib.(le_i >= z_n_bytes) then '\x00' else z_bytes.[le_i] )
    let to_repr_bytes (x : t) : Bytes.t = Repr.to_bytes (to_repr x)

    (** [as_signed x] reinterprets the binary representation of [x] as a two's complement signed integer
        of the same bit-width. *)
    let as_signed (x : t) : Signed.t =
      let x = to_z x in
      Signed.of_z_exn Z.(if leq x (S.to_z max_signed) then x else x - U.to_z max_unsigned - one)

    (** [sign_extend i x] fills the bytes after [i] with the most significant bit of the [i]th bit of x. *)
    let sign_extend byte_i (x : t) : Signed.t =
      let bit_i = Stdlib.(7 + (8 * byte_i)) in
      Signed.of_z_exn (Z.signed_extract (to_z x) 0 Stdlib.(1 + bit_i))

    let to_uint (x : t) : Uint.t = Uint.of_z_exn (to_z x)
    let of_uint_opt (x : Uint.t) = of_z_opt (Uint.to_z x)
    let of_uint_exn (x : Uint.t) : t = of_z_exn (Uint.to_z x)
    let of_uint_truncating (x : Uint.t) : t = of_z_truncating (Uint.to_z x)

    let of_bytes_be_exn (bs : Bytes.t) = of_uint_exn (Uint.of_bytes_be bs)
    let to_bytes_be (x : t) = Uint.to_bytes_be (to_uint x)

    let of_signed_int (x : int) = Signed.(as_unsigned ~$x)

    let to_rlp (x : t) = Uint.to_rlp (to_uint x)
    let of_rlp (rlp : Rlp.t) =
      Option.(
        let$ uint = Uint.of_rlp rlp in
        of_uint_opt uint )
  end
end

module Bits256 = TwosComplement (Traits.Byte_width.Bytes32)

(** Unsigned 256-bit integers. {!U256.t} is used to represent Ethereum 256-bit words. *)
module U256 = Bits256.Unsigned

(** Signed 256-bit integers. {!I256.t} is used for signed arithmetic on Ethereum 256-bit words. *)
module I256 = Bits256.Signed

(** Signed and unsigned 128-bit integers. {!U128.t} is used for Monad header timestamps. *)
module Bits128 = TwosComplement (Traits.Byte_width.Bytes16)

module U128 = Bits128.Unsigned
module I128 = Bits128.Signed

(** Signed and unsigned 64-bit integers. More operations than the versions in stdlib. *)
module Bits64 = TwosComplement (Traits.Byte_width.Bytes8)

module U64 = Bits64.Unsigned
module I64 = Bits64.Signed

(** Signed and unsigned 32-bit integers. More operations than the versions in stdlib. *)
module Bits32 = TwosComplement (Traits.Byte_width.Bytes4)

module U32 = Bits32.Unsigned
module I32 = Bits32.Signed

(** Single-byte integers. Used specificaly to represent a parity bit, which is encoded as a byte. *)
module Bits8 = TwosComplement (Traits.Byte_width.Bytes1)

module U8 = Bits8.Unsigned
