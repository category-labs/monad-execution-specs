(** Generic number types backed by Zarith unbounded integers. The functor {!Numeric.Make} can be instantiated
    with a choice of signedness and bit width to produce an opaque type representing (un)signed integers of
    the corresponding width.

    Note that the {!Numeric.Make} functor is applicative, therefore multiple instantiations with the same
    parameter result in interchangeable numeric types.
 *)

exception Domain_error of Z.t
exception Invalid_operation

module type IS_BOUNDED = sig
  val bit_width : int option
end
module type IS_SIGNED = sig
  val v : bool
end

module Make (Bounded : IS_BOUNDED) (Signed : IS_SIGNED) = struct
  module Impl : sig
    type t

    val bit_width : int option
    val byte_width : int option

    val signed : bool

    val max_t : t option
    val min_t : t option

    val in_range : Z.t -> bool

    val of_z_exn : Z.t -> t
    val of_z_truncating : (Z.t -> t) option

    val to_z : t -> Z.t

    val testbit : t -> int -> bool
  end = struct
    type t = Z.t

    let () = ignore (Option.iter (fun b -> assert (b > 0 && b mod 8 = 0)) Bounded.bit_width)

    let bit_width = Bounded.bit_width
    let byte_width = Option.map (fun b -> b / 8) Bounded.bit_width

    let signed = Signed.v

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

    let of_z_exn (x : Z.t) =
      if not (in_range x) then raise (Domain_error x) ;
      x

    let of_z_truncating =
      match (bit_width, signed) with
      | None, _ -> None
      | Some bits, true -> Some (fun x -> Z.signed_extract x 0 bits)
      | Some bits, false -> Some (fun x -> Z.extract x 0 bits)

    let to_z x = x

    let testbit x i = Z.testbit x i
  end

  include Impl

  let zero = of_z_exn Z.zero
  let one = of_z_exn Z.one

  let of_bytes_be : Bytes.t -> t =
    match (bit_width, signed) with
    | Some bits, true ->
        fun bs ->
          let x_abs = Z.of_bits (Bytes.reverse bs) in
          let negative = Z.testbit x_abs (bits - 1) in
          if negative then of_z_exn Z.(zero - x_abs) else of_z_exn x_abs
    | None, true ->
        (* Cannot recover sign *)
        fun _bs -> raise Invalid_operation
    | _, false ->
        (* Do not truncate silently *)
        fun bs -> of_z_exn (Z.of_bits (Bytes.reverse bs))

  let to_bytes_be : t -> Bytes.t =
    match byte_width with
    | None -> fun x -> Bytes.reverse (Z.to_bits (to_z x))
    | Some byte_width ->
        fun x ->
          let z_bytes = Z.to_bits (to_z x) in
          let z_n_bytes = Bytes.length z_bytes in
          Bytes.init byte_width (fun i ->
              (* Z.to_bits may return more bytes than we need because it does the conversion one limb at a
                 time. When limbs are 64 bits, this means we get e.g. 24 bytes for a 160-bit number. The
                 code below handles truncating, reversing and optionally zero-padding *)
              if i > z_n_bytes - 1 then '\x00' else z_bytes.[z_n_bytes - 1 - i] )

  let to_bytes_le : t -> Bytes.t = fun x -> Bytes.reverse (to_bytes_be x)

  let byte i x =
    let bytes = to_bytes_be x in
    bytes.[i]

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

  (* Will be signed or unsigned depending on the signedness of the module *)
  let compare (x : t) (y : t) = Z.compare (to_z x) (to_z y)
  let equal x y = Z.equal (to_z x) (to_z y)
  let hash x = Z.hash (to_z x)

  include Comparable.Make (struct
    type t = Impl.t
    let compare = compare
  end)

  let is_zero x = x = zero
  module Hashtbl = Hashtbl.Make (struct
    type t = Impl.t
    let hash = hash
    let equal = equal
  end)

  let to_string x = Z.to_string (to_z x)
  let to_hex_string x =
    let sign = if x < zero then "-" else "" in
    Format.sprintf "%s0x%s" sign (Bytes.to_hex_string (to_bytes_be x))

  let to_short_hex_string x =
    let sign = if x < zero then "-" else "" in
    to_bytes_be x
    |> Bytes.to_seq
    |> Seq.drop_while Stdlib.(( = ) '\x00')
    |> Bytes.of_seq
    |> (fun b ->
    let len = Bytes.length b in
    if Stdlib.(len = 0) then Bytes.make 1 '\x00' else b )
    |> Bytes.to_hex_string
    |> Format.sprintf "%s0x%s" sign

  let of_string s = of_z_exn (Z.of_string s)
  let ( ~@ ) = of_string

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

  (* Will be signed or unsigned depending on the signedness of the module *)
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

  (* YP 331 *)
  let minus_1_64th (x : t) : t = x - (x / ~$64)

  (** [bytes_to_whole_words x] computes {m ceil(x / 32)}. *)
  let bytes_to_whole_words (x : t) =
    let q, r = Z.div_rem (to_z x) (Z.of_int 32) in
    of_z_exn q + if Z.(equal r zero) then zero else one
end

module Size = struct
  module Bits256 = struct
    let bit_width = Some 256
  end
  module Bits160 = struct
    let bit_width = Some 160
  end
  module Bits64 = struct
    let bit_width = Some 64
  end
  module Unbounded = struct
    let bit_width = None
  end
end

module Signedness = struct
  module Signed : IS_SIGNED = struct
    let v = true
  end
  module Unsigned : IS_SIGNED = struct
    let v = false
  end
end

module IntegerBase = Make (Size.Unbounded) (Signedness.Signed)
module UintBase = Make (Size.Unbounded) (Signedness.Unsigned)

module Uint = struct
  include UintBase

  let as_signed (x : t) : IntegerBase.t = IntegerBase.of_z_exn (to_z x)
end
module Integer = struct
  include IntegerBase

  let as_unsigned_exn (x : t) : Uint.t = Uint.of_z_exn (to_z x)
end

(** Helper functor to create pairs of signed and unsigned types for a given bit width, together with conversion
    functions via two's complement. *)
module TwosComplement (B : IS_BOUNDED) = struct
  module SI = Make (B) (Signedness.Signed)
  module UI = Make (B) (Signedness.Unsigned)

  module S = struct
    include SI
    let bit_width = Option.get bit_width
    let byte_width = Option.get byte_width
    let max_t = Option.get max_t
    let min_t = Option.get min_t
    let of_z_truncating = Option.get of_z_truncating
  end

  module U = struct
    include UI
    let bit_width = Option.get bit_width
    let byte_width = Option.get byte_width
    let max_t = Option.get max_t
    let min_t = Option.get min_t
    let of_z_truncating = Option.get of_z_truncating
  end

  let max_unsigned = U.(to_z max_t)
  let max_signed = S.(to_z max_t)
  module Signed = struct
    include S

    (** [as_unsigned x] reinterprets the binary representation of [x] (in two's complement) as an unsigned
        integer of the same bit-width. *)
    let as_unsigned (x : t) : U.t =
      let x = to_z x in
      U.of_z_exn Z.(if geq x zero then x else max_unsigned + x + one)
  end
  module Unsigned = struct
    include U

    (** [as_signed x] reinterprets the binary representation of [x] as a two's complement signed integer
        of the same bit-width. *)
    let as_signed (x : t) : Signed.t =
      let x = to_z x in
      Signed.of_z_exn Z.(if leq x max_signed then x else x - max_unsigned - one)

    (** [sign_extend i x] fills the bytes after [i] with the most significant bit of the [i]th bit of x. *)
    let sign_extend byte_i (x : t) : Signed.t =
      let bit_i = Stdlib.(7 + (8 * byte_i)) in
      Signed.of_z_exn (Z.signed_extract (to_z x) 0 Stdlib.(1 + bit_i))

    let to_unbounded (x : t) : Uint.t = Uint.of_z_exn (to_z x)
    let of_unbounded_exn (x : Uint.t) : t = of_z_exn (Uint.to_z x)
    let of_unbounded_truncating (x: Uint.t) : t = of_z_truncating (Uint.to_z x)

    let of_signed_int (x : int) = Signed.(as_unsigned ~$x)
  end
end

module Bits256 = TwosComplement (Size.Bits256)

(** Unsigned 256-bit integers. {!U256.t} is used to represent Ethereum 256-bit words. *)
module U256 = struct
  include Bits256.Unsigned
end

(** Signed 256-bit integers. {!I256.t} is used for signed arithmetic on Ethereum 256-bit words. *)
module I256 = Bits256.Signed

module Bits160 = TwosComplement (Size.Bits160)

(** Unsigned 160-bit integers. {!U160.t} is used to represent 160-bit Ethereum addresses. *)
module U160 = struct
  include Bits160.Unsigned
  let to_u256 (x : t) : U256.t = U256.of_z_exn (to_z x)
  let of_u256_truncating (x : U256.t) = of_z_truncating (U256.to_z x)
end
