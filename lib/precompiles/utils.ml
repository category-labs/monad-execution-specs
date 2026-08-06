open Byte_string
open Numeric
open Chain.Ethereum

type precompile = Evmc.Message.t -> Evmc.Result.t

(** A state/result monad for executing Ethereum precompiles. This includes primitives for parsing the message's
    input data, validating gas and checking precompile-specific preconditions. *)
module Precompile = struct
  module Base = Monad.Result_state (struct
    type state = Evmc.Message.t * int
    type error = Evmc.Result.StatusCode.t
  end)
  include Base

  let input_data =
    let$ msg, _ = get in
    return msg.input_data

  let advance n =
    let$ msg, i = get in
    let$ () = put (msg, i + n) in
    return i

  (* Helpers for reading input data. If the message's input length is exceeded, all of the reader operations
     in this module proceed as if the input was followed by infinitely many trailing zeros, as required in
     YP (216), YP (217), YP (246), YP (285). *)
  let byte : char t =
    let$ i = advance 1 in
    let$ bs = input_data in
    return (if i < Bytes.length bs then bs.[i] else '\x00')

  module type BYTES = sig
    type t
    val byte_width : int
    val sub_with_zero_padding : Bytes.t -> int -> t
    val reverse : t -> t
    val to_bytes : t -> Bytes.t
  end

  let byte_reader (type bs) (module B : BYTES with type t = bs) : bs t =
    let$ i = advance B.byte_width in
    let$ bs = input_data in
    return (B.sub_with_zero_padding bs i)

  let b32 : B32.t t = byte_reader (module B32)
  let b48 : B48.t t = byte_reader (module B48)

  module type NUMERIC = sig
    module Repr : BYTES
    type t
    val of_repr : Repr.t -> t
  end

  (* Read a big-endian k-byte number from calldata. YP (307) *)
  let numeric_reader (type num) (module N : NUMERIC with type t = num) : num t =
    N.of_repr <$> byte_reader (module N.Repr)

  (* Read a little-endian k-byte number from calldata. YP (308) *)
  let numeric_reader_le (type num) (module N : NUMERIC with type t = num) : num t =
    let$ repr_be = byte_reader (module N.Repr) in
    let repr_le = N.Repr.reverse repr_be in
    return (N.of_repr repr_le)

  let u256 = numeric_reader (module U256)
  let u32 = numeric_reader (module U32)

  let u64_le = numeric_reader_le (module U64)
  let uint64_le = U64.to_uint64 <$> u64_le

  let bytes (n : int) : Bytes.t t =
    let$ i = advance n in
    let$ bs = input_data in
    return (Bytes.sub_with_zero_padding bs i n)

  let pair (e1 : 'a t) (e2 : 'b t) : ('a * 'b) t =
    let$ e1 = e1 in
    let$ e2 = e2 in
    return (e1, e2)

  let list (n : int) (elt : 'a t) : 'a list t =
    let rec loop i =
      if i = 0 then return []
      else
        let$ hd = elt in
        let$ tl = loop (i - 1) in
        return (hd :: tl)
    in
    loop n

  (** Gas checks. *)
  let spend_gas (gas : Gas.t) : unit t =
    let$ msg, i = get in
    if Gas.(of_uint64 msg.gas < gas) then fail Evmc.Result.StatusCode.Out_of_gas
    else put ({msg with gas = Gas.(to_uint64 (of_uint64 msg.gas - gas))}, i)

  (** Generic precompile failure. *)
  let precompile_failure : 'a t = fail Evmc.Result.StatusCode.Precompile_failure

  let ensure (condition : bool) : unit t = if condition then return () else precompile_failure
  module Option = struct
    include Option
    let or_fail (opt : 'a option) = match opt with None -> precompile_failure | Some v -> Base.return v
  end
  module Result = struct
    include Stdlib.Result
    let or_fail (res : ('a, 'b) result) =
      match res with Error _ -> precompile_failure | Ok v -> Base.return v
  end

  (** Run a Bytes.t computation on an input message, returning an Evmc.Result.t *)
  let run (msg : Evmc.Message.t) (impl : Bytes.t t) : Evmc.Result.t =
    (* YP (209) *)
    match impl (msg, 0) with
    | Ok output, (msg', _) ->
        Evmc.Result.
          { status_code = StatusCode.Success
          ; gas_left = msg'.gas
          ; gas_refund = 0L
          ; output_data = output
          ; create_address = Address.zero }
    | Error err, _ ->
        (* Failure return path for precompiles that can fail, as per YP (269), YP (280), YP (287), YP (293) *)
        assert (err <> Evmc.Result.StatusCode.Success) ;
        Evmc.Result.failure err
end

(** Encoding and decoding for G_1/G_2 points for EC precompiles. *)
module Ec_precompile_utils (M : sig
  module F_p : sig
    include Ec.Algebra.FIELD with type t = private Integer.t
    val of_uint_opt : Uint.t -> t option
  end
  module C1_coord_repr : Precompile.BYTES
  module C_1 : Ec.Curve.SIG with type Underlying.t = F_p.t
  module G_1 : sig
    include Ec.Curve.SIG with type Underlying.t = F_p.t and type t = private C_1.t
    val in_subgroup : C_1.t -> t option
  end

  module F_p2 : sig
    type t = {re : F_p.t; im : F_p.t}
  end
  module C_2 : Ec.Curve.SIG with type Underlying.t = F_p2.t
  module G_2 : sig
    include Ec.Curve.SIG with type Underlying.t = F_p2.t and type t = private C_2.t
    val in_subgroup : C_2.t -> t option
  end

  (* Confusingly, the Yellow Paper encodes Fp_2 elements as pairs (im, re), see YP (263), YP (264), YP (265),
     but EIP-2537 specifies the encoding of c0 + c1 * v as encode(c0) || encode (c1), so both schemes are
     supported here. *)
  val complex_encoding : [`Real_first | `Imaginary_first]
end) =
struct
  open M

  (* YP (257) *)
  let f_p =
    Precompile.(
      let$ x = Uint.of_bytes_be <$> (M.C1_coord_repr.to_bytes <$> byte_reader (module M.C1_coord_repr)) in
      Option.or_fail (F_p.of_uint_opt x) )

  let point_c1 =
    Precompile.(
      (* YP (260) *)
      let$ x = f_p in
      (* YP (261) *)
      let$ y = f_p in
      (* YP (259) *)
      Option.or_fail C_1.(of_coords x y) )

  (* YP (258) *)
  let point_g1 =
    Precompile.(
      let$ p = point_c1 in
      Option.or_fail G_1.(in_subgroup p) )

  let f_p2 =
    match complex_encoding with
    | `Real_first ->
        Precompile.(
          let$ x = f_p in
          let$ y = f_p in
          return F_p2.{re = x; im = y} )
    | `Imaginary_first ->
        Precompile.(
          let$ x = f_p in
          let$ y = f_p in
          return F_p2.{im = x; re = y} )

  let point_c2 =
    Precompile.(
      (* YP (264), YP (265) *)
      let$ g_x = f_p2 in
      (* YP (266), YP (267) *)
      let$ g_y = f_p2 in
      (* YP (263) *)
      Option.or_fail (C_2.of_coords g_x g_y) )

  (* YP (262) *)
  let point_g2 =
    Precompile.(
      let$ p = point_c2 in
      Option.or_fail G_2.(in_subgroup p) )

  let c1_coord_to_repr (x : F_p.t) : Bytes.t =
    (x :> Integer.t)
    |> Integer.as_unsigned_exn
    |> Uint.to_bytes_be
    |> fun bs ->
    let padding_length = M.C1_coord_repr.byte_width - Bytes.length bs in
    assert (padding_length >= 0) ;
    Bytes.make padding_length '\x00' ^ bs

  (* Inverse of YP (258) *)
  let delta_1_inv (p : C_1.t) =
    let x, y = C_1.(coords p) in
    [x; y] |> List.map c1_coord_to_repr |> Bytes.(concat empty)

  (* Inverse of YP (262) *)
  let delta_2_inv =
    match complex_encoding with
    | `Real_first ->
        fun (p : C_2.t) ->
          let x, y = C_2.(coords p) in
          [x.re; x.im; y.re; y.im] |> List.map c1_coord_to_repr |> Bytes.(concat empty)
    | `Imaginary_first ->
        fun (p : C_2.t) ->
          let x, y = C_2.(coords p) in
          [x.im; x.re; y.im; y.re] |> List.map c1_coord_to_repr |> Bytes.(concat empty)
end
