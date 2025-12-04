(** Immutable fixed-width and unbounded byte arrays, as opposed to the mutable [Stdlib.Bytes.t], and
    associated utilities. *)

module type STRING_LIKE = sig
  type t = private string
  val byte_width : int option
  val of_byte_string_opt : string -> t option
  val type_name : string
end

module Impl (Byte_width : Traits.Byte_width.SIG) : sig
  type t = Byte_width.repr
  val byte_width : int option
end = struct
  type t = string

  let byte_width = Byte_width.byte_width

  let () = match byte_width with None -> () | Some w -> assert (w > 0)

  let of_byte_string_opt =
    match byte_width with
    | None -> fun (bs : string) -> Some (bs :> t)
    | Some n -> fun (bs : string) -> if String.length bs <> n then None else Some (bs :> t)

  let type_name =
    match byte_width with None -> "Bytes.t" | Some byte_width -> Format.sprintf "Bytes.B%d.t" byte_width
end

module Make (Base : STRING_LIKE) = struct
  include Base

  let of_byte_string_exn s = Option.get (of_byte_string_opt s)

  let length (bs : t) = String.length (bs :> string)
  let to_seq (bs : t) = String.to_seq (bs :> string)
  let fold_left f acc (bs : t) = String.fold_left f acc (bs :> string)
  let fold_right f (bs : t) acc = String.fold_right f (bs :> string) acc

  let starts_with ~(prefix : Variable.t) (bs : t) =
    String.starts_with ~prefix:(prefix :> string) (bs :> string)

  let ( .$() ) (bs : t) i = (bs :> string).[i]

  let reverse (bs : t) =
    let n = length bs in
    of_byte_string_exn (String.init n (fun i -> bs.$(n - i - 1)))

  (** Print [bytes] as a hexadecimal string, without a '0x' prefix. *)
  let to_hex_string (bytes : t) =
    to_seq bytes |> Seq.map Char.code |> Seq.map (Format.sprintf "%02x") |> List.of_seq |> String.concat ""

  (** Print [bytes] as a hexadecimal string, without a '0x' prefix. Skip initial zeros. *)
  let to_short_hex_string (bytes : t) =
    to_seq bytes
    |> Seq.drop_while Char.(equal '\x00')
    |> Seq.map Char.code
    |> Seq.map (Format.sprintf "%02x")
    |> List.of_seq
    |> String.concat ""

  (** As {!String.init}, except throwing an exception if this functor is instantiated to a fixed byte width that
      does not match the length argument. *)
  let init len byte_i = of_byte_string_exn (String.init len byte_i)

  (** As {!String.make}, except throwing an exception if this functor is instantiated to a fixed byte width that
      does not match the length argument. *)
  let make len byte_i = of_byte_string_exn (String.make len byte_i)

  (** Parse a string consisting of an even number of hex digits (\[a-f\]\[A-F\]\[0-9\]), optionally prefixed by
      '0x', into an array of bytes. If [byte_width] is set, the string must match it exactly. *)
  let of_hex_string str =
    assert (String.length str mod 2 = 0) ;
    (* Optionally discard 0x prefix *)
    let start = if String.starts_with ~prefix:"0x" str || String.starts_with ~prefix:"0X" str then 2 else 0 in
    let len = (String.length str - start) / 2 in
    let byte_i i =
      let c1 = str.[start + (i * 2)] in
      let c0 = str.[start + (i * 2) + 1] in
      (* TODO: this is very inefficient. It can be replaced with a lookup table. *)
      Char.chr (int_of_string (Printf.sprintf "0x%c%c" c1 c0))
    in
    init len byte_i

  (*
  (** [sub_with_zero_padding bytes i sz] returns a [sz]-length byte array formed by zero-padding
      the array [bytes[i, min(len(bytes), i+sz))]] to [length sz]. *)
  let sub_with_zero_padding (bs : Variable.t) (pos : int) (len : Byte_width.length_type_for_init) : t =
   fun bs pos len ->
    let str = (bs :> string) in
    let byte_i j = if pos + j >= String.length str then '\x00' else str.[pos + j] in
    init len byte_i
   *)

  let to_byte_string (bs : t) : Variable.t = (bs :> Variable.t)

  type zero_and_nonzero_counts = {zero_bytes : int; nonzero_bytes : int}
  let count_zero_and_nonzero_bytes (bs : t) =
    fold_left
      (fun counts byte ->
        if byte = '\x00' then {counts with zero_bytes = counts.zero_bytes + 1}
        else {counts with nonzero_bytes = counts.nonzero_bytes + 1} )
      {zero_bytes = 0; nonzero_bytes = 0} bs

  include Comparable.Make (struct
    type nonrec t = t
    let compare (x : t) (y : t) = String.compare (x :> string) (y :> string)
  end)

  let of_yojson =
    let type_name = Base.type_name in
    fun (json : Yojson.Safe.t) : (t, string) result ->
      match json with
      | `String str -> ( try Ok (of_hex_string str) with _ -> Error type_name )
      | _ -> Error type_name

  let to_yojson (x : t) : Yojson.Safe.t = `String (Format.sprintf "0x%s" (to_hex_string x))

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
                ( of_hex_string k
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
end

include Make (Impl(Traits.Byte_width.Unbounded))

(* Extra operations for unbounded byte arrays. *)
let of_byte_string str = Option.get (of_byte_string_opt str)
let ( ~@ ) str = of_byte_string str

let of_char c = make 1 c

let ( ^ ) (x : t) (y : t) = of_byte_string ((x :> string) ^ (y :> string))

let concat (sep : t) (bs : t list) : t = of_byte_string (String.concat (sep :> string) (bs :> string list))

let empty : t = make 0 '\x00'

let sub (bytes : t) start len = of_byte_string (String.sub (bytes :> string) start len)

let of_seq seq = of_byte_string (String.of_seq seq)

module Make_fixed (Byte_width : sig
  val byte_width : int
end) =
struct
  module Base = Fixed (Byte_width)
  include Base
  include Byte_width

  let init byte_i = init byte_width byte_i
  let make byte = make byte_width byte

  let zero = make '\x00'
end

module B32 = Make_fixed (struct
  let byte_width = 32
end)
module B20 = Make_fixed (struct
  let byte_width = 20
end)

(*
include String

type bytes = t

(** [sub_with_zero_padding bytes i sz] returns a [sz]-length byte array formed by zero-padding
      the array [bytes[i, min(len(bytes), i+sz))]] to [length sz]. *)
let sub_with_zero_padding bytes i sz =
  init sz (fun j -> if i + j >= length bytes then '\x00' else bytes.[i + j])

(** Print [bytes] as a hexadecimal string, without a '0x' prefix. *)
let to_hex_string bytes =
  to_seq bytes |> Seq.map Char.code |> Seq.map (Format.sprintf "%02x") |> List.of_seq |> String.concat ""

(** Parse a string consisting of an even number of hex digits (\[a-f\]\[A-F\]\[0-9\]), optionally prefixed by
      '0x', into an array of bytes. *)
let of_hex_string str =
  assert (String.length str mod 2 = 0) ;
  let str = String.lowercase_ascii str in
  (* Optionally discard 0x prefix *)
  let str = if String.starts_with ~prefix:"0x" str then String.sub str 2 (String.length str - 2) else str in
  init
    (String.length str / 2)
    (fun i -> Char.chr (int_of_string (Printf.sprintf "0x%c%c" str.[i * 2] str.[(i * 2) + 1])))

let of_chars chrs = of_seq (List.to_seq chrs)

module Map = Map.Make (String)

let of_yojson (json : Yojson.Safe.t) : (t, string) result =
  match json with
  | `String str -> (
    try Ok (of_hex_string str) with _ -> Error (Format.sprintf "Cannot parse \"%s\" as a byte string" str) )
  | _ -> Error "Expected string"
let of_yojson_exn (json : Yojson.Safe.t) : t = Result.get_ok (of_yojson json)
let to_yojson (bs : t) : Yojson.Safe.t = `String (Format.sprintf "0x%s" (to_hex_string bs))

 *)
