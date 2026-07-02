(** Immutable fixed- and variable-width byte arrays, as opposed to the mutable [Stdlib.Bytes.t], and
    associated utilities. *)

(** Variable-length byte-strings defined as aliases to OCaml's string type. *)
module Bytes = struct
  include String

  (* Shadow the monomorphic comparison operators introduced in String. *)
  open Stdlib

  let of_char (chr : char) = make 1 chr
  let of_chars (chars : char list) = of_seq (List.to_seq chars)

  let reverse (bs : t) =
    let n = length bs in
    mapi (fun i _ -> bs.[n - i - 1]) bs

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

  (** Parse a string consisting of an even number of hex digits (\[a-f\]\[A-F\]\[0-9\]), optionally prefixed by
      '0x', into an array of bytes. If the [width] argument is provided, the resulting byte-string is left-padded
      with zeros up to the desired width. Raises an exception if the given string does not follow the correct format. *)
  let of_hex_string =
    let hex_table =
      Iarray.init 256 (fun i ->
          let open Stdlib in
          let i_c = Char.(chr i) in
          if i_c >= '0' && i_c <= '9' then i - Char.code '0'
          else if i_c >= 'a' && i_c <= 'f' then 10 + i - Char.code 'a'
          else if i_c >= 'A' && i_c <= 'F' then 10 + i - Char.code 'A'
          else -256 )
    in
    fun ?width str ->
      assert (String.length str mod 2 = 0) ;
      (* Optionally discard 0x prefix *)
      let start =
        if String.starts_with ~prefix:"0x" str || String.starts_with ~prefix:"0X" str then 2 else 0
      in
      let padding, len =
        let len = (String.length str - start) / 2 in
        match width with None -> (0, len) | Some w -> (max w len - len, max w len)
      in
      let byte_i i =
        if i < padding then '\x00'
        else
          let i = i - padding in
          let c1 = Char.code str.[start + (i * 2)] in
          let c0 = Char.code str.[start + (i * 2) + 1] in
          let num = (Iarray.get hex_table c1 * 16) + Iarray.get hex_table c0 in
          (* num is positive if and only if both c1 and c0 are valid hex digits. *)
          Char.chr num
      in
      String.init len byte_i

  let ( ~@ ) str = of_hex_string str

  type zero_and_nonzero_counts = {zero_bytes : int; nonzero_bytes : int}
  let count_zero_and_nonzero_bytes (bs : t) =
    fold_left
      (fun counts byte ->
        if byte = '\x00' then {counts with zero_bytes = counts.zero_bytes + 1}
        else {counts with nonzero_bytes = counts.nonzero_bytes + 1} )
      {zero_bytes = 0; nonzero_bytes = 0} bs

  (** [sub_with_zero_padding bytes i sz] returns the [sz]-length byte-string starting at [bytes.[i]].
      If the length of [bytes] is smaller than [i + sz - 1], it is padded with zeros. *)
  let sub_with_zero_padding bytes i sz =
    init sz (fun j -> if i + j >= length bytes || i + j < 0 then '\x00' else bytes.[i + j])

  include Comparable.Make (struct
    type nonrec t = t
    let compare (x : t) (y : t) = String.compare (x :> string) (y :> string)
  end)

  let of_yojson ?width (json : Yojson.Safe.t) : (t, string) result =
    let type_name = "Byte_string.t" in
    match json with
    | `String str -> ( try Ok (of_hex_string ?width str) with _ -> Error type_name )
    | _ -> Error type_name

  let to_yojson (x : t) : Yojson.Safe.t = `String (Format.sprintf "0x%s" (to_hex_string x))

  (* JSON conversions for byte-string-indexed maps. *)
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

module Fixed (Byte_width : sig
  val byte_width : [> `Fixed of int]
end) =
struct
  let byte_width = match Byte_width.byte_width with `Fixed n -> n
  module Impl : sig
    type t = private string

    val of_bytes : string -> t option
    val init : (int -> char) -> t
  end = struct
    type t = string
    let of_bytes (bs : Bytes.t) : t option = if Stdlib.(String.length bs = byte_width) then Some bs else None
    let init byte_i : t = String.init byte_width byte_i
  end
  include Impl

  let make char = init (fun _ -> char)
  let zeros = make '\x00'

  let of_bytes_exn (bs : Bytes.t) : t = Option.get (of_bytes bs)
  let to_bytes (bs : t) : string = (bs :> string)

  let to_seq (bs : t) = String.to_seq (bs :> string)
  let fold_left f acc (bs : t) = String.fold_left f acc (bs :> string)
  let fold_right f (bs : t) acc = String.fold_right f (bs :> string) acc

  let starts_with ~(prefix : Bytes.t) (bs : t) = String.starts_with ~prefix (bs :> string)

  let ( .$() ) (bs : t) i = (bs :> string).[i]

  let map (f : char -> char) (bs : t) = init (fun i -> f bs.$(i))
  let mapi (f : int -> char -> char) (bs : t) = init (fun i -> f i bs.$(i))
  let iter (f : char -> unit) (bs : t) = String.iter f (bs :> string)
  let iteri (f : int -> char -> unit) (bs : t) = String.iteri f (bs :> string)

  let reverse (bs : t) =
    let byte_i i = bs.$(byte_width - i - 1) in
    init byte_i

  (** [sub bytes i] returns the {!byte_width}-length byte-string starting at [bytes.[i]]. Throws
      an exception if [i] is out of bounds or [bytes] is shorter than [i + byte_width - 1]. *)
  let sub (bytes : Bytes.t) i =
    (* Significantly faster than calling init, as it uses memcpy under the hood. *)
    of_bytes_exn (Bytes.sub bytes i byte_width)

  (** [sub_with_zero_padding bytes i] returns the {!byte_width}-length byte-string starting at [bytes.[i]].
      If the length of [bytes] is smaller than [i + byte_width - 1], it is padded with zeros. *)
  let sub_with_zero_padding (bytes : Bytes.t) i =
    init (fun j -> if i + j >= Bytes.length bytes || i + j < 0 then '\x00' else bytes.[i + j])

  (** Print [bytes] as a hexadecimal string, without a '0x' prefix. *)
  let to_hex_string (bytes : t) = Bytes.to_hex_string (bytes :> string)

  (** Print [bytes] as a hexadecimal string, without a '0x' prefix. Skip initial zeros. *)
  let to_short_hex_string (bytes : t) = Bytes.to_short_hex_string (bytes :> string)

  (** Parse a string consisting of an even number of hex digits (\[a-f\]\[A-F\]\[0-9\]), optionally prefixed by
      '0x', into an array of bytes. Raises an exception if the given string does not follow the correct format,
      or the length of the resulting byte-string is different from {!byte_width}. *)
  let of_hex_string ?(zero_pad = true) str =
    let width = if zero_pad then Some byte_width else None in
    of_bytes_exn (Bytes.of_hex_string ?width str)

  let ( ~@ ) str = of_hex_string str

  include Comparable.Make (struct
    type nonrec t = t
    let compare (x : t) (y : t) = String.compare (x :> string) (y :> string)
  end)

  let of_yojson (json : Yojson.Safe.t) : (t, string) result =
    let type_name = Format.sprintf "Byte_string.B%d.t" byte_width in
    match Bytes.of_yojson ~width:byte_width json with
    | Ok bs when Int.(equal (Bytes.length bs) byte_width) -> Ok (of_bytes_exn bs)
    | _ -> Error type_name

  let to_yojson (x : t) : Yojson.Safe.t = Bytes.to_yojson (x :> string)

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
                (* In many Ethereum fixture test json files, 32-byte strings are encoded as variable-width, so
                   we need to zero-pad the keys here up to the correct width. *)
                ( of_hex_string ~zero_pad:true k
                , match elt_of_yojson v with Ok elt -> elt | Error msg -> raise (Value_decoding_error msg) ) )
            |> Map.of_seq )
        with Value_decoding_error err -> Error err )
      | _ -> Error (Format.sprintf "B%d.Map.t" byte_width)

    let to_yojson elt_to_yojson (map : 'elt t) : Yojson.Safe.t =
      to_seq map
      |> Seq.map (fun (k, v) -> (to_hex_string k, elt_to_yojson v))
      |> List.of_seq
      |> fun entries -> `Assoc entries
  end
end

module B256 = Fixed (Traits.Byte_width.Bytes256)
module B32 = Fixed (Traits.Byte_width.Bytes32)
module B20 = struct
  include Fixed (Traits.Byte_width.Bytes20)

  let of_bytes32_truncating (bs : B32.t) : t = init (fun i -> B32.(bs.$(i + 32 - 20)))

  (** Widen a 20 byte string [addr] to 32 bytes by left-padding with zeros. *)
  let to_bytes32 (addr : t) : B32.t =
    B32.init (fun i -> if Stdlib.(i < 32 - 20) then '\x00' else addr.$(i - 32 + 20))
end
module B8 = Fixed (Traits.Byte_width.Bytes8)
