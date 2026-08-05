(** Solidity-specific conventions: events, selectors, function signatures. *)

open Byte_string
open Chain.Ethereum
open Type

(** Convert a tuple of types into a list of their canonical type names. This is used to get cryptographic
      signatures of function prototypes and events. *)
let rec tuple_to_canonical_type_names : type a. a tup -> string list = function
  | [] -> []
  | ty :: tys -> type_name ty :: tuple_to_canonical_type_names tys

module Event = struct
  type ('i, 'ni) t =
    {name : string; anonymous : bool; indexed_parameter_types : 'i tup; non_indexed_parameter_types : 'ni tup}

  (* TODO: if this ever becomes a bottleneck, it can be cached inside the event record. *)
  let encode_header (ev : ('i, 'ni) t) =
    let params =
      String.concat ","
        ( tuple_to_canonical_type_names ev.indexed_parameter_types
        @ tuple_to_canonical_type_names ev.non_indexed_parameter_types )
    in
    Crypto.keccak_256 (Format.sprintf "%s(%s)" ev.name params)

  let rec encode_indexed_parameters : type i. i tup -> i -> B32.t list =
   fun tys vals ->
    match (tys, vals) with
    | t :: tys, v :: vals ->
        let v_enc = enc t v in
        (* Non-word-sized types in indexed topics are encoded via a different scheme. For now it is not
               necessary to implement this. *)
        assert (List.length v_enc = 1) ;
        List.hd v_enc :: encode_indexed_parameters tys vals
    | [], [] -> []

  let to_log (ev : ('i, 'ni) t) (address : Address.t) (indexed_parameters : 'i) (non_indexed_parameters : 'ni)
      : Log.t =
    let indexed_topics = encode_indexed_parameters ev.indexed_parameter_types indexed_parameters in
    let topics = if ev.anonymous then indexed_topics else encode_header ev :: indexed_topics in
    let data =
      enc_tup ev.non_indexed_parameter_types non_indexed_parameters
      |> List.map B32.to_bytes
      |> Bytes.(concat empty)
    in
    {address; topics; data}
end

module Selector = B4

module Signature = struct
  module Impl : sig
    type ('i, 'o) t = private
      {name : string; input : 'i tup; output : 'o typ; as_string : string; selector : Selector.t}
    val make : string -> input:'i tup -> output:'o typ -> ('i, 'o) t
  end = struct
    type ('i, 'o) t =
      {name : string; input : 'i tup; output : 'o typ; as_string : string; selector : Selector.t}

    let make name ~(input : 'i tup) ~(output : 'o typ) : ('i, 'o) t =
      let parameter_type_names = tuple_to_canonical_type_names input in
      let as_string = Format.sprintf "%s(%s)" name (String.concat "," parameter_type_names) in
      let selector = B4.sub (B32.to_bytes (Crypto.keccak_256 as_string)) 0 in
      {name; input; output; as_string; selector}
  end
  include Impl

  let input_to_message
      ?(static = false)
      ?(delegated = false)
      ?(depth = 0l)
      ?(value = U256.zero)
      ?(kind = Evmc.Message.CallKind.Call)
      ?(create2_salt = B32.zeros)
      ?(code_address = Address.zero)
      ?(code = Bytes.empty)
      ?(prepend_selector = true)
      ~(gas : Uint64.t)
      ~(sender : Address.t)
      ~(recipient : Address.t)
      ~(memory_capacity : Int32.t)
      (s : ('i, 'o) t)
      (input : 'i) : Evmc.Message.t =
    let selector = if prepend_selector then Selector.to_bytes s.selector else Bytes.empty in
    let input = enc (Tuple s.input) input in
    let input_data = Bytes.(concat empty (selector :: List.map B32.to_bytes input)) in
    Evmc.Message.
      { kind
      ; sender
      ; recipient
      ; input_data
      ; static
      ; delegated
      ; depth
      ; value
      ; gas
      ; create2_salt
      ; code_address
      ; code
      ; memory_capacity }

  let result_to_output (s : ('i, 'o) t) (result : Evmc.Result.t) :
      (('o, Type.decode_error) result, Evmc.Result.StatusCode.t) result =
    if Evmc.Result.StatusCode.(result.status_code = Success) then Ok (dec_bytes s.output result.output_data)
    else Error result.status_code
end
