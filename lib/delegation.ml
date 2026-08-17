(** Utilities for handling EOA delegation as per EIP-7702. *)

open Numeric
open Byte_string
module Address = B20

let eoa_delegation_prefix : Bytes.t = "\xef\x01\x00"
let eoa_delegated_code_length = Bytes.length eoa_delegation_prefix + Address.byte_width
let () = assert (eoa_delegated_code_length = 23)

let magic = "\x05"
let per_empty_account_cost = Uint.(~$25_000)
let per_auth_base_cost = Uint.(~$12_500)

(** [is_valid_delegation code] checks whether [code] starts with the delegation indicator ([0xef0100]) and is
    exactly 23 bytes (corresponding to the delegation indicator plus a 20-byte address) *)
let is_valid_delegation (code : Bytes.t) : bool =
  Bytes.length code = eoa_delegated_code_length && Bytes.starts_with ~prefix:eoa_delegation_prefix code

(** [delegation_code addr] returns the delegation code for [addr] (the address prefixed by the delegation
    indicator), or the empty byte string if the address is zero. *)
let delegation_code (address : Address.t) : Bytes.t =
  if Address.(address = zeros) then Bytes.empty
  else Format.sprintf "%s%s" eoa_delegation_prefix (Address.to_bytes address)

(** If [code] is a valid delegation, [get_delegated_address code] returns the address where the delegated code
    is hosted, otherwise it returns [None]. *)
let get_delegated_address (code : Bytes.t) : Address.t option =
  if is_valid_delegation code then
    Some (Address.of_bytes_exn (Bytes.sub code (Bytes.length eoa_delegation_prefix) Address.byte_width))
  else None
