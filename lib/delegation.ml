(** Utilities for handling EOA delegation as per EIP-7702. *)

module Authorization = Chain.Ethereum.Transaction.Authorization
module Address = Chain.Ethereum.Address
open Numeric
open Byte_string

let set_code_tx_magic = "\x05"
let eoa_delegation_prefix : Bytes.t = "\xef\x01\x00"
let eoa_delegated_code_length = Bytes.length eoa_delegation_prefix + Address.byte_width
let () = assert (eoa_delegated_code_length = 23)

let per_empty_account_cost = Uint.(~$25_000)
let per_auth_base_cost = Uint.(~$12_500)

(** Checks whether the given bytecode starts with the delegation indicator (0xef0100) and is exactly 23 bytes
    (corresponding to the delegation indicator plus a 20-byte address) *)
let is_valid_delegation (code : Bytes.t) : bool =
  Bytes.length code = eoa_delegated_code_length && Bytes.starts_with ~prefix:eoa_delegation_prefix code

let delegation_code (address : Address.t) : Bytes.t =
  Format.sprintf "%s%s" eoa_delegation_prefix (Address.to_bytes address)

(** If the bytecode starts with a delegation indicator (0xef0100), [get_delegated_address] returns the address
    where the delegated code is hosted, otherwise it returns [None]. *)
let get_delegated_address (code : Bytes.t) : Address.t option =
  if is_valid_delegation code then
    Some (Address.of_bytes_exn (Bytes.sub code (Bytes.length eoa_delegation_prefix) Address.byte_width))
  else None
