module Address = Chain.Ethereum.Address
open Utils
open Numeric

let set_code_tx_magic : Bytes.t = "\x05"
let eoa_delegation_prefix : Bytes.t = "\xef\x01\x00"
let eoa_delegated_code_length = Bytes.length eoa_delegation_prefix + Address.byte_width
let () = assert (eoa_delegated_code_length = 23)

let per_empty_account_cost = Uint.(~$25_000)
let per_auth_base_cost = Uint.(~$12_500)

let get_delegated_address (code : Bytes.t) : Address.t option =
  if Bytes.length code = eoa_delegated_code_length && Bytes.starts_with ~prefix:eoa_delegation_prefix code
  then Some (Address.of_bytes_be (Bytes.sub code (Bytes.length eoa_delegation_prefix) Address.byte_width))
  else None

