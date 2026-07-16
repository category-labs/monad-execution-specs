open Monad_lib
open Byte_string
open Chain.Ethereum

let kvm_prefix = Bytes.of_hex_string "ae0001"

let kvm = External_vm.load "librv64_vm.so"
module Kvm = External_vm.Make (struct
  let vm = kvm
end)

let zstd_decomp = Rvcode.Zstd_decomp.make ()
let code_cache = Rvcode.Code_cache.make ~log2_size:'\x0a'

module Override (Base : Evmc.VM) : Evmc.VM = struct
  let get_execution_token (addr : Address.t) (code : Bytes.t) =
    match Rvcode.Code_cache.lookup code_cache addr with
    | Some token -> Some token
    | None -> (
      match Rvcode.Code_cache.insert_valid code_cache zstd_decomp addr code with
      | Ok token -> Some token
      | Error err ->
          (* This should never happen. If the ELF blob was in storage, then it must be valid. *)
          Format.eprintf "Error loading ELF blob into cache: %s\n" (Rvcode.Validate_result.to_string err) ;
          None )

  let call
      (type t) (host : (module Evmc.HOST with type t = t)) (msg : Evmc.Message.t) (code : Bytes.t) (state : t)
      =
    match get_execution_token msg.code_address code with
    | Some token ->
        Format.eprintf "Invoking KVM call\n" ;
        let result, state = Kvm.execute host msg (B16.to_bytes token) state in
        Format.eprintf "KVM create result: %s\n" (Yojson.Safe.pretty_to_string (Evmc.Result.to_yojson result)) ;
        (result, state)
    | None -> (Evmc.Result.(failure StatusCode.Internal_error), state)

  let create
      (type t) (host : (module Evmc.HOST with type t = t)) (msg : Evmc.Message.t) (code : Bytes.t) (state : t)
      =
    (* KVM uses a different format for initialization messages, passing the entire init blob (prefix + code
       + initialization data). *)
    match Rvcode.Code_cache.try_insert_new code_cache zstd_decomp msg.recipient code with
    | Error err ->
        Format.eprintf "Error validating ELF blob: %s\n" (Rvcode.Validate_result.to_string err) ;
        (Evmc.Result.(failure Contract_validation_failure), state)
    | Ok (code_sections, token) ->
        let init_contract_msg =
          {msg with kind = Call; elf_init = true; input_data = code_sections.init_blob}
        in
        Format.eprintf "Invoking KVM create\n" ;
        let result, state = Kvm.execute host init_contract_msg (B16.to_bytes token) state in
        Format.eprintf "KVM create result: %s\n" (Yojson.Safe.pretty_to_string (Evmc.Result.to_yojson result)) ;
        (* Return the db blob in the format that's expected by EVM creation calls. Note that kvm returns
           gas_left = -1 *)
        let result = {result with output_data = code_sections.db_blob; gas_left = msg.gas} in
        (result, state)

  let execute (type t) (host : (module Evmc.HOST with type t = t)) (msg : Evmc.Message.t) (code : Bytes.t) =
    if not (Bytes.starts_with ~prefix:kvm_prefix code) then Base.execute host msg code
    else
      match msg.kind with
      | Call | DelegateCall | CallCode -> call host msg code
      | Create | Create2 -> create host msg code
end
