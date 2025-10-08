open Monad_lib
open Chain.Ethereum

let usage_str = "Usage: evmrun [--gas N] --bytecode_file bytecode_file --calldata calldata_file"
let bytecode_source = ref None
let calldata_source = ref None
let gas_limit = ref 100000L

let set_source_file r = Arg.String (fun s -> r := Some (`File s))
let set_source_literal r = Arg.String (fun s -> r := Some (`Literal s))

let () =
  Arg.(
    parse
      [ ("--bytecode_file", set_source_file bytecode_source, "Bytecode file")
      ; ("--calldata_file", set_source_file calldata_source, "Calldata file")
      ; ("--bytecode", set_source_literal bytecode_source, "Bytecode")
      ; ("--calldata", set_source_literal calldata_source, "Calldata")
      ; ("--gas", String (fun s -> gas_limit := Int64.of_string s), "Gas limit (default: 100000)") ]
      (fun extra_arg ->
        Format.printf "Unknown argument %s\n" extra_arg ;
        exit (-1) )
      usage_str )

let to_bytes str =
  let l = String.length str in
  assert (l mod 2 == 0) ;
  String.init (l / 2) (fun i -> Char.chr (int_of_string (Printf.sprintf "0x%c%c" str.[i * 2] str.[(i * 2) + 1])))

let read_source place =
  match !place with
  | Some(`File file) -> In_channel.(with_open_bin file input_all)
  | Some(`Literal lit) -> to_bytes lit
  | None -> ""

let bytecode = read_source bytecode_source
let calldata = read_source calldata_source

module Revision = struct
  let rev = Chain.Monad.Revision.Four
end

module EvmcHost = Evmc.Dummy (Revision)

module Vm = Vm.Make (Revision) (EvmcHost)

let msg =
  Evmc.(
    Message.
      { kind = CallKind.Call
      ; flags = []
      ; depth = 0l
      ; gas = !gas_limit
      ; recipient = Address.zero
      ; sender = Address.zero
      ; input_data = calldata
      ; value = Word.of_int 1000
      ; create2_salt = Word.zero
      ; code_address = Address.zero
      ; code = bytecode } )

let result, _state = Vm.call msg EvmcHost.State.empty

let () =
  match result.status_code with Success -> Format.printf "Ok\n" | _ -> Format.printf "Execution failure\n"
