open Monad_lib
open Monad_lib.Numeric
open Chain.Ethereum

let usage_str =
  "Usage: evmrun [--gas N] [--trace] (--bytecode_file FILE | --bytecode HEX) (--calldata_file FILE | \
   --bytecode HEX)"
let bytecode_source = ref None
let calldata_source = ref None
let gas_limit = ref 100000L
let trace = ref false

let set_source_file r = Arg.String (fun s -> r := Some (`File s))
let set_source_literal r = Arg.String (fun s -> r := Some (`Literal s))

let () =
  Arg.(
    parse
      [ ("--bytecode_file", set_source_file bytecode_source, "Bytecode file")
      ; ("--calldata_file", set_source_file calldata_source, "Calldata file")
      ; ("--bytecode", set_source_literal bytecode_source, "Bytecode")
      ; ("--calldata", set_source_literal calldata_source, "Calldata")
      ; ("--gas", String (fun s -> gas_limit := Int64.of_string s), "Gas limit (default: 100000)")
      ; ("--trace", Set trace, "Enable tracing") ]
      (fun extra_arg ->
        Format.printf "Unknown argument %s\n" extra_arg ;
        exit (-1) )
      usage_str )

let read_source place =
  match !place with
  | Some (`File file) -> In_channel.(with_open_bin file input_all)
  | Some (`Literal lit) -> Bytes.of_hex_string lit
  | None -> ""

let bytecode = read_source bytecode_source
let calldata = read_source calldata_source

module Params = struct
  let trace = !trace
end

module HostImpl = Evmc.DummyHost (Params)

module Evm = struct
  module Evm0 = Evmc.Instantiate (HostImpl.M) (HostImpl.Make) (Vm.Make (Params))

  (* Unfold one level of recursion to get access to the full signature of Vm and Host *)
  module Vm = Vm.Make (Params) (Evm0.Host)
  module Host = HostImpl.Make (Vm)
end

let msg =
  Evmc.(
    Message.
      { kind = CallKind.Call
      ; static = false
      ; delegated = false
      ; depth = 0l
      ; gas = !gas_limit
      ; recipient = Address.zero
      ; sender = Address.zero
      ; input_data = calldata
      ; value = U256.of_int 1000
      ; create2_salt = U256.zero
      ; code_address = Address.zero
      ; code = bytecode } )

let result, _state = Evm.Vm.execute msg msg.code HostImpl.State.empty

let () =
  match result.status_code with Success -> Format.printf "Ok\n" | _ -> Format.printf "Execution failure\n"
