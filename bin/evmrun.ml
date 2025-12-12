open Monad_lib
open Numeric
open Byte_string
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

let trace = !trace

let sender = Address.zero

let gas_limit = Uint.of_uint64 !gas_limit

let tx =
  Transaction.Legacy
    { nonce = U256.zero
    ; gas_limit
    ; value = U256.zero
    ; r = U256.zero
    ; s = U256.zero
    ; to_ = Address.zero
    ; data = Bytes.empty
    ; gas_price = Uint.zero
    ; v = U256.zero }

let block = Block.{header = Header.empty; transactions = [tx]; ommers = []; withdrawals = []}

let result, _state =
  (*Evm.Vm.execute msg msg.code Evmc.DummyHost.State.empty*)
  let world_state = State.WorldState.make Uint.zero in
  let block_state = State.BlockState.make world_state block in
  let transaction_state = State.TransactionState.make block_state tx in
  let msg =
    {(Execution.prepare_message block_state sender gas_limit tx) with code = bytecode; input_data = calldata}
  in
  Execution.process_message ~trace msg transaction_state

let () =
  match result.status_code with Success -> Format.printf "Ok\n" | _ -> Format.printf "Execution failure\n"
