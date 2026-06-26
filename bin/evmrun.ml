open Monad_lib
open Numeric
open Byte_string
open Chain.Ethereum
open Chain.Monad

let usage_str =
  "Usage: evmrun <options> (--bytecode_file FILE | --bytecode HEX) (--calldata_file FILE | --calldata HEX)"
let revision : Revision.active ref = ref `Eight
let chain_id : Uint.t ref = ref Testnet.chain_id
let bytecode_source = ref None
let calldata_source = ref None
let gas_limit = ref 100_000L
let trace = ref false
let gc_stats = ref false

let set_source_file r = Arg.String (fun s -> r := Some (`File s))
let set_source_literal r = Arg.String (fun s -> r := Some (`Literal s))

let set_revision =
  Arg.String
    (fun s ->
      revision :=
        let rev =
          match Revision.of_string s with
          | Some rev -> rev
          | None -> raise (Arg.Bad (Format.sprintf "Invalid revision %s" s))
        in
        let rev =
          match Revision.is_active rev with
          | Some rev -> rev
          | None ->
              raise
                (Arg.Bad
                   (Format.sprintf "Revision %s is unsupported in this version" (Revision.to_string rev)) )
        in
        rev )

let set_chain_id = Arg.String (fun s -> chain_id := Uint.of_string s)
let () =
  Arg.(
    parse
      [ ( "--revision"
        , set_revision
        , Format.sprintf "Revision to use (default: %s)" Revision.(to_string (!revision :> t)) )
      ; ("--chain_id", set_chain_id, Format.sprintf "Chain ID to use (default: %s)" (Uint.to_string !chain_id))
      ; ("--bytecode_file", set_source_file bytecode_source, "Bytecode file")
      ; ("--calldata_file", set_source_file calldata_source, "Calldata file")
      ; ("--bytecode", set_source_literal bytecode_source, "Bytecode")
      ; ("--calldata", set_source_literal calldata_source, "Calldata")
      ; ("--gc_stats", Set gc_stats, "Report GC statistics after execution")
      ; ( "--gas"
        , String (fun s -> gas_limit := Int64.of_string s)
        , Format.sprintf "Gas limit (default: %Ld)" !gas_limit )
      ; ("--trace", Set trace, "Enable tracing") ]
      (fun extra_arg ->
        Format.printf "Unknown argument %s\n" extra_arg ;
        exit (-1) )
      usage_str )

let read_source place =
  match !place with
  | Some (`File file) ->
      In_channel.(with_open_bin file (fun f -> Bytes.of_hex_string (String.trim (input_all f))))
  | Some (`Literal lit) -> Bytes.of_hex_string lit
  | None -> ""

let bytecode = read_source bytecode_source
let calldata = read_source calldata_source

let sender = Address.zero

let gas_limit = Uint.of_uint64 !gas_limit

let tx =
  Transaction.Legacy
    { nonce = U64.zero
    ; gas_limit
    ; value = U256.zero
    ; r = U256.zero
    ; s = U256.zero
    ; to_ = Some Address.zero
    ; data = Bytes.empty
    ; gas_price = Uint.zero
    ; v = U256.zero }

let block = Block.{header = Header.empty; transactions = [tx]; ommers = []; withdrawals = []}

module Params = struct
  let chain_id = !chain_id
  let revision = !revision
  let trace = !trace
end
module Execution = Execution.Make (Params)

let () =
  let result, _state =
    let world_state = Host.WorldState.empty in
    let block_state = Host.BlockState.make world_state block in
    let transaction_state = Host.TransactionState.make block_state Address.zero tx in
    let msg = {(Execution.prepare_message sender gas_limit tx) with code = bytecode; input_data = calldata} in
    Execution.Vm.execute msg bytecode transaction_state
  in
  if !gc_stats then Gc.print_stat Out_channel.stdout ;

  match result.status_code with Success -> Format.printf "Ok\n" | _ -> Format.printf "Execution failure\n"
