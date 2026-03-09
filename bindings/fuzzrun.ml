open Monad_lib
open Numeric
open Byte_string
open Chain.Ethereum

let ledger_path = Sys.argv.(1)

let ( let$ ) x rest = x rest
let parse name parser input continuation =
  match try Some (parser input) with _ -> None with
  | Some value -> continuation value
  | None -> Format.printf "Could not parse %s as %s\n" input name

let parse_address = parse "address" Address.of_hex_string
let parse_u256 = parse "256-bit unsigned" U256.of_string
let parse_int = parse "integer" int_of_string

let () =
  let open Fuzz_client in
  let client = make ~chain_id:Chain.Monad.Mainnet.chain_id ~ledger_path in
  while true do
    Format.printf "> " ;
    Format.print_flush () ;
    let input = read_line () in
    match String.split_on_char ' ' input with
    | ["exit"] -> exit 0
    | ["set_balance"; addr; balance] ->
        let$ addr = parse_address addr in
        let$ balance = parse_u256 balance in
        set_balance client addr balance
    | ["get_balance"; addr] ->
        let$ addr = parse_address addr in
        let balance = get_balance client addr in
        Format.printf "%s\n" (U256.to_string balance)
    | ["get_state_root"] ->
        let state_root = get_state_root client in
        Format.printf "%s\n" (B32.to_hex_string state_root)
    | ["run"; n] ->
        let$ n = parse_int n in
        run client n
    | _ ->
        Format.printf "Unrecognized command: %s\n" input ;
        Format.printf "Available commands are:\n" ;
        Format.printf "\tset_balance <addr> <balance>\n" ;
        Format.printf "\tget_balance <addr>\n" ;
        Format.printf "\tget_state_root <addr> <balance>\n" ;
        Format.printf "\trun <n_blocks>\n" ;
        Format.printf "\texit\n"
  done
