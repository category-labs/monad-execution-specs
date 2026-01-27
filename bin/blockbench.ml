open Monad_lib
open Chain.Ethereum

let major_allocs = ref []
let minor_allocs = ref []
let promotions = ref 0

let tracker =
  let alloc_minor alloc =
    major_allocs := alloc :: !major_allocs ;
    None
  in
  let alloc_major alloc =
    minor_allocs := alloc :: !minor_allocs ;
    None
  in
  let promote _ = incr promotions ; None in
  let dealloc_minor _ = () in
  let dealloc_major _ = () in
  Gc.Memprof.{alloc_minor; alloc_major; promote; dealloc_minor; dealloc_major}

let dump_allocs name list =
  let find_mpt_call bt =
    let rec loop (raw_slot : Printexc.raw_backtrace_slot option) =
      match raw_slot with
      | None -> None
      | Some raw_slot -> (
          let slot = Printexc.convert_raw_backtrace_slot raw_slot in
          match Printexc.Slot.location slot with
          | Some loc when String.starts_with ~prefix:"lib/" loc.filename -> Some loc
          | _ -> loop (Printexc.get_raw_backtrace_next_slot raw_slot) )
    in
    loop (Some (Printexc.get_raw_backtrace_slot bt 0))
  in
  List.iter
    (fun (alloc : Gc.Memprof.allocation) ->
      let entry = find_mpt_call alloc.callstack in
      Option.iter
        (fun (entry : Printexc.location) -> Format.eprintf "%s:%d\n" entry.filename entry.line_number)
        entry )
    list

let ( $/ ) path file = Filename.concat path file
let fixtures_folder = "./test/execution/fixtures"

let valid_block_tests_folder = fixtures_folder $/ "blockchain_tests" $/ "valid_blocks"

let load_preconditions pre (state : Host.WorldState.t) =
  let open Host.WorldState in
  let accounts = Address.Map.add_seq (Address.Map.to_seq pre) state.accounts in
  {state with accounts}

let load_genesis_block (genesis_block_header : Block.Header.t) (state : Host.WorldState.t) =
  { state with
    history = [Block.{header = genesis_block_header; transactions = []; ommers = []; withdrawals = []}] }

let run_blockchain_test ((_name : string), (fixtures : Fixtures.BlockchainTest.test_case)) =
  let module Execution = Execution.Make (struct
    let chain_id = fixtures.config.chain_id
  end) in
  Host.WorldState.empty
  |> load_genesis_block fixtures.genesis_block_header
  |> load_preconditions (Address.Map.map Fixtures.AccountWithoutCodeHash.to_account fixtures.pre)
  |> fun s ->
  Result.List.fold_leftM ~f:(Execution.process_block ~verify:true) s fixtures.blocks
  |> Result.map_error Execution.Error.to_string
  |> ignore

let valid_block_tests () =
  Sys.readdir valid_block_tests_folder
  |> Array.to_seq
  |> Seq.filter (fun filename -> Filename.extension filename = ".json")
  |> Seq.map (fun filename ->
      let path = valid_block_tests_folder $/ filename in
      let fixtures =
        Result.get_ok (Fixtures.BlockchainTest.of_yojson ~skip_invalid:false (Yojson.Safe.from_file path))
      in
      List.iter run_blockchain_test fixtures )
  |> List.of_seq

let () =
  let ctl = Gc.get () in
  let ctl = Gc.{ctl with minor_heap_size = 8 * 1024 * 1024 (*; space_overhead = 200*)} in
  Gc.set ctl ;
  ignore ctl ;
  (*let profiler = Gc.Memprof.start ~sampling_rate:0.0001 tracker in*)
  let _ = valid_block_tests () in
  (*
  Gc.Memprof.stop () ;
  Gc.Memprof.discard profiler ;
  dump_allocs "Major" !major_allocs ;
  dump_allocs "Minor" !minor_allocs ;
  Format.eprintf "Promotions %d\n" !promotions

   *)
  ()
