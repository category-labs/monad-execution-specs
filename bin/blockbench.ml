open Monad_lib
open Chain.Ethereum

let ( $/ ) path file = Filename.concat path file
let fixtures_folder = "./test/execution/fixtures"

let valid_block_tests_folder = fixtures_folder $/ "blockchain_tests" $/ "valid_blocks"

let load_preconditions pre (state : Host.WorldState.t) =
  let open Host.WorldState in
  let accounts = Host.Accounts.add_seq (Host.Accounts.to_seq pre) state.accounts in
  (*let accounts = Address.Map.add_seq (Address.Map.to_seq pre) state.accounts in*)
  {state with accounts}
  (*snd (Host.WorldState.state_root {state with accounts})*)

let load_genesis_block (genesis_block_header : Block.Header.t) (state : Host.WorldState.t) =
  { state with
    history = [Block.{header = genesis_block_header; transactions = []; ommers = []; withdrawals = []}] }

module Execution = Execution.Make (struct
                       let chain_id = Numeric.Uint.one
                       end)

let run_blockchain_test ((_name : string), (fixtures : Fixtures.BlockchainTest.test_case)) =
  Host.WorldState.empty
  |> load_genesis_block fixtures.genesis_block_header
  |> load_preconditions fixtures.pre
  (*|> (fun s -> snd (Host.WorldState.state_root s))*)
  |> fun s ->
  (Result.List.fold_leftM ~f:(Execution.process_block ~verify:false) s fixtures.blocks)
|> ignore

let fixture_filename = ref ""

let valid_block_tests () =
  Sys.readdir valid_block_tests_folder
  |> Array.to_seq
  |> Seq.filter (fun filename -> Filename.extension filename = ".json")
  (*|> Seq.filter (fun filename -> filename = Sys.argv.(1))*)
  |> Seq.map (fun filename ->
      fixture_filename := filename ;
      let path = valid_block_tests_folder $/ filename in
      let fixtures =
        Result.get_ok (Fixtures.BlockchainTest.of_yojson ~skip_invalid:false (Yojson.Safe.from_file path))
      in
      List.iter run_blockchain_test fixtures )
  |> List.of_seq

module LocMap = Map.Make (struct
  type t = (string * int * int) list

  let compare = Repr.compare
end)

let () =
  let ctl = Gc.get () in
  let ctl = Gc.{ctl with minor_heap_size = 8 * 1024 * 1024 (*; space_overhead = 200*)} in
  Gc.set ctl ;
  ignore ctl ;
  let results = valid_block_tests () in
  Format.eprintf "Executed %d tests\n" (List.length results);
  ()
