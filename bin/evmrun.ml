open Monad_lib
open Numeric
open Byte_string
open Chain.Ethereum
open Chain.Monad

let usage_str =
  "Usage: evmrun [--gas N] [--trace] [--chain_id ID] [--revision REV] (--bytecode_file FILE | --bytecode \
   HEX) (--calldata_file FILE | --calldata HEX)"
let revision : Revision.active ref = ref `Eight
let chain_id : Uint.t ref = ref Testnet.chain_id
let bytecode_source = ref None
let calldata_source = ref None
let gas_limit = ref Uint64.max_uint
let trace = ref false
let minprof = ref false
let majprof = ref false
let promprof = ref false
let alloc_frames = ref 1

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
      ; ("--minprof", Set minprof, "Report minor-heap allocation cost centres")
      ; ("--majprof", Set majprof, "Report major-heap allocation cost centres")
      ; ("--promprof", Set promprof, "Report minor->major promotion cost centres")
      ; ("--gas", String (fun s -> gas_limit := Int64.of_string s), "Gas limit (default: 100000)")
      ; ("--trace", Set trace, "Enable tracing")
      ; ( "--alloc-frames"
        , Int (fun n -> alloc_frames := n)
        , "Group allocations by the top N call frames (default: 1)" ) ]
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

let minor = ref []
let major = ref []
let promoted = ref []

let alloc_tracker =
  Gc.Memprof.
    { null_tracker with
      alloc_minor =
        (fun alloc ->
          minor := alloc :: !minor ;
          (* Track the block so [promote] fires if it survives a minor collection. *)
          Some alloc )
    ; alloc_major =
        (fun alloc ->
          major := alloc :: !major ;
          None )
    ; promote =
        (fun alloc ->
          promoted := alloc :: !promoted ;
          None ) }

let summarize_allocs ~depth () =
  let minor = !minor in
  let major = !major in
  let promoted = !promoted in
  (* Must match the rate given to [Gc.Memprof.start] below: each sample stands
     for roughly [1. /. sampling_rate] words allocated. *)
  let sampling_rate = 0.0004 in
  let words_per_sample = 1. /. sampling_rate in
  let bytes_of_samples s = float_of_int s *. words_per_sample *. float_of_int (Sys.word_size / 8) in
  (* Render one backtrace frame as "name (file:line)". *)
  let frame_str slot =
    let name = match Printexc.Slot.name slot with Some n -> n | None -> "??" in
    match Printexc.Slot.location slot with
    | Some loc -> Printf.sprintf "%s (%s:%d)" name loc.Printexc.filename loc.Printexc.line_number
    | None -> name
  in
  (* Group samples by their innermost [depth] frames: two samples share a bucket
     iff their top [depth] call frames agree. [depth = 1] groups by allocation
     site alone; larger [depth] separates a site by the call path that reached
     it. Frames are listed innermost-first; read " <- " as "called by". *)
  let site_of (a : Gc.Memprof.allocation) =
    match Printexc.backtrace_slots a.Gc.Memprof.callstack with
    | Some slots when Array.length slots > 0 ->
        let n = min depth (Array.length slots) in
        String.concat " <- " (List.init n (fun i -> frame_str slots.(i)))
    | _ -> "<no backtrace>"
  in
  (* Per site: (total samples, #sampled blocks, total words across those blocks,
     largest block, smallest block). [a.size] is the block's word count, excluding the header. *)
  if !minprof then begin
    let table : (string, int ref * int ref * int ref * int ref * int ref) Hashtbl.t = Hashtbl.create 256 in
    let add (a : Gc.Memprof.allocation) =
      let site = site_of a in
      let samples, blocks, words, max_words, min_words =
        match Hashtbl.find_opt table site with
        | Some v -> v
        | None ->
            let v = (ref 0, ref 0, ref 0, ref 0, ref max_int) in
            Hashtbl.add table site v ; v
      in
      samples := !samples + a.Gc.Memprof.n_samples ;
      incr blocks ;
      words := !words + a.Gc.Memprof.size ;
      max_words := max !max_words a.Gc.Memprof.size ;
      min_words := min !min_words a.Gc.Memprof.size
    in
    List.iter add minor ;
    let rows =
      Hashtbl.fold (fun site (s, b, w, mx, mn) acc -> (site, !s, !b, !w, !mx, !mn) :: acc) table []
      |> List.sort (fun (_, s1, _, _, _, _) (_, s2, _, _, _, _) -> Int.compare s2 s1)
    in
    let total_samples = List.fold_left (fun acc (_, s, _, _, _, _) -> acc + s) 0 rows in
    Printf.printf "\n=== minor-heap allocation cost centres (statmemprof, rate %.4g) ===\n" sampling_rate ;
    Printf.printf "sampled minor blocks: %d | samples: %d | est. total: %.1f MB\n\n" (List.length minor)
      total_samples (bytes_of_samples total_samples /. 1.0e6) ;
    Printf.printf "  %14s %7s %9s %7s %8s %7s   %s\n" "est. bytes" "%" "#blocks" "min w" "avg w" "max w" "site" ;
    List.iteri
      (fun i (site, s, b, w, mx, mn) ->
        if i < 25 then begin
          let pct = 100. *. float_of_int s /. float_of_int (max 1 total_samples) in
          let avg_words = if b = 0 then 0. else float_of_int w /. float_of_int b in
          Printf.printf "  %14.0f %6.1f%% %9d %7d %8.1f %7d   %s\n" (bytes_of_samples s) pct b mn avg_words mx
            site
        end )
      rows
  end ;
  (* Extra summary restricted to blocks allocated directly in the major heap
     (e.g. objects larger than the minor-heap allocation threshold). *)
  if !majprof then begin
    let major_table : (string, int ref * int ref * int ref * int ref * int ref) Hashtbl.t =
      Hashtbl.create 256
    in
    let add_major (a : Gc.Memprof.allocation) =
      let site = site_of a in
      let samples, blocks, words, max_words, min_words =
        match Hashtbl.find_opt major_table site with
        | Some v -> v
        | None ->
            let v = (ref 0, ref 0, ref 0, ref 0, ref max_int) in
            Hashtbl.add major_table site v ; v
      in
      samples := !samples + a.Gc.Memprof.n_samples ;
      incr blocks ;
      words := !words + a.Gc.Memprof.size ;
      max_words := max !max_words a.Gc.Memprof.size ;
      min_words := min !min_words a.Gc.Memprof.size
    in
    List.iter add_major major ;
    let major_rows =
      Hashtbl.fold (fun site (s, b, w, mx, mn) acc -> (site, !s, !b, !w, !mx, !mn) :: acc) major_table []
      |> List.sort (fun (_, s1, _, _, _, _) (_, s2, _, _, _, _) -> Int.compare s2 s1)
    in
    let major_total = List.fold_left (fun acc (_, s, _, _, _, _) -> acc + s) 0 major_rows in
    Printf.printf "\n=== major-heap allocation cost centres (statmemprof, rate %.4g) ===\n" sampling_rate ;
    Printf.printf "sampled major blocks: %d | samples: %d | est. total: %.1f MB\n\n" (List.length major)
      major_total (bytes_of_samples major_total /. 1.0e6) ;
    Printf.printf "  %14s %7s %9s %7s %8s %7s   %s\n" "est. bytes" "%" "#blocks" "min w" "avg w" "max w" "site" ;
    List.iteri
      (fun i (site, s, b, w, mx, mn) ->
        if i < 25 then begin
          let pct = 100. *. float_of_int s /. float_of_int (max 1 major_total) in
          let avg_words = if b = 0 then 0. else float_of_int w /. float_of_int b in
          Printf.printf "  %14.0f %6.1f%% %9d %7d %8.1f %7d   %s\n" (bytes_of_samples s) pct b mn avg_words mx
            site
        end )
      major_rows
  end ;
  (* Third summary: blocks promoted from the minor to the major heap. Sites are
     the original (minor) allocation sites of objects that survived a collection. *)
  if !promprof then begin
    let promoted_table : (string, int ref * int ref * int ref * int ref * int ref) Hashtbl.t =
      Hashtbl.create 256
    in
    let add_promoted (a : Gc.Memprof.allocation) =
      let site = site_of a in
      let samples, blocks, words, max_words, min_words =
        match Hashtbl.find_opt promoted_table site with
        | Some v -> v
        | None ->
            let v = (ref 0, ref 0, ref 0, ref 0, ref max_int) in
            Hashtbl.add promoted_table site v ; v
      in
      samples := !samples + a.Gc.Memprof.n_samples ;
      incr blocks ;
      words := !words + a.Gc.Memprof.size ;
      max_words := max !max_words a.Gc.Memprof.size ;
      min_words := min !min_words a.Gc.Memprof.size
    in
    List.iter add_promoted promoted ;
    let promoted_rows =
      Hashtbl.fold (fun site (s, b, w, mx, mn) acc -> (site, !s, !b, !w, !mx, !mn) :: acc) promoted_table []
      |> List.sort (fun (_, s1, _, _, _, _) (_, s2, _, _, _, _) -> Int.compare s2 s1)
    in
    let promoted_total = List.fold_left (fun acc (_, s, _, _, _, _) -> acc + s) 0 promoted_rows in
    Printf.printf "\n=== promoted (minor -> major) allocation cost centres (statmemprof, rate %.4g) ===\n"
      sampling_rate ;
    Printf.printf "sampled promoted blocks: %d | samples: %d | est. total: %.1f MB\n\n" (List.length promoted)
      promoted_total (bytes_of_samples promoted_total /. 1.0e6) ;
    Printf.printf "  %14s %7s %9s %7s %8s %7s   %s\n" "est. bytes" "%" "#blocks" "min w" "avg w" "max w" "site" ;
    List.iteri
      (fun i (site, s, b, w, mx, mn) ->
        if i < 25 then begin
          let pct = 100. *. float_of_int s /. float_of_int (max 1 promoted_total) in
          let avg_words = if b = 0 then 0. else float_of_int w /. float_of_int b in
          Printf.printf "  %14.0f %6.1f%% %9d %7d %8.1f %7d   %s\n" (bytes_of_samples s) pct b mn avg_words mx
            site
        end )
      promoted_rows
  end

(* Per-opcode execution counts and wall-clock times accumulated by the VM
   (Monad_lib.Vm.instr_count / instr_time_ns), sorted by total time. *)
let summarize_instructions () =
  let rows =
    List.init 256 (fun i -> (i, Vm.instr_count.(i), Vm.instr_time_ns.(i)))
    |> List.filter (fun (_, count, _) -> count > 0)
    |> List.sort (fun (_, _, t1) (_, _, t2) -> Float.compare t2 t1)
  in
  let total_ns = List.fold_left (fun acc (_, _, t) -> acc +. t) 0. rows in
  let total_count = List.fold_left (fun acc (_, c, _) -> acc + c) 0 rows in
  Printf.printf "\n=== per-instruction timings (Unix wall clock) ===\n" ;
  Printf.printf "executed opcodes: %d distinct, %d total | accumulated time: %.3f ms\n\n"
    (List.length rows) total_count (total_ns /. 1.0e6) ;
  Printf.printf "  %-18s %12s %7s %14s %12s\n" "opcode" "count" "%time" "total (ms)" "avg (ns)" ;
  List.iter
    (fun (i, count, total) ->
      let name = Opcode.to_string (Opcode.of_byte (Char.chr i)) in
      let pct = 100. *. total /. (if total_ns = 0. then 1. else total_ns) in
      let avg = if count = 0 then 0. else total /. float_of_int count in
      Printf.printf "  %-18s %12d %6.1f%% %14.3f %12.1f\n" name count pct (total /. 1.0e6) avg )
    rows

let profile fn =
  if !minprof || !majprof || !promprof then (
    let _memprof = Gc.Memprof.start ~sampling_rate:0.0004 alloc_tracker in
    fn () ;
    summarize_allocs ~depth:!alloc_frames () )
  else fn ()

let () =
  begin
    profile (fun () ->
        let result, _state =
          let world_state = State.WorldState.empty in
          let block_state = State.BlockState.make world_state block in
          let transaction_state = State.TransactionState.make block_state Address.zero tx in
          let msg =
            {(Execution.prepare_message sender gas_limit tx) with code = bytecode; input_data = calldata}
          in
          Execution.Vm.execute msg bytecode transaction_state
        in
        Gc.print_stat Out_channel.stdout ;

        match result.status_code with
        | Success -> Format.printf "Ok\n"
        | _ -> Format.printf "Execution failure\n" ) ;
    summarize_instructions ()
  end
