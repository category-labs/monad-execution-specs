open Monad_lib

(* Using only three characters ensures paths have overlaps to test Patricia compression *)

let max_path_length = int_of_string Sys.argv.(1)
let max_trie_elements = int_of_string Sys.argv.(2)
let n_trials = int_of_string Sys.argv.(3)

let random_path () =
  let length = Random.int_in_range ~min:10 ~max:max_path_length in
  Nibbles.init length (fun _ -> (Random.int 16))

let random_root_hash () =
  let length = Random.int_in_range ~min:10 ~max:max_trie_elements in
  Seq.ints 0
  |> Seq.take length
  |> Seq.map (fun _ -> (let p = random_path () in p.bytes, "1"))
  (*|> Mpt.Trie.of_seq
  |> Mpt.PatriciaTrie.of_trie*)
  (*|> Mpt.PatriciaTrie.of_seq*)
  |> Mpt.of_seq
  |> fun mpt -> mpt.root_hash

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
          | Some loc when String.equal loc.filename "lib/mpt.ml" -> Some loc
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

let () =
  let ctl = Gc.get () in
  let ctl = Gc.{ctl with minor_heap_size = 8 * 1024 * 1024 (*; space_overhead = 200*)} in
  Gc.set ctl ;
  (*
  ignore ctl ;
  let profiler = Gc.Memprof.start ~sampling_rate:0.0001 tracker in
   *)
  for i = 0 to n_trials do
    ignore (random_root_hash ())
  done ;
  (*
  Gc.Memprof.stop () ;
  Gc.Memprof.discard profiler ;
   *)
  dump_allocs "Major" !major_allocs ;
  dump_allocs "Minor" !minor_allocs ;
  Format.eprintf "Promotions %d\n" !promotions
