open Monad_lib
open Numeric

type event =
  | Nil
  | Alloc_major of Gc.Memprof.allocation
  | Alloc_minor of Gc.Memprof.allocation
  | Promotion of int
  | Dealloc_major of int
  | Dealloc_minor of int

let n_events = ref 0
let events = Array.make 500_000 Nil

let push event =
  let n = !n_events in
  incr n_events;
  events.(n) <- event;
  n

let tracker =
  let alloc_minor alloc = Some (push (Alloc_minor alloc)) in
  let alloc_major alloc = Some (push (Alloc_major alloc)) in
  let promote minor_idx = Some (push (Promotion minor_idx)) in
  let dealloc_minor idx = ignore (push (Dealloc_minor idx)) in
  let dealloc_major idx = ignore (push (Dealloc_major idx)) in
  Gc.Memprof.{alloc_minor; alloc_major; promote; dealloc_minor; dealloc_major}

let count ~prop arr = arr |> Array.to_seq |> Seq.filter prop |> Seq.length

let is_major_alloc = function Alloc_major _ -> true | _ -> false
let is_minor_alloc = function Alloc_minor _ -> true | _ -> false
let is_promotion = function Promotion _ -> true | _ -> false
let is_major_dealloc = function Dealloc_major _ -> true | _ -> false
let is_minor_dealloc = function Dealloc_minor _ -> true | _ -> false

let dump_memprof_info () =
  let events = Array.init !n_events (fun i -> events.(i)) in
  let major_allocs = count ~prop:is_major_alloc events in
  let minor_allocs = count ~prop:is_minor_alloc events in
  let promotions = count ~prop:is_promotion events in
  Format.eprintf "Major allocs: %d\n" major_allocs;
  Format.eprintf "Minor allocs: %d\n" minor_allocs;
  Format.eprintf "Promotions: %d\n" promotions

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

module Params = struct
  let chain_id = Uint.zero
end

module Evm = struct
  module Evm0 =
    Host.Instantiate
      (Params)
      (Vm.Make (struct
        let trace = false
      end))

  (* Unfold one level of recursion to get access to the full signature of Vm *)
  module Vm =
    Vm.Make
      (struct
        let trace = false
      end)
      (Evm0.Host)
  module Host = Host.Make (Params) (Vm)
end

let max_pc = ref None
let trace = ref false

let usage_msg = Format.sprintf "%s <max_pc> [--trace]" Sys.argv.(0)

let arg_spec = [("--trace", Arg.Set trace, "Enable GC tracing")]

let () =
  Arg.parse arg_spec
    (fun s ->
      match !max_pc with
      | None -> max_pc := Some (U256.of_string s)
      | Some _ -> raise (Arg.Bad "Too many arguments") )
    usage_msg

let max_pc = Option.get !max_pc
let trace = !trace

let rec counter () : U256.t Evm.Vm.M.t =
  Evm.Vm.M.(
    let$ state = get in
    let pc = state.machine_state.pc in
    if U256.(pc >= max_pc) then return pc
    else
      let$ () = put {state with machine_state = {state.machine_state with pc = U256.(pc + one)}} in
      counter () )

let run ~trace fn =
  if trace then (
    let profiler = Gc.Memprof.start ~sampling_rate:0.001 tracker in
    let result = fn () in
    Gc.Memprof.stop () ;
    Gc.Memprof.discard profiler ;
    dump_memprof_info ();
    result )
  else fn ()

let () =
  let ctl = Gc.get () in
  let ctl = Gc.{ctl with minor_heap_size = 8 * 1024 * 1024 (*; space_overhead = 200*)} in
  Gc.set ctl ;
  ignore ctl ;
  let k = counter () in
  let _res, _ctx =
    run ~trace (fun () -> Evm.Host.run (Evm.Vm.M.StHost.run k Vm.Context.empty) Host.TransactionState.empty)
  in
  ()
