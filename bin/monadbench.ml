open Monad_lib
open Numeric

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

let max_pc : U256.t = U256.of_string Sys.argv.(1)

let rec counter () : U256.t Evm.Vm.M.t =
  Evm.Vm.M.(
    let$ state = get in
    let pc = state.machine_state.pc in
    if U256.(pc >= max_pc) then return pc
    else
      let$ () = put {state with machine_state = {state.machine_state with pc = U256.(pc + one)}} in
      counter () )

let () =
  let ctl = Gc.get () in
  let ctl = Gc.{ctl with minor_heap_size = 8 * 1024 * 1024 (*; space_overhead = 200*)} in
  Gc.set ctl ;
  ignore ctl ;
  let profiler = Gc.Memprof.start ~sampling_rate:0.001 tracker in
  let k = counter () in
  let (_res, _ctx) = Evm.Host.run (Evm.Vm.M.StHost.run k Vm.Context.empty) Host.TransactionState.empty in
  Gc.Memprof.stop () ;
  Gc.Memprof.discard profiler ;
  dump_allocs "Major" !major_allocs ;
  dump_allocs "Minor" !minor_allocs ;
  Format.eprintf "Promotions %d\n" !promotions
