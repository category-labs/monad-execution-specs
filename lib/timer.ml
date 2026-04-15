(** Utilities for timing subprograms. *)

type t = {name : string; mutable time_ns : int64}

module M = Map.Make (String)

let timers : t M.t ref = ref M.empty

let make name =
  match M.find_opt name !timers with
  | Some t -> t
  | None ->
      let t = {name; time_ns = 0L} in
      timers := M.add name t !timers ;
      t

let timed timer f =
 fun x ->
  let start = Mtime_clock.elapsed_ns () in
  let result = f x in
  let delta = Int64.sub (Mtime_clock.elapsed_ns ()) start in
  timer.time_ns <- Int64.add timer.time_ns delta ;
  result

let reset timer = timer.time_ns <- 0L

let reset_all () = M.iter (fun _ timer -> reset timer) !timers

let report ?(formatter = Format.std_formatter) () =
  let timers = M.to_list !timers in
  let name_width = List.fold_left (fun l (name, _) -> max l (String.length name)) 0 timers in
  Format.fprintf formatter "Timer stats:\n" ;
  List.iter
    (fun (name, timer) -> Format.fprintf formatter "%-*s %Ldns\n" name_width name timer.time_ns)
    timers
