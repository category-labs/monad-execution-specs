open Monad_lib

module Vm = Bindings.Vm.Pack (Vm.Make (struct
  let trace = Sys.getenv_opt "MONAD_ML_TRACE" |> Option.map bool_of_string |> Option.value ~default:false
end))

let () =
  let open Ctypes in
  let ptr = coerce (ptr Bindings.Vm.repr) (ptr void) Vm.vm in
  let i = Nativeint.to_int (raw_address_of_ptr ptr) in
  Callback.register "monad_vm" i
