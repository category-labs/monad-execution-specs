open Monad_lib

module Vm = Bindings.Vm.Pack (Vm.Make (struct
  let trace = false
end))

let () =
  let open Ctypes in
  let ptr = coerce (ptr Bindings.Vm.repr) (ptr void) Vm.vm in
  let i = Nativeint.to_int (raw_address_of_ptr ptr) in
  Format.printf "i = %x\n" i ; Format.print_flush () ; Callback.register "monad_vm" i
