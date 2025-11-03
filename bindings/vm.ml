open Monad_lib
open Numeric

module Vm = Evmc.C.OCamlVM (Vm.Make (struct
  let trace = true
  let chain_id = U256.of_int 1234
end))

let () =
  let open Ctypes in
  let ptr = coerce (ptr Evmc.C.Vm.repr) (ptr void) Vm.vm in
  let i = Nativeint.to_int (raw_address_of_ptr ptr) in
  Format.printf "i = %x\n" i ;
  Format.print_flush () ;
  Callback.register "monad_vm" i
