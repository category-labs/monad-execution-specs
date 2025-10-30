let () =
  let f = Format.formatter_of_out_channel (open_out "gen_evmc_bindings.c") in
  Format.fprintf f {|#include <evmc/evmc.h>@.|};
  Cstubs.write_c ~prefix:"" f (module Monad_lib.Evmc.C)
