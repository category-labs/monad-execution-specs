let () =
  let filename = Sys.argv.(1) in
  Common.gen_struct_generator ~filename ~includes:["evmc/evmc.h"] (module C_evmc_template.Types)
