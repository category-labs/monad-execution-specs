let () =
  Array.iteri
    (fun i text ->
      if i > 0 then
        print_endline
          ( try
              let value = Monad_lib.Numeric.Uint.of_string text in
              Z.to_string (Monad_lib.Numeric.Uint.to_z value)
            with Invalid_argument _ | Monad_lib.Numeric.Domain_error _ -> "Error" ) )
    Sys.argv
