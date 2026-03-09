(* Ad-hoc monad for handling `with_open` *)
let ( let$ ) (k : ('h -> 'o) -> 'o) (f : 'h -> 'o) = k f

let () =
  let dir_name = Sys.argv.(1) in
  let path kind =
    let extension = match kind with `C -> "c" | `H -> "h" | `Ml -> "ml" in
    let file_name = Format.sprintf "fuzzrun_stubs_generated.%s" extension in
    Filename.concat dir_name file_name
  in

  let$ ml_fd = Out_channel.with_open_text (path `Ml) in
  let$ c_fd = Out_channel.with_open_text (path `C) in
  let$ h_fd = Out_channel.with_open_text (path `H) in

  let prefix = "execrun" in
  let stubs = (module Bindings.Stubs : Cstubs_inverted.BINDINGS) in

  Cstubs_inverted.write_ml (Format.formatter_of_out_channel ml_fd) ~prefix stubs ;
  Cstubs_inverted.write_c_header (Format.formatter_of_out_channel h_fd) ~prefix stubs ;
  Cstubs_inverted.write_c (Format.formatter_of_out_channel c_fd) ~prefix stubs
