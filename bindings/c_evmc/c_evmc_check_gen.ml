open Ctypes

let check expression expected = Printf.printf "_Static_assert(%s == %d, %S);\n" expression expected expression

module Checked = struct
  include C_evmc_generated

  (* Compute the layout described by the bindings, rather than importing the
     header's layout. Enum representations still come from the header probe. *)
  let structure = Ctypes.structure
  let field = Ctypes.field

  let inspect : type a. a typ -> unit =
   fun typ ->
    let name =
      match typ with
      | Ctypes_static.Struct {tag; _} -> "struct " ^ tag
      | Ctypes_static.Union {utag; _} -> "union " ^ utag
      | _ -> Ctypes.string_of_typ typ
    in
    check (Printf.sprintf "sizeof(%s)" name) (Ctypes.sizeof typ) ;
    match typ with
    | Ctypes_static.Struct {fields; _} ->
        List.iter
          (fun (Ctypes_static.BoxedField field) ->
            let member = Ctypes.field_name field in
            check
              (Printf.sprintf "sizeof(((%s *)0)->%s)" name member)
              (Ctypes.sizeof (Ctypes.field_type field)) ;
            check (Printf.sprintf "offsetof(%s, %s)" name member) (Ctypes.offsetof field) )
          fields
    | _ -> ()

  let seal typ = Ctypes.seal typ ; inspect typ
end

let () =
  print_endline "#include <stddef.h>\n#include <evmc/evmc.h>" ;
  check "sizeof(struct evmc_bytes32)" (sizeof C_evmc_template.Bytes32.repr) ;
  check "sizeof(((struct evmc_bytes32 *)0)->bytes)" 32 ;
  check "sizeof(struct evmc_address)" (sizeof C_evmc_template.Address.repr) ;
  check "sizeof(((struct evmc_address *)0)->bytes)" 20
module Layout = C_evmc_template.Types (Checked)
