open Typedtree

(* Inspect resolved identifiers and instantiated types, not operator spelling:
   local opens may select a field-specific (=), while a generic comparison can
   hide behind an alias. Scalar primitives need no structural comparison of
   domain values; reject every other use, including unconstrained type variables. *)
let comparison_primitives =
  [ "%equal"
  ; "%notequal"
  ; "%lessthan"
  ; "%lessequal"
  ; "%greaterthan"
  ; "%greaterequal"
  ; "%compare"
  ; "%eq"
  ; "%noteq" ]

let comparison_functions =
  [ "Stdlib.min"
  ; "Stdlib.max"
  ; "Stdlib.List.mem"
  ; "Stdlib.List.mem_assoc"
  ; "Stdlib.List.assoc"
  ; "Stdlib.List.assoc_opt"
  ; "Stdlib.List.remove_assoc"
  ; "Stdlib.Array.mem"
  ; "Stdlib.Iarray.mem"
  ; "Stdlib.Seq.mem" ]

let rec head env ty =
  match Types.get_desc (Ctype.expand_head env ty) with Types.Tpoly (ty, []) -> head env ty | desc -> desc

let scalar_argument env ty =
  match head env ty with
  | Types.Tarrow (_, arg, _, _) -> (
    match head env arg with
    | Types.Tconstr (Path.Pident id, [], _) ->
        Ident.is_predef id && List.mem (Ident.name id) ["int"; "bool"; "char"; "string"]
    | _ -> false )
  | _ -> false

let inspect filename =
  let info = Cmt_format.read_cmt filename in
  (* Dune runs the audit from the build root, where the CMT's relative load paths
     resolve both normally and inside a test sandbox. *)
  Load_path.init ~auto_include:Load_path.no_auto_include ~visible:info.cmt_loadpath.visible
    ~hidden:info.cmt_loadpath.hidden ;
  Env.reset_cache () ;
  let failures = ref 0 in
  let iter =
    { Tast_iterator.default_iterator with
      expr =
        (fun self e ->
          ( match e.exp_desc with
          | Texp_ident (path, _, vd) ->
              let name = Path.name path in
              let comparison =
                match vd.Types.val_kind with
                | Types.Val_prim prim -> List.mem prim.Primitive.prim_name comparison_primitives
                | _ -> List.mem name comparison_functions
              in
              if comparison then
                let env = Envaux.env_of_only_summary e.exp_env in
                if not (scalar_argument env e.exp_type) then (
                  incr failures ;
                  let loc = e.exp_loc.loc_start in
                  Format.eprintf "%s:%d: structural comparison %s : %a@." loc.pos_fname loc.pos_lnum name
                    Printtyp.type_scheme e.exp_type )
          | _ -> () ) ;
          Tast_iterator.default_iterator.expr self e ) }
  in
  (match info.cmt_annots with Implementation s -> iter.structure iter s | _ -> ()) ;
  !failures

let () =
  try
    if Array.length Sys.argv < 2 then failwith "No CMT files supplied to comparison audit" ;
    let failures =
      Array.fold_left
        (fun count filename -> count + inspect filename)
        0
        (Array.sub Sys.argv 1 (Array.length Sys.argv - 1))
    in
    if failures > 0 then exit 1 ;
    Printf.printf "Checked %d library CMT files: no non-scalar polymorphic comparisons.\n"
      (Array.length Sys.argv - 1)
  with exn ->
    Location.report_exception Format.err_formatter exn ;
    exit 2
