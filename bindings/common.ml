(** Common utilities for sharing data with Ctypes. *)
open Ctypes

open Monad_lib
open Byte_string

let malloc = Foreign.foreign "malloc" (size_t @-> returning (ptr void))
let free = Foreign.foreign "free" (ptr void @-> returning void)

(* Libffi does not allow passing or returning arrays from functions, including arrays stored in structs.
   Therefore any byte-array types need to be declared as structs with N scalar fields instead. *)
module Byte_array (Bs : sig
  type t
  val byte_width : int
  val init : (int -> char) -> t
  val iteri : (int -> char -> unit) -> t -> unit
  val name : string
end) =
struct
  type repr

  let repr : repr structure typ = structure Bs.name
  let bytes = Iarray.init Bs.byte_width (fun i -> field repr (Format.sprintf "bytes_%i" i) uint8_t)
  let () = seal repr

  type t = Bs.t
  let of_c (repr : repr structure) =
    Bs.init (fun i -> getf repr (Iarray.get bytes i) |> Unsigned.UInt8.to_int |> Char.chr)
  let to_c (bs : t) : repr structure =
    let repr = make repr in
    Bs.iteri (fun i (b : char) -> Char.code b |> Unsigned.UInt8.of_int |> setf repr (Iarray.get bytes i)) bs ;
    repr
  let t = view ~read:of_c ~write:to_c repr
end

(* A common pitfall when using CTypes is to allocate a CArray, then store a pointer to that array inside a
   C struct and pass that to a C function. If the programmer does not explicitly keep around a reference to
   the original CArray or the fat pointer to it, then it may be garbage-collected as the C struct only stores
   a raw pointer.
   To solve this and retain some form of compositionality, every function that allocates C objects and returns
   a C-style pointer takes an extra `ownership` argument that determines whether the result is manually
   managed, bound to the lifetime of a parent, or exists only inside a local scope (statically unenforceable
   outside of OxCaml).
   See e.g. https://github.com/yallop/ocaml-ctypes/issues/571 *)
let tie_lifetime ~child ~parent = Gc.finalise (fun _ -> ignore (Sys.opaque_identity child)) parent

type (_, _) ownership =
  | Tied_to : 'a -> ('r, 'r) ownership
  | Manual : ('r, 'r * unit ptr) ownership
  | Local : ('r, 'r) ownership (* Caller must make sure the object does not escape its lexical scope. *)

let apply_ownership (type r) (type s) ~(ownership : (r, s) ownership) (obj : r) : s =
  match ownership with
  | Tied_to parent -> tie_lifetime ~child:obj ~parent ; obj
  | Manual ->
      let handle = Root.create obj in
      (obj, handle)
  | Local -> obj

module Bytes = struct
  include Bytes
  let of_c (pointer : Unsigned.uint8 ptr) (size : Unsigned.size_t) : t =
    string_from_ptr (coerce (ptr uint8_t) (ptr char) pointer) ~length:(Unsigned.Size_t.to_int size)

  let to_c (bs : t) =
    let pointer =
      if Stdlib.(length bs = 0) then from_voidp uint8_t null
      else
        let arr = CArray.of_string bs in
        coerce (ptr char) (ptr uint8_t) (CArray.start arr)
    in
    let size = Unsigned.Size_t.of_int (length bs) in
    let result = (pointer, size) in
    apply_ownership result
end

module List = struct
  include List
  let of_c (pointer : 'a ptr) (size : Unsigned.size_t) =
    List.init (Unsigned.Size_t.to_int size) (fun i -> !@(pointer +@ i))

  let to_c (elt_typ : 'a typ) (l : 'a list) =
    let arr = CArray.of_list elt_typ l in
    let ptr = CArray.start arr in
    let size = Unsigned.Size_t.of_int (CArray.length arr) in
    (* We need to be careful to tie the ownership of array elements to the array itself, as their lexical
       scope does not outlive this function. *)
    tie_lifetime ~child:l ~parent:ptr ;
    apply_ownership (ptr, size)
end

(* Ad-hoc monad for handling `with_open` *)
let ( let$ ) (k : ('h -> 'o) -> 'o) (f : 'h -> 'o) = k f

let gen_struct_generator
    ~(filename : string) ~(includes : string list) (bindings : (module Cstubs_structs.BINDINGS)) =
  let$ out_fd = Out_channel.with_open_text filename in
  let out_fmt = Format.formatter_of_out_channel out_fd in

  List.iter (fun lib -> Format.fprintf out_fmt "#include <%s>\n" lib) includes ;
  Cstubs_structs.write_c out_fmt bindings

(** Cstubs_inverted works by passing a module of type [Cstubs_inverted.INTERNAL] to a template module. The
    [INTERNAL] instance allows the template to register types and functions to be exposed to C. However, when
    registering a C function through [Cstubs_inverted.INTERNAL.internal], its address is not available to the
    OCaml code.
    We extend the Cstubs_inverted function registration mechanism here to give us pointers to every top-level
    C function that is registered from the OCaml side. This is necessary in order to build an EVMC-style vtable
    without using libffi to marshal OCaml closures (which causes issues with sanitizers). This works by
    combining the exporting pass of [Cstubs_inverted]:
      {v ML template -> C+ML declaring exported C functions -> dynlib v}
    with the importing pass of [Cstubs]:
      {v ML template -> C+ML declaring imported C functions v}

    + The programmer defines a [BINDINGS] instance that declares OCaml functions to be exported as C bindings
      by calling [INTERNAL.internal]. Each such declaration returns a pointer to the C function that will be
      exported.
    + At build time, the [BINDINGS] functor is passed to the [gen_inverted_stubs] generator.
      [gen_inverted_stubs] instantiates the functor and generates C bindings for the OCaml functions as
      usual with [Cstubs_inverted], but additionally it collects the names of all exported functions and
      uses [Cstubs] to generate "address accessor" C functions that return the address of each of the exported
      C bindings as OCaml objects. During build-time execution, calls to [INTERNAL.internal] return null
      pointers, as the address of the C functions cannot be determined at this point.
    + To build the final run-time library, the generated C and ML files above are linked together with the
      original [BINDINGS] instance. At run-time, calls to [INTERNAL.internal] register the OCaml callback
      into [Cstubs_inverted]'s callback table and return pointers to the corresponding C functions via a
      call to the "address accessor" functions. *)
module type INTERNAL = sig
  include Cstubs_inverted.INTERNAL
  val internal :
    ?runtime_lock:bool -> string -> ('a -> 'b) Ctypes.fn -> ('a -> 'b) -> ('a -> 'b) Ctypes.static_funptr
end

(** As [Cstubs_inverted.BINDINGS], instances of [BINDINGS] are applied repeatedly during code generation and
    also at runtime. Every application must register the same unique names, function types, and runtime-lock
    settings in the same order. Initialization side effects must be safe to repeat. During code generation,
    [INTERNAL.internal] returns null placeholder pointers; the real pointers are only inserted at runtime. *)
module type BINDINGS = functor (_ : INTERNAL) -> sig end

(** Implement [INTERNAL] from the modules generated by [gen_inverted_stubs]. *)
module Internal
    (Inverted : Cstubs_inverted.INTERNAL)
    (Addresses : sig
      val foreign_value : string -> 'a Ctypes.typ -> 'a Ctypes.ptr
    end) : INTERNAL = struct
  include Inverted
  let internal ?runtime_lock name fn f =
    Inverted.internal ?runtime_lock name fn f ;
    coerce (ptr void) (static_funptr fn) (Addresses.foreign_value name void)
end

(** Placeholder returned for registered functions while generating stubs, see the [BINDINGS] contract above. *)
let null_funptr fn = coerce (ptr void) (static_funptr fn) null

(** Collect all the function names declared by a [BINDINGS] instance. *)
let collect_callback_names (module B : BINDINGS) =
  let names = ref [] in
  let module _ = B (struct
    let enum _ _ = ()
    let structure _ = ()
    let union _ = ()
    let typedef _ _ = ()
    let internal ?runtime_lock:_ name fn _ =
      names := name :: !names ;
      null_funptr fn
  end) in
  List.rev !names

let gen_inverted_stubs
    ~(filename_without_extension : string) ~(includes : string list) ~(prefix : string) (module B : BINDINGS)
    : unit =
  let filename = function
    | `C -> Format.sprintf "%s.c" filename_without_extension
    | `H -> Format.sprintf "%s.h" filename_without_extension
    | `Ml -> Format.sprintf "%s.ml" filename_without_extension
  in

  let names = collect_callback_names (module B) in
  let module Stubs (I : Cstubs_inverted.INTERNAL) = B (struct
    include I
    let internal ?runtime_lock name fn f = I.internal ?runtime_lock name fn f ; null_funptr fn
  end) in
  (* Walk over the function names declared in the bindings and collect their addresses. *)
  let module Addresses (F : Cstubs.FOREIGN with type 'a result = unit) = struct
    let () = List.iter (fun name -> F.foreign_value name void) names
  end in
  let addresses_prefix = prefix ^ "_address" in

  let$ ml_fd = Out_channel.with_open_text (filename `Ml) in
  let ml_fmt = Format.formatter_of_out_channel ml_fd in
  Cstubs_inverted.write_ml ml_fmt ~prefix (module Stubs) ;
  Format.fprintf ml_fmt "@\nmodule Addresses = struct@\n" ;
  Cstubs.write_ml ml_fmt ~prefix:addresses_prefix (module Addresses) ;
  Format.fprintf ml_fmt "end@." ;

  let$ h_fd = Out_channel.with_open_text (filename `H) in
  let h_fmt = Format.formatter_of_out_channel h_fd in
  List.iter (fun lib -> Format.fprintf h_fmt "#include <%s>\n" lib) includes ;
  Cstubs_inverted.write_c_header h_fmt ~prefix (module Stubs) ;

  let$ c_fd = Out_channel.with_open_text (filename `C) in
  let c_fmt = Format.formatter_of_out_channel c_fd in
  List.iter (fun lib -> Format.fprintf c_fmt "#include <%s>\n" lib) includes ;
  Cstubs_inverted.write_c c_fmt ~prefix (module Stubs) ;
  Cstubs.write_c c_fmt ~prefix:addresses_prefix (module Addresses) ;
  (* Insert a constructor to automatically load the OCaml runtime on dlopen. Note that there is no destructor
     to call caml_shutdown, so repeated calls to dlopen and dlclose will leak resources. *)
  Format.fprintf c_fmt
    {|
#include <caml/callback.h>

__attribute__((constructor))
static void _%s_init_ocaml_runtime(void) {
    static char *argv[] = { "_%s_init_ocaml", NULL };
    caml_startup(argv);
}
|}
    prefix prefix
