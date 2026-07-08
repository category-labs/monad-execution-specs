(** Plug an external EVMC-compatible VM (a dynamically-loaded [.so]/[.dylib]) into the OCaml
    execution client, in place of the built-in interpreter.

    This is the inverse of [bindings/vm] (which exports the OCaml VM as an EVMC library). Here we
    expose the OCaml {!Monad_lib.Host} — a pure state monad over [TransactionState.t] — to the
    external VM as a C [evmc_host_interface] vtable, and call the VM's [execute] function. The
    impedance mismatch (pure state function vs. effectful C callbacks) is bridged with a mutable
    [TransactionState.t ref] that the callbacks read and write in place. This is sound because EVMC
    requires the VM to invoke host callbacks synchronously, on the calling thread, for the duration
    of a single [execute] call. *)

open Monad_lib
open Ctypes
open Common
module C = C_evmc
module B32 = Monad_lib.Byte_string.B32
module TransactionState = Host.TransactionState

(* The EVMC revision passed to the external VM. Hardcoded: the external VM is assumed Monad-aware
   and to expect a single fixed revision (see plan). We use EVMC_PRAGUE (13), matching the
   Prague-era feature level of the spec (EIP-7702 etc.); a lower revision such as London (9) would
   make a generic VM reject PUSH0 in the EIP-4788/EIP-2935 system contracts. *)
let monad_revision = 13

(* ------------------------------------------------------------------ *)
(* Loader                                                             *)
(* ------------------------------------------------------------------ *)

(* Derive the EVMC create-function base name from a library path, following the same rules as
   [evmc_load]: take the basename, strip all extensions and a "lib" prefix, replace '-' with '_'.
   e.g. "/path/libevmone.so.0.11" -> "evmone". *)
let create_base_name path =
  let base = Filename.basename path in
  let base = match String.index_opt base '.' with Some i -> String.sub base 0 i | None -> base in
  let base =
    if String.length base >= 3 && String.sub base 0 3 = "lib" then String.sub base 3 (String.length base - 3)
    else base
  in
  String.map (fun c -> if c = '-' then '_' else c) base

(* Load an EVMC VM from a shared library and return a pointer to its [evmc_vm] vtable. Mirrors
   [evmc_load_and_create]: dlopen, find the create function (by derived name, falling back to the
   generic "evmc_create"), instantiate, and check the ABI version. *)
let load (path : string) : C.Vm.repr structure ptr =
  let lib = Dl.dlopen ~filename:path ~flags:Dl.[RTLD_NOW; RTLD_GLOBAL] in
  let create_fn = void @-> returning (ptr C.Vm.repr) in
  let create =
    let sym = "evmc_create_" ^ create_base_name path in
    try Foreign.foreign ~from:lib sym create_fn with _ -> Foreign.foreign ~from:lib "evmc_create" create_fn
  in
  let vm = create () in
  if is_null vm then failwith (Printf.sprintf "evmc: create function returned NULL for %s" path) ;
  let abi = !@(vm |-> C.Vm.abi_version) in
  let expected = Int64.to_int C.evmc_abi_version in
  if abi <> expected then
    failwith (Printf.sprintf "evmc: ABI version mismatch (vm reports %d, expected %d)" abi expected) ;
  vm

(* ------------------------------------------------------------------ *)
(* The pluggable VM functor                                           *)
(* ------------------------------------------------------------------ *)

module Make (V : sig
  val vm : C.Vm.repr structure ptr
end) =
struct
  open C

  let make_host_interface (type t) (host : (module Evmc.HOST with type t = t)) (state : t ref) =
    let (module Host) = host in
    (* Run a host computation against the threaded state, writing back the resulting state. *)
    let run : 'a. (Host.t -> 'a * Host.t) -> 'a =
     fun m ->
      let v, s' = m !state in
      state := s' ;
      v
    in
    let addr_out p = Address.of_c !@p in
    let b32_out p = Bytes32.of_c !@p in

    let intf = make Host_interface.repr in
    (* Keep callback closures alive as long as [intf] is — [setf] writes only a raw pointer. *)
    let roots = ref [] in
    let keep : 'a. 'a -> 'a =
     fun x ->
      roots := Obj.repr x :: !roots ;
      x
    in
    let open Host_interface in
    setf intf account_exists
      (coerce (Foreign.funptr account_exists_fn) (static_funptr account_exists_fn)
         (keep (fun _ctx a -> run (Host.account_exists (addr_out a)))) ) ;
    setf intf get_storage
      (coerce (Foreign.funptr get_storage_fn) (static_funptr get_storage_fn)
         (keep (fun _ctx a k -> Bytes32.to_c (run (Host.get_storage (addr_out a) (b32_out k))))) ) ;
    setf intf set_storage
      (coerce (Foreign.funptr set_storage_fn) (static_funptr set_storage_fn)
         (keep (fun _ctx a k v -> run (Host.set_storage (addr_out a) (b32_out k) (b32_out v)))) ) ;
    setf intf get_balance
      (coerce (Foreign.funptr get_balance_fn) (static_funptr get_balance_fn)
         (keep (fun _ctx a -> Uint256be.to_c (run (Host.get_balance (addr_out a))))) ) ;
    setf intf get_code_size
      (coerce (Foreign.funptr get_code_size_fn) (static_funptr get_code_size_fn)
         (keep (fun _ctx a -> Unsigned.Size_t.of_int64 (run (Host.get_code_size (addr_out a))))) ) ;
    setf intf get_code_hash
      (coerce (Foreign.funptr get_code_hash_fn) (static_funptr get_code_hash_fn)
         (keep (fun _ctx a ->
              let h = match run (Host.get_code_hash (addr_out a)) with Some h -> h | None -> B32.zeros in
              Bytes32.to_c h ) ) ) ;
    setf intf copy_code
      (coerce (Foreign.funptr copy_code_fn) (static_funptr copy_code_fn)
         (keep (fun _ctx a offset buf size ->
              let offset = Unsigned.Size_t.to_int offset and size = Unsigned.Size_t.to_int size in
              let s : string = run (Host.copy_code (addr_out a) ~offset ~size) in
              let n = min (String.length s) size in
              for i = 0 to n - 1 do
                buf +@ i <-@ Unsigned.UInt8.of_int (Char.code s.[i])
              done ;
              Unsigned.Size_t.of_int n ) ) ) ;
    setf intf selfdestruct
      (coerce (Foreign.funptr selfdestruct_fn) (static_funptr selfdestruct_fn)
         (keep (fun _ctx a b -> run (Host.selfdestruct ~address:(addr_out a) ~beneficiary:(addr_out b)))) ) ;
    setf intf call
      (coerce (Foreign.funptr call_fn) (static_funptr call_fn)
         (keep (fun _ctx msg -> Result.to_c (run (Host.call (Message.of_c !@msg))))) ) ;
    (* [get_tx_context] returns a pointer; keep the marshalled struct alive past the callback so the
       VM can read it. *)
    let tx_context_keepalive = ref None in
    setf intf get_tx_context
      (coerce (Foreign.funptr get_tx_context_fn) (static_funptr get_tx_context_fn)
         (keep (fun _ctx ->
              let s = Tx_context.to_c (run Host.get_tx_context) in
              tx_context_keepalive := Some s ;
              addr s ) ) ) ;
    setf intf get_block_hash
      (coerce (Foreign.funptr get_block_hash_fn) (static_funptr get_block_hash_fn)
         (keep (fun _ctx n ->
              let h = match run (Host.get_block_hash n) with Some h -> h | None -> B32.zeros in
              Bytes32.to_c h ) ) ) ;
    setf intf emit_log
      (coerce (Foreign.funptr emit_log_fn) (static_funptr emit_log_fn)
         (keep (fun _ctx a data data_size topics topics_count ->
              let data = Bytes.of_c data data_size in
              let topics = List.of_c (coerce (ptr Bytes32.repr) (ptr Bytes32.t) topics) topics_count in
              run (Host.emit_log (addr_out a) ~data ~topics) ) ) ) ;
    setf intf access_account
      (coerce (Foreign.funptr access_account_fn) (static_funptr access_account_fn)
         (keep (fun _ctx a -> run (Host.access_account (addr_out a)))) ) ;
    setf intf access_storage
      (coerce (Foreign.funptr access_storage_fn) (static_funptr access_storage_fn)
         (keep (fun _ctx a k -> run (Host.access_storage (addr_out a) (b32_out k)))) ) ;
    setf intf get_transient_storage
      (coerce
         (Foreign.funptr get_transient_storage_fn)
         (static_funptr get_transient_storage_fn)
         (keep (fun _ctx a k -> Bytes32.to_c (run (Host.get_transient_storage (addr_out a) (b32_out k))))) ) ;
    setf intf set_transient_storage
      (coerce
         (Foreign.funptr set_transient_storage_fn)
         (static_funptr set_transient_storage_fn)
         (keep (fun _ctx a k v -> run (Host.set_transient_storage (addr_out a) (b32_out k) (b32_out v)))) ) ;
    (* The tx-context keepalive ref is reachable through its (rooted) closure, so it needs no
       separate root. Tie all closures to [intf]'s lifetime. *)
    tie_lifetime ~child:!roots ~parent:intf ;
    intf

  let execute (type t) (host : (module Evmc.HOST with type t = t)) (msg : Evmc.Message.t) (code : Bytes.t) :
      t -> Evmc.Result.t * t =
   fun (s0 : t) ->
    let state = ref s0 in
    let intf = make_host_interface host state in
    let ctx = from_voidp Host_context.repr null in
    let msg_c = Message.to_c msg in
    let code_ptr, code_size = Bytes.to_c code ~ownership:Local in
    Format.printf "code is %s\n%!" (Bytes.to_hex_string code) ;
    let exec = coerce (static_funptr Vm.execute_fn) (Foreign.funptr Vm.execute_fn) !@(V.vm |-> Vm.execute) in
    let result_c = exec V.vm (addr intf) ctx monad_revision (addr msg_c) code_ptr code_size in
    let result = Result.of_c result_c in
    (* Keep the C-side inputs reachable across the synchronous call. *)
    ignore (Sys.opaque_identity intf) ;
    ignore (Sys.opaque_identity msg_c) ;
    ignore (Sys.opaque_identity code_ptr) ;
    (result, !state)
end
