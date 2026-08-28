module Stubs (I : Cstubs_inverted.INTERNAL) = struct
  open Monad_lib
  open Byte_string
  open Numeric

  open Ctypes
  open Common

  (* TODO: make this configurable. *)
  module Chain_params : Chain.Monad.PARAMS = struct
    include Chain.Monad.Mainnet

    (* TODO: bump to Nine once EIP-5 lands. *)
    let revision = `Eight
  end

  (* Unpack a C host vtable into an Evmc.Host implementation. *)
  module C_host (Host : sig
    val intf : C_evmc.Host_interface.repr structure ptr
    val ctx : C_evmc.Host_context.repr structure ptr
  end) : Evmc.HOST with type t = unit = struct
    type t = unit

    type 'a st = unit -> 'a * unit
    let return (v : 'a) : 'a st = fun () -> (v, ())

    open C_evmc
    open Host_interface

    (* Wrap a C vtable function pointer in an OCaml-level closure. *)
    let bind (fn_typ : (C_evmc.Host_context.repr structure ptr -> 'a) fn) field =
      let coercion = coerce (static_funptr fn_typ) (Foreign.funptr fn_typ) in
      coercion !@(Host.intf |-> field) Host.ctx

    let addr_in a = addr (Address.to_c a)

    let b32_in bs = addr (Bytes32.to_c bs)
    let b32_out bs = Bytes32.of_c bs

    let account_exists : Address.t -> bool st =
      let f = bind account_exists_fn account_exists in
      fun acc -> return (f (addr_in acc))

    let get_storage : Address.t -> B32.t -> B32.t st =
      let f = bind get_storage_fn get_storage in
      fun acc loc -> return (b32_out (f (addr_in acc) (b32_in loc)))

    let set_storage : Address.t -> B32.t -> B32.t -> Evmc.StorageStatus.t st =
      let f = bind set_storage_fn set_storage in
      fun acc loc v -> return (f (addr_in acc) (b32_in loc) (b32_in v))

    let get_balance : Address.t -> U256.t st =
      let f = bind get_balance_fn get_balance in
      fun acc -> return (Uint256be.of_c (f (addr_in acc)))

    let get_code_size : Address.t -> Uint64.t st =
      let f = bind get_code_size_fn get_code_size in
      fun acc -> return (Unsigned.Size_t.to_int64 (f (addr_in acc)))

    let get_code_hash : Address.t -> B32.t option st =
      let f = bind get_code_hash_fn get_code_hash in
      fun acc ->
        return
          (let r = b32_out (f (addr_in acc)) in
           if B32.(equal r zeros) then None else Some r )

    let copy_code : Address.t -> offset:int -> size:int -> Bytes.t st =
      let f = bind copy_code_fn copy_code in
      fun addr ~offset ~size ->
        return
          (let buf = CArray.make uint8_t size in
           let n =
             f (addr_in addr) (Unsigned.Size_t.of_int offset) (CArray.start buf) (Unsigned.Size_t.of_int size)
           in
           Bytes.of_c (CArray.start buf) n )

    let selfdestruct : address:Address.t -> beneficiary:Address.t -> bool st =
      let f = bind selfdestruct_fn selfdestruct in
      fun ~address ~beneficiary -> return (f (addr_in address) (addr_in beneficiary))

    let call : Evmc.Message.t -> Evmc.Result.t st =
      let f = bind call_fn call in
      fun msg -> return (Result.of_c (f (addr (Message.to_c msg))))

    let get_tx_context : Evmc.TxContext.t st =
      let ptr = bind get_tx_context_fn get_tx_context in
      return (Tx_context.of_c !@ptr)

    let get_block_hash : Uint64.t -> B32.t option st =
      let f = bind get_block_hash_fn get_block_hash in
      fun n ->
        return
          (let r = b32_out (f n) in
           if B32.(equal r zeros) then None else Some r )

    let emit_log : Address.t -> data:Bytes.t -> topics:B32.t list -> unit st =
      let f = bind emit_log_fn emit_log in
      fun addr ~data ~topics ->
        return
          (let data_ptr, data_size = Bytes.to_c data ~ownership:Local in
           let topics_ptr, topics_count = Common.List.to_c Bytes32.t topics ~ownership:Local in
           f (addr_in addr) data_ptr data_size
             (coerce (ptr Bytes32.t) (ptr Bytes32.repr) topics_ptr)
             topics_count )

    let access_account : Address.t -> [`Warm | `Cold] st =
      let f = bind access_account_fn access_account in
      fun acc -> return (f (addr_in acc))

    let access_storage : Address.t -> B32.t -> [`Warm | `Cold] st =
      let f = bind access_storage_fn access_storage in
      fun acc k -> return (f (addr_in acc) (b32_in k))

    let get_transient_storage : Address.t -> B32.t -> B32.t st =
      let f = bind get_transient_storage_fn get_transient_storage in
      fun acc k -> return (b32_out (f (addr_in acc) (b32_in k)))

    let set_transient_storage : Address.t -> B32.t -> B32.t -> unit st =
      let f = bind set_transient_storage_fn set_transient_storage in
      fun acc k v -> return (f (addr_in acc) (b32_in k) (b32_in v))
  end

  (* Bindings to the monadml_evm fields. Currently, all the monadml_evm fields are
     allocated statically once when the dynamic library is loaded, and a call to
     make_monadml_evm simply returns a struct containing these pre-allocated pointers.
     Any data allocated by this module, including closures, must remain alive
     indefinitely. *)
  module Evm_bindings = struct
    open C_evmc
    open Vm

    (* Coerce an OCaml closure to a static_funptr with global lifetime. The closure f will never be
       released by the garbage collector. *)
    let to_static_funptr ty f =
      let _ = Root.create f in
      coerce (Foreign.funptr ty) (static_funptr ty) f

    let name =
      let name = CArray.of_string "monadml_evm" in
      let _ = Root.create name in
      CArray.start name

    let version =
      let version = CArray.of_string Version.hash in
      let _ = Root.create version in
      CArray.start version

    (* The VM instance is statically allocated, so deallocating it is a no-op, however EVMC requires
       the destroy callback to be non-null. *)
    let destroy_impl (_vm : Vm.repr structure ptr) = ()
    let destroy = to_static_funptr destroy_fn destroy_impl

    let execute_impl
        (debug_tstore : bool)
        (_vm : Vm.repr structure ptr)
        (intf : Host_interface.repr structure ptr)
        (ctx : Host_context.repr structure ptr)
        (_rev : int)
        (msg : Message.repr structure ptr)
        (code : Unsigned.UInt8.t ptr)
        (code_size : Unsigned.Size_t.t) =
      let msg = C_evmc.Message.of_c !@msg in
      let code = Bytes.of_c code code_size in
      let module Host = C_host (struct
        let intf = intf
        let ctx = ctx
      end) in
      let module Vm =
        Monad_lib.Vm.Make
          (struct
            include Chain_params
            let trace = false
            let debug_tstore = debug_tstore
          end)
          (Host)
      in
      let result, () = Vm.execute msg code () in
      C_evmc.Result.to_c result
    let execute =
      let execute_base = to_static_funptr execute_fn (execute_impl false) in
      let execute_debug_tstore = to_static_funptr execute_fn (execute_impl true) in
      fun debug_tstore -> if debug_tstore then execute_debug_tstore else execute_base

    let get_capabilities_impl (_vm : Vm.repr structure ptr) = Vm.Capabilities.evm1
    let get_capabilities = to_static_funptr get_capabilities_fn get_capabilities_impl

    let set_option = coerce (ptr void) (static_funptr Vm.set_option_fn) null
  end

  let make_monadml_evm debug_tstore =
    let open C_evmc.Vm in
    let vm = addr (make repr) in
    vm |-> abi_version <-@ Int64.to_int C_evmc.evmc_abi_version ;
    vm |-> name <-@ Evm_bindings.name ;
    vm |-> version <-@ Evm_bindings.version ;
    vm |-> destroy <-@ Evm_bindings.destroy ;
    vm |-> execute <-@ Evm_bindings.execute debug_tstore ;
    vm |-> get_capabilities <-@ Evm_bindings.get_capabilities ;
    vm |-> set_option <-@ Evm_bindings.set_option ;
    vm

  let monadml_evm_default = make_monadml_evm false
  let () = ignore (Root.create monadml_evm_default)
  let () =
    I.internal ~runtime_lock:false "evmc_create_monadml_evm"
      (void @-> returning (ptr C_evmc.Vm.repr))
      (fun () -> monadml_evm_default)

  let monadml_evm_debug_tstore = make_monadml_evm true
  let () = ignore (Root.create monadml_evm_debug_tstore)
  let () =
    I.internal ~runtime_lock:false "evmc_create_monadml_evm_debug_tstore"
      (void @-> returning (ptr C_evmc.Vm.repr))
      (fun () -> monadml_evm_debug_tstore)
end
