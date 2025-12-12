(** A high-level version of the {{:https://evmc.ethereum.org/}EVMC interface}. *)

open Numeric
open Byte_string
open Chain.Ethereum

module Result = struct
  module StatusCode = struct
    (** Equivalent to
        {{:https://evmc.ethereum.org/group__EVMC.html#ga4c0be97f333c050ff45321fcaa34d920}[evmc_status_code]}. *)
    type t =
      | Success
      | Failure
      | Revert
      | Out_of_gas
      | Invalid_instruction
      | Undefined_instruction
      | Stack_overflow
      | Stack_underflow
      | Bad_jump_destination
      | Invalid_memory_access
      | Call_depth_exceeded
      | Static_mode_violation
      | Precompile_failure
      | Contract_validation_failure
      | Argument_out_of_range
      | Wasm_unreachable_instruction
      | Wasm_trap
      | Insufficient_balance
      | Internal_error
      | Rejected
      | Out_of_memory

    let to_string = function
      | Success -> "Success"
      | Failure -> "Failure"
      | Revert -> "Revert"
      | Out_of_gas -> "Out of gas"
      | Invalid_instruction -> "Invalid instruction"
      | Undefined_instruction -> "Undefined instruction"
      | Stack_overflow -> "Stack overflow"
      | Stack_underflow -> "Stack underflow"
      | Bad_jump_destination -> "Bad jump destination"
      | Invalid_memory_access -> "Invalid memory access"
      | Call_depth_exceeded -> "Call depth exceeded"
      | Static_mode_violation -> "Static memory violation"
      | Precompile_failure -> "Precompile failure"
      | Contract_validation_failure -> "Contract validation failure"
      | Argument_out_of_range -> "Argument out of range"
      | Wasm_unreachable_instruction -> "Wasm unreachable instruction"
      | Wasm_trap -> "Wasm trap"
      | Insufficient_balance -> "Insufficient balance"
      | Internal_error -> "Internal error"
      | Rejected -> "Rejected"
      | Out_of_memory -> "Out of memory"
  end

  (** Equivalent to {{:https://evmc.ethereum.org/structevmc__result.html}[evmc_result]}. *)
  type t =
    { status_code : StatusCode.t
    ; gas_left : Int64.t
    ; gas_refund : Int64.t
    ; output_data : Bytes.t
    ; create_address : Address.t }

  let failure error_code =
    assert (StatusCode.(error_code <> Success && error_code <> Revert)) ;
    { status_code = error_code
    ; gas_left = 0L
    ; gas_refund = 0L
    ; output_data = Bytes.empty
    ; create_address = Address.zero }
end

module Message = struct
  module CallKind = struct
    type t = Call | DelegateCall | CallCode | Create | Create2
  end

  (** Equivalent to {{:https://evmc.ethereum.org/structevmc__message.html}[evmc_message]}. *)
  type t =
    { kind : CallKind.t
    ; static : bool
    ; delegated : bool (* Represents EIP-7702 delegated calls, not the DELEGAECALL opcode *)
    ; depth : Int32.t
    ; gas : Uint64.t
    ; recipient : Address.t
    ; sender : Address.t
    ; input_data : Bytes.t
    ; value : U256.t
    ; create2_salt : B32.t
    ; code_address : Address.t
    ; code : Bytes.t }
end

module TxInitcode = struct
  (** Equivalent to {{:https://evmc.ethereum.org/structevmc__tx__initcode.html}[evmc_tx_initcode]}. *)
  type t = {hash : B32.t; code : Bytes.t}
end

module TxContext = struct
  (** Equivalent to {{:https://evmc.ethereum.org/structevmc__tx__context.html}[evmc_tx_context]}. *)
  type t =
    { tx_gas_price : U256.t
    ; tx_origin : Address.t
    ; block_coinbase : Address.t
    ; block_number : Uint64.t
    ; block_timestamp : Uint64.t
    ; block_gas_limit : Uint64.t
    ; block_prev_randao : U256.t
    ; chain_id : U256.t
    ; block_base_fee : U256.t
    ; blob_base_fee : U256.t
    ; blob_hashes : B32.t list
    ; initcodes : TxInitcode.t list }
end

module StorageStatus = struct
  type t =
    (* 0 -> 0 -> Z *)
    | Added
    (* X -> X -> 0 *)
    | Deleted
    (* X -> X -> Z *)
    | Modified
    (* X -> 0 -> Z *)
    | DeletedAdded
    (* X -> Y -> 0 *)
    | ModifiedDeleted
    (* X -> 0 -> X *)
    | DeletedRestored
    (* 0 -> Y -> 0 *)
    | AddedDeleted
    (* X -> Y -> X *)
    | ModifiedRestored
    (* Catch-all *)
    | Assigned
end

module Host = struct
  (** The type of monads that can provide the EVMC host API. This mirrors the structure
      of {{:https://evmc.ethereum.org/structevmc__host__interface.html}[evmc_host_interface]}, replacing
      the explicit [evmc_host_context*] parameter with a monad which may be equivalent to a
      [evmc_host_context ->] reader monad. *)
  module type SIG = sig
    include Monad.SIG
    val account_exists : Address.t -> bool t

    val get_storage : Address.t -> B32.t -> B32.t t
    val set_storage : Address.t -> B32.t -> B32.t -> StorageStatus.t t

    val get_balance : Address.t -> U256.t t

    val get_code_size : Address.t -> Uint64.t t
    val get_code_hash : Address.t -> B32.t t
    val copy_code : Address.t -> offset:int -> size:int -> Bytes.t t

    val selfdestruct : address:Address.t -> beneficiary:Address.t -> bool t

    val call : Message.t -> Result.t t

    val get_tx_context : TxContext.t t

    val get_block_hash : Uint64.t -> B32.t t

    val emit_log : Address.t -> data:Bytes.t -> topics:B32.t list -> unit t

    val access_account : Address.t -> [`Warm | `Cold] t
    val access_storage : Address.t -> B32.t -> [`Warm | `Cold] t

    val get_transient_storage : Address.t -> B32.t -> B32.t t
    val set_transient_storage : Address.t -> B32.t -> B32.t -> unit t
  end

  (* Lift a host monad through a transformer stack *)
  module Lift (MT : Monad.TRANS) (M : SIG with type 'a t = 'a MT.Inner.t) = struct
    include MT
    let account_exists acc = MT.lift (M.account_exists acc)

    let get_storage addr k = MT.lift (M.get_storage addr k)
    let set_storage addr k v = MT.lift (M.set_storage addr k v)

    let get_balance addr = MT.lift (M.get_balance addr)

    let get_code_size addr = MT.lift (M.get_code_size addr)
    let get_code_hash addr = MT.lift (M.get_code_hash addr)
    let copy_code addr ~offset ~size = MT.lift (M.copy_code addr ~offset ~size)

    let selfdestruct ~address ~beneficiary = MT.lift (M.selfdestruct ~address ~beneficiary)

    let call msg = MT.lift (M.call msg)

    let get_tx_context = MT.lift M.get_tx_context

    let get_block_hash i = MT.lift (M.get_block_hash i)

    let emit_log addr ~data ~topics = MT.lift (M.emit_log addr ~data ~topics)

    let access_account addr = MT.lift (M.access_account addr)
    let access_storage addr k = MT.lift (M.access_storage addr k)

    let get_transient_storage addr k = MT.lift (M.get_transient_storage addr k)
    let set_transient_storage addr k v = MT.lift (M.set_transient_storage addr k v)
  end
end

(** The type of EVMC VMs over monad M, broadly based on
    {{:https://evmc.ethereum.org/structevmc__vm.html}[evmc_vm]}, minus the ancilliary introspection
    operations. *)
module Vm (M : Monad.SIG) = struct
  module type SIG = sig
    val execute : Message.t -> Bytes.t -> Result.t M.t
  end
end

(** Helper module to instantiate a host and VM over the same monad.  *)
module Instantiate
    (M : Monad.SIG)
    (HostF : functor (Vm : Vm(M).SIG) -> Host.SIG with type 'a t = 'a M.t)
    (VmF : functor (Host : Host.SIG with type 'a t = 'a M.t) -> Vm(M).SIG) : sig
  module Host : Host.SIG with type 'a t = 'a M.t
  module Vm : Vm(M).SIG
end = struct
  module H = Host
  module V = Vm

  module rec Host : (H.SIG with type 'a t = 'a M.t) = HostF (Vm)

  and Vm : V(M).SIG = VmF (Host)
end
