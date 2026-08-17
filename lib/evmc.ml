(** A high-level version of the {{:https://github.com/category-labs/evmc}Category Labs fork} of the
    {{:https://evmc.ethereum.org/}EVMC interface}.

    The EVMC interface is a de-facto Ethereum standard that allows EVM implementations to be written against an
    abstract interface (the EVMC host) instead of tightly integrated with an entire execution client.

    The Monad reference implementation follows the boundaries between VM and host delineated by the EVMC interface
    but diverges in two important respects.
    + High-level OCaml types are used rather than C primitive types.
    + APIs are based around explicit state passing, to allow for a purely functional implementation. *)

open Numeric
open Byte_string
open Chain.Ethereum

module Result = struct
  module StatusCode = struct
    (** EVM execution status code: [Success] or [Revert] in case of normal termination, or a descriptive
        error code in case of failure. Equivalent to
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
      | Monad_reserve_balance_violation
      | Internal_error
      | Rejected
      | Out_of_memory
      (* TODO: there is currently no Monad EVMC equivalent for this. The C++ implementation does not track
         VM error conditions with this granularity. *)
      | Create_from_delegated_eoa

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
      | Monad_reserve_balance_violation -> "Monad reserve balance violation"
      | Internal_error -> "Internal error"
      | Rejected -> "Rejected"
      | Out_of_memory -> "Out of memory"
      | Create_from_delegated_eoa -> "Create from delegated eoa"
  end

  (** Equivalent to {{:https://evmc.ethereum.org/structevmc__result.html}[evmc_result]}. *)
  type t =
    { status_code : StatusCode.t
    ; gas_left : Int64.t
    ; gas_refund : Int64.t
    ; output_data : Bytes.t
    ; create_address : Address.t }

  (** [failure error_code] constructs a result representing termination due to execution failure (but not
      deliberate termination due to a [REVERT] instruction). *)
  let failure error_code =
    assert (StatusCode.(error_code <> Success && error_code <> Revert)) ;
    { status_code = error_code
    ; gas_left = 0L
    ; gas_refund = 0L
    ; output_data = Bytes.empty
    ; create_address = Address.zero }
end

module Message = struct
  (** Equivalent to
      {{:https://evmc.ethereum.org/group__EVMC.html#gab2fa68a92a6828064a61e46060abc634}[evmc_call_kind]}. Note
      that the [EVMC_EOFCREATE] call kind is not provided. *)
  module CallKind = struct
    type t = Call | DelegateCall | CallCode | Create | Create2
  end

  (** An EVMC message represents a call to the EVM, corresponding to a contract creation or message call in
      Sections 7 and 8 respectively of the Ethereum Yellow Paper.
      Equivalent to {{:https://evmc.ethereum.org/structevmc__message.html}[evmc_message]}. *)
  type t =
    { kind : CallKind.t
    ; static : bool  (** Whether the call is static, the inverse of I_w in the Yellow Paper. *)
    ; delegated : bool  (** Represents EIP-7702 delegated calls, not the DELEGATECALL opcode *)
    ; depth : Int32.t  (** Depth of the call represented by this message. *)
    ; gas : Uint64.t
    ; recipient : Address.t
    ; sender : Address.t
    ; input_data : Bytes.t
    ; value : U256.t
    ; create2_salt : B32.t
    ; code_address : Address.t
    ; code : Bytes.t (* TODO: the Category EVMC has obsoleted this field, remove. *)
    ; memory_capacity : Int32.t  (** The remaining memory capacity for this call, see MIP-3. *) }
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
  (** The status of a storage modification, used to compute SSTORE gas cost and refund calculation. See EIP-2200
      and the definition of [C_SSTORE] in the Yellow Paper.
      Equivalent to
      {{:https://evmc.ethereum.org/group__EVMC.html#gae012fd6b8e5c23806b507c2d3e9fb1aa}[evmc_storage_status]}. *)
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

module type HOST = sig
  (** Types supporting a purely functional version of the EVMC host API. This mirrors the structure
      of {{:https://evmc.ethereum.org/structevmc__host__interface.html}[evmc_host_interface]}, replacing
      the mutable [evmc_host_context*] parameter with an explicit threaded state of abstract type [t]. *)
  type t

  val account_exists : Address.t -> t -> bool * t
  (** [account_exists addr] returns [true] if an account exists at [addr], false otherwise.
      Equivalent to
      {{:https://evmc.ethereum.org/group__EVMC.html#ga4c5464305402bf2a10d94bf2d828d82b}evmc_account_exists_fn}.
   *)

  val get_storage : Address.t -> B32.t -> t -> B32.t * t
  (** [get_storage addr key] returns the value at the storage key [key] for the account at [addr]. If the account
      does not exist or the storage key has never been written to, the value is taken to be zero.
      Equivalent to
      {{:https://evmc.ethereum.org/group__EVMC.html#ga7aff77bf67e8fad5819807b8aafff7cb}evmc_get_storage_fn}.
   *)

  val set_storage : Address.t -> B32.t -> B32.t -> t -> StorageStatus.t * t
  (** [set_storage addr key value] sets the value at the storage key [key] for the account at [addr] to the new
      value [value], returning a [StorageStatus.t] corresponding to the effect of this update on the storage
      item.
      Equivalent to
      {{:https://evmc.ethereum.org/group__EVMC.html#gaf7481ac7c3f1071d5d4d8256d0687e83}evmc_set_storage_fn}. *)

  val get_balance : Address.t -> t -> U256.t * t
  (** [get_balance addr] returns the balance of the account at [addr]. If the account does not exist, the balance
      is taken to be zero.
      Equivalent to
      {{:https://evmc.ethereum.org/group__EVMC.html#ga5208ee08734b69bb0a28793f0ecfbc48}evmc_get_balance_fn}. *)

  val get_code_size : Address.t -> t -> Uint64.t * t
  (** [get_code_size addr] returns the size in bytes of the Ethereum bytecode stored in the account at [addr].
      If the account does not exist, [get_code_size] behaves as if the code was empty.
      Equivalent to
      {{:https://evmc.ethereum.org/group__EVMC.html#ga38e37a3a70dec828829cccb461e99de2}evmc_get_code_size_fn}. *)

  val get_code_hash : Address.t -> t -> B32.t option * t
  (** [get_code_hash addr] returns the hash of the Ethereum bytecode stored in the account at [addr],
      or [None] if the account does not exist.
      Equivalent to
      {{:https://evmc.ethereum.org/group__EVMC.html#ga7971754ea6e237ffb9e9b7ab102fa16e}evmc_get_code_hash_fn}. *)

  val copy_code : Address.t -> offset:int -> size:int -> t -> Bytes.t * t
  (** [copy_code addr ~offset ~size] returns the [size] bytes of the code for the account at [addr] starting
      at offset [offset]. If the requested interval exceeds the size of the code at [addr], the result is padded
      with zeros on the right.
      Equivalent to
      {{:https://evmc.ethereum.org/group__EVMC.html#ga7dc696d1491951200ac5dc4f852a4499}evmc_copy_code_fn}. *)

  val selfdestruct : address:Address.t -> beneficiary:Address.t -> t -> bool * t
  (** [selfdestruct ~address ~beneficiary] indicates that a [SELFDESTRUCT] instruction has been called. The
      host must transfer the full balance of [address] to [beneficiary] and, if [address] was created in
      the current transaction, add it to the self-destruct list as per EIP-6780.
      [selfdestruct ~address ~beneficiary] returns [true] if and only if the account has been successfully
      added to the self-destruct list and it had not been self-destructed yet during the current transaction.
      Equivalent to
      {{:https://evmc.ethereum.org/group__EVMC.html#ga1aa9fa657b3f0de375e2f07e53b65bcc}evmc_selfdestruct_fn}. *)

  val call : Message.t -> t -> Result.t * t
  (** [call msg] performs a contract creation or message call according to YP Section 7 or 8 respectively.
      Equivalent to
      {{:https://evmc.ethereum.org/group__EVMC.html#ga54f569386b52be6eee15ca9e14ed1ef8}evmc_call_fn}. *)

  val get_tx_context : t -> TxContext.t * t
  (** [get_tx_context] returns the context for the current transaction.
      Equivalent to
      {{:https://evmc.ethereum.org/group__EVMC.html#ga7b403c029b5b9ad627ffafb8c41ac84b}evmc_get_tx_context_fn}.
   *)

  val get_block_hash : Uint64.t -> t -> B32.t option * t
  (** [get_block_hash num] returns the block hash of the block [num], or [None] if no such block is available.
      Equivalent to
      {{:https://evmc.ethereum.org/group__EVMC.html#ga97c2981658d797d3031720a54740a4b3}evmc_get_block_hash_fn}.
   *)

  val emit_log : Address.t -> data:Bytes.t -> topics:B32.t list -> t -> unit * t
  (** [emit_log addr ~data ~topics] creates a log with the specified [data] and [topics] and appends it to
      the logs emitted during the current transaction.
      Equivalent to
      {{:https://evmc.ethereum.org/group__EVMC.html#gaab96621b67d653758b3da15c2b596938}evmc_emit_log_fn}. *)

  val access_account : Address.t -> t -> [`Warm | `Cold] * t
  (** [access_account addr] adds the account [addr] to the list of accessed accounts in the current transaction,
      and returns [`Warm] if the account had previously been accessed or [`Cold] otherwise.
      Equivalent to
      {{:https://evmc.ethereum.org/group__EVMC.html#gac33551d757c3762e4cc3dd9bdfeee356}evmc_access_account_fn}.
   *)

  val access_storage : Address.t -> B32.t -> t -> [`Warm | `Cold] * t
  (** [access_storage addr key] adds the pair [(addr, key)] to the list of accessed storage slots in the current
      transaction, and returns [`Warm] if the pair had previously been accessed or [`Cold] otherwise.
      Equivalent to
      {{:https://evmc.ethereum.org/group__EVMC.html#ga8eb6233115c660f8d779eb9b132e93c5}evmc_access_storage_fn}.
   *)

  val get_transient_storage : Address.t -> B32.t -> t -> B32.t * t
  (** [get_transient_storage addr key] returns the value at the transient storage key [key] for the account at
      [addr]. If the account does not exist or the transient storage key has not been written to during this
      transaction, the value is taken to be zero.
      Equivalent to
      {{:https://evmc.ethereum.org/group__EVMC.html#gaf9d05d52083ede06470147205d695224}evmc_get_transient_storage_fn}. *)

  val set_transient_storage : Address.t -> B32.t -> B32.t -> t -> unit * t
  (** [set_transient_storage addr key value] sets the value at the transient storage key [key] for the account
      at [addr] to the new value [value].
      Equivalent to
      {{:https://evmc.ethereum.org/group__EVMC.html#gaf9d05d52083ede06470147205d695224}evmc_set_transient_storage_fn}. *)
end

(** The type of EVMC VMs over a host [H.t], broadly based on
    {{:https://evmc.ethereum.org/structevmc__vm.html}[evmc_vm]}, minus the ancillary introspection
    operations. *)
module Vm (H : sig
  type t
end) =
struct
  module type SIG = sig
    val execute : Message.t -> Bytes.t -> H.t -> Result.t * H.t
    (** [execute msg code] executes the code [code] on the input [msg].
        Equivalent to
        {{:https://evmc.ethereum.org/group__EVMC.html#gaed9a4ab5609b55c5e3272d6d37d84ff7}evmc_execute_fn}.
     *)
  end
end

(** Helper module to instantiate a host and VM over the same underlying host type.  *)
module Instantiate
    (T : sig
      type t
    end)
    (HostF : functor (Vm : Vm(T).SIG) -> HOST with type t = T.t)
    (VmF : functor (H : HOST with type t = T.t) -> Vm(T).SIG) : sig
  module Host : HOST with type t = T.t
  module Vm : Vm(T).SIG
end = struct
  module V = Vm

  module rec Host : (HOST with type t = T.t) = HostF (Vm)

  and Vm : V(T).SIG = VmF (Host)
end
