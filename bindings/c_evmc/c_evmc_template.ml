open Ctypes
open Common

(** evmc_bytes32 *)
module Bytes32 = Byte_array (struct
  include Monad_lib.Byte_string.B32
  let name = "evmc_bytes32"
end)

(** evmc_uint256be *)
module Uint256be = struct
  include Byte_array (struct
    include Monad_lib.Byte_string.B32
    let name = "evmc_uint256be"
  end)

  type t = Monad_lib.Numeric.U256.t
  let of_c (repr : repr structure) : t = Monad_lib.Numeric.U256.of_repr (of_c repr)
  let to_c (x : t) : repr structure = to_c (Monad_lib.Numeric.U256.to_repr x)
  let t = view ~read:of_c ~write:to_c repr
end

(** evmc_address *)
module Address = Byte_array (struct
  include Monad_lib.Chain.Ethereum.Address
  let name = "evmc_address"
end)

module Types (F : Ctypes.TYPE) = struct
  open F
  module Evmc = Monad_lib.Evmc

  module Bytes32 = struct
    include Bytes32
    let repr = F.lift_typ repr
  end

  module Uint256be = struct
    include Uint256be
    let repr = F.lift_typ repr
  end

  module Address = struct
    include Address
    let repr = F.lift_typ repr
  end

  let evmc_abi_version = constant "EVMC_ABI_VERSION" int64_t

  module Message = struct
    module Call_kind = struct
      (** evmc_call_kind *)
      let t : Evmc.Message.CallKind.t typ =
        let call = constant "EVMC_CALL" int64_t in
        let delegatecall = constant "EVMC_DELEGATECALL" int64_t in
        let callcode = constant "EVMC_CALLCODE" int64_t in
        let create = constant "EVMC_CREATE" int64_t in
        let create2 = constant "EVMC_CREATE2" int64_t in

        let open Evmc.Message.CallKind in
        enum "evmc_call_kind"
          [ (Call, call)
          ; (DelegateCall, delegatecall)
          ; (CallCode, callcode)
          ; (Create, create)
          ; (Create2, create2) ]
    end

    module Flags = struct
      (** evmc_flags *)

      let static = constant "EVMC_STATIC" int64_t
      let delegated = constant "EVMC_DELEGATED" int64_t

      let t : [`Delegated | `Static] typ = enum "evmc_flags" [(`Static, static); (`Delegated, delegated)]
    end

    (** evmc_message *)
    type repr

    let repr : repr structure typ = structure "evmc_message"
    let kind = field repr "kind" Call_kind.t
    let flags = field repr "flags" uint32_t
    let depth = field repr "depth" int32_t
    let gas = field repr "gas" int64_t
    let recipient = field repr "recipient" Address.repr
    let sender = field repr "sender" Address.repr
    let input_data = field repr "input_data" (ptr uint8_t)
    let input_size = field repr "input_size" size_t
    let value = field repr "value" Uint256be.repr
    let create2_salt = field repr "create2_salt" Bytes32.repr
    let code_address = field repr "code_address" Address.repr
    let memory_handle = field repr "memory_handle" (ptr uint8_t)
    let memory = field repr "memory" (ptr uint8_t)
    let memory_capacity = field repr "memory_capacity" uint32_t
    let () = seal repr
  end

  module Result = struct
    module Status_code = struct
      (** evmc_status_code *)
      let t : Evmc.Result.StatusCode.t typ =
        let success = constant "EVMC_SUCCESS" int64_t in
        let failure = constant "EVMC_FAILURE" int64_t in
        let revert = constant "EVMC_REVERT" int64_t in
        let out_of_gas = constant "EVMC_OUT_OF_GAS" int64_t in
        let invalid_instruction = constant "EVMC_INVALID_INSTRUCTION" int64_t in
        let undefined_instruction = constant "EVMC_UNDEFINED_INSTRUCTION" int64_t in
        let stack_overflow = constant "EVMC_STACK_OVERFLOW" int64_t in
        let stack_underflow = constant "EVMC_STACK_UNDERFLOW" int64_t in
        let bad_jump_destination = constant "EVMC_BAD_JUMP_DESTINATION" int64_t in
        let invalid_memory_access = constant "EVMC_INVALID_MEMORY_ACCESS" int64_t in
        let call_depth_exceeded = constant "EVMC_CALL_DEPTH_EXCEEDED" int64_t in
        let static_mode_violation = constant "EVMC_STATIC_MODE_VIOLATION" int64_t in
        let precompile_failure = constant "EVMC_PRECOMPILE_FAILURE" int64_t in
        let contract_validation_failure = constant "EVMC_CONTRACT_VALIDATION_FAILURE" int64_t in
        let argument_out_of_range = constant "EVMC_ARGUMENT_OUT_OF_RANGE" int64_t in
        let wasm_unreachable_instruction = constant "EVMC_WASM_UNREACHABLE_INSTRUCTION" int64_t in
        let wasm_trap = constant "EVMC_WASM_TRAP" int64_t in
        let insufficient_balance = constant "EVMC_INSUFFICIENT_BALANCE" int64_t in
        let monad_reserve_balance_violation = constant "EVMC_MONAD_RESERVE_BALANCE_VIOLATION" int64_t in
        let internal_error = constant "EVMC_INTERNAL_ERROR" int64_t in
        let rejected = constant "EVMC_REJECTED" int64_t in
        let out_of_memory = constant "EVMC_OUT_OF_MEMORY" int64_t in
        let open Evmc.Result.StatusCode in
        enum "evmc_status_code"
          [ (Success, success)
          ; (Failure, failure)
          ; (Revert, revert)
          ; (Out_of_gas, out_of_gas)
          ; (Invalid_instruction, invalid_instruction)
          ; (Undefined_instruction, undefined_instruction)
          ; (Stack_overflow, stack_overflow)
          ; (Stack_underflow, stack_underflow)
          ; (Bad_jump_destination, bad_jump_destination)
          ; (Invalid_memory_access, invalid_memory_access)
          ; (Call_depth_exceeded, call_depth_exceeded)
          ; (Static_mode_violation, static_mode_violation)
          ; (Precompile_failure, precompile_failure)
          ; (Contract_validation_failure, contract_validation_failure)
          ; (Argument_out_of_range, argument_out_of_range)
          ; (Wasm_unreachable_instruction, wasm_unreachable_instruction)
          ; (Wasm_trap, wasm_trap)
          ; (Insufficient_balance, insufficient_balance)
          ; (Monad_reserve_balance_violation, monad_reserve_balance_violation)
          ; (Internal_error, internal_error)
          ; (Rejected, rejected)
          ; (Out_of_memory, out_of_memory)
          ; (* evmc.h does not define a specific error code for this case. *)
            (Create_from_delegated_eoa, failure) ]
    end

    (** evmc_result *)
    type repr

    let repr : repr structure typ = structure "evmc_result"

    let release_result_fn = ptr repr @-> returning void

    let status_code = field repr "status_code" Status_code.t
    let gas_left = field repr "gas_left" int64_t
    let gas_refund = field repr "gas_refund" int64_t
    let output_data = field repr "output_data" (ptr uint8_t)
    let output_size = field repr "output_size" size_t
    let release = field repr "release" (static_funptr release_result_fn)
    let create_address = field repr "create_address" Address.repr

    (* We use a uint32_t here instead of an array of 4 uint8_t. *)
    let padding = field repr "padding" uint32_t

    let () = seal repr
  end

  module Tx_context = struct
    module Initcode = struct
      (** evmc_tx_initcode *)
      type repr

      let repr : repr structure typ = structure "evmc_tx_initcode"
      let hash = field repr "hash" Bytes32.repr
      let code = field repr "code" (ptr uint8_t)
      let code_size = field repr "code_size" size_t
      let () = seal repr
    end

    (** evmc_tx_context *)
    type repr

    let repr : repr structure typ = structure "evmc_tx_context"
    let tx_gas_price = field repr "tx_gas_price" Uint256be.repr
    let tx_origin = field repr "tx_origin" Address.repr
    let block_coinbase = field repr "block_coinbase" Address.repr
    let block_number = field repr "block_number" int64_t
    let block_timestamp = field repr "block_timestamp" int64_t
    let block_gas_limit = field repr "block_gas_limit" int64_t
    let block_prev_randao = field repr "block_prev_randao" Uint256be.repr
    let chain_id = field repr "chain_id" Uint256be.repr
    let block_base_fee = field repr "block_base_fee" Uint256be.repr
    let blob_base_fee = field repr "blob_base_fee" Uint256be.repr
    let blob_hashes = field repr "blob_hashes" (ptr Bytes32.repr)
    let blob_hashes_count = field repr "blob_hashes_count" size_t
    let initcodes = field repr "initcodes" (ptr Initcode.repr)
    let initcodes_count = field repr "initcodes_count" size_t
    let () = seal repr
  end

  module Storage_status = struct
    (** evmc_storage_status *)
    let t : Evmc.StorageStatus.t typ =
      let assigned = constant "EVMC_STORAGE_ASSIGNED" int64_t in
      let added = constant "EVMC_STORAGE_ADDED" int64_t in
      let deleted = constant "EVMC_STORAGE_DELETED" int64_t in
      let modified = constant "EVMC_STORAGE_MODIFIED" int64_t in
      let deleted_added = constant "EVMC_STORAGE_DELETED_ADDED" int64_t in
      let modified_deleted = constant "EVMC_STORAGE_MODIFIED_DELETED" int64_t in
      let deleted_restored = constant "EVMC_STORAGE_DELETED_RESTORED" int64_t in
      let added_deleted = constant "EVMC_STORAGE_ADDED_DELETED" int64_t in
      let modified_restored = constant "EVMC_STORAGE_MODIFIED_RESTORED" int64_t in
      let open Evmc.StorageStatus in
      enum "evmc_storage_status"
        [ (Assigned, assigned)
        ; (Added, added)
        ; (Deleted, deleted)
        ; (Modified, modified)
        ; (DeletedAdded, deleted_added)
        ; (ModifiedDeleted, modified_deleted)
        ; (DeletedRestored, deleted_restored)
        ; (AddedDeleted, added_deleted)
        ; (ModifiedRestored, modified_restored) ]
  end

  module Host_context = struct
    (** evmc_host_context *)
    type repr

    let repr : repr structure typ = structure "evmc_host_context"
  end

  module Host_interface = struct
    (** evmc_get_tx_context_fn *)
    let get_tx_context_fn = ptr Host_context.repr @-> returning (ptr Tx_context.repr)

    (** evmc_get_block_hash_fn *)
    let get_block_hash_fn = ptr Host_context.repr @-> int64_t @-> returning Bytes32.repr

    (** evmc_access_status *)
    let access_status : [`Cold | `Warm] typ =
      let cold = constant "EVMC_ACCESS_COLD" int64_t in
      let warm = constant "EVMC_ACCESS_WARM" int64_t in
      enum "evmc_access_status" [(`Cold, cold); (`Warm, warm)]

    (** evmc_account_exists_fn *)
    let account_exists_fn = ptr Host_context.repr @-> ptr Address.repr @-> returning bool

    (** evmc_get_storage_fn *)
    let get_storage_fn =
      ptr Host_context.repr @-> ptr Address.repr @-> ptr Bytes32.repr @-> returning Bytes32.repr

    (** evmc_get_transient_storage_fn *)
    let get_transient_storage_fn =
      ptr Host_context.repr @-> ptr Address.repr @-> ptr Bytes32.repr @-> returning Bytes32.repr

    (** evmc_set_storage_fn *)
    let set_storage_fn =
      ptr Host_context.repr
      @-> ptr Address.repr
      @-> ptr Bytes32.repr
      @-> ptr Bytes32.repr
      @-> returning Storage_status.t

    (** evmc_set_transient_storage_fn *)
    let set_transient_storage_fn =
      ptr Host_context.repr @-> ptr Address.repr @-> ptr Bytes32.repr @-> ptr Bytes32.repr @-> returning void

    (** evmc_get_balance_fn *)
    let get_balance_fn = ptr Host_context.repr @-> ptr Address.repr @-> returning Uint256be.repr

    (** evmc_get_code_size_fn *)
    let get_code_size_fn = ptr Host_context.repr @-> ptr Address.repr @-> returning size_t

    (** evmc_get_code_hash_fn *)
    let get_code_hash_fn = ptr Host_context.repr @-> ptr Address.repr @-> returning Bytes32.repr

    (** evmc_copy_code_fn *)
    let copy_code_fn =
      ptr Host_context.repr @-> ptr Address.repr @-> size_t @-> ptr uint8_t @-> size_t @-> returning size_t

    (** evmc_selfdestruct_fn *)
    let selfdestruct_fn = ptr Host_context.repr @-> ptr Address.repr @-> ptr Address.repr @-> returning bool

    (** evmc_emit_log_fn *)
    let emit_log_fn =
      ptr Host_context.repr
      @-> ptr Address.repr
      @-> ptr uint8_t
      @-> size_t
      @-> ptr Bytes32.repr
      @-> size_t
      @-> returning void

    (** evmc_access_account_fn *)
    let access_account_fn = ptr Host_context.repr @-> ptr Address.repr @-> returning access_status

    (** evmc_access_storage_fn *)
    let access_storage_fn =
      ptr Host_context.repr @-> ptr Address.repr @-> ptr Bytes32.repr @-> returning access_status

    (** evmc_call_fn *)
    let call_fn = ptr Host_context.repr @-> ptr Message.repr @-> returning Result.repr

    (** evmc_host_interface *)
    type repr

    let repr : repr structure typ = structure "evmc_host_interface"
    let account_exists = field repr "account_exists" (static_funptr account_exists_fn)
    let get_storage = field repr "get_storage" (static_funptr get_storage_fn)
    let set_storage = field repr "set_storage" (static_funptr set_storage_fn)
    let get_balance = field repr "get_balance" (static_funptr get_balance_fn)
    let get_code_size = field repr "get_code_size" (static_funptr get_code_size_fn)
    let get_code_hash = field repr "get_code_hash" (static_funptr get_code_hash_fn)
    let copy_code = field repr "copy_code" (static_funptr copy_code_fn)
    let selfdestruct = field repr "selfdestruct" (static_funptr selfdestruct_fn)
    let call = field repr "call" (static_funptr call_fn)
    let get_tx_context = field repr "get_tx_context" (static_funptr get_tx_context_fn)
    let get_block_hash = field repr "get_block_hash" (static_funptr get_block_hash_fn)
    let emit_log = field repr "emit_log" (static_funptr emit_log_fn)
    let access_account = field repr "access_account" (static_funptr access_account_fn)
    let access_storage = field repr "access_storage" (static_funptr access_storage_fn)
    let get_transient_storage = field repr "get_transient_storage" (static_funptr get_transient_storage_fn)
    let set_transient_storage = field repr "set_transient_storage" (static_funptr set_transient_storage_fn)
    let () = seal repr
  end

  module Vm = struct
    (** evmc_set_option_result *)
    let set_option_result : [`Success | `InvalidName | `InvalidValue] typ =
      let success = constant "EVMC_SET_OPTION_SUCCESS" int64_t in
      let invalid_name = constant "EVMC_SET_OPTION_INVALID_NAME" int64_t in
      let invalid_value = constant "EVMC_SET_OPTION_INVALID_VALUE" int64_t in
      enum "evmc_set_option_result"
        [(`Success, success); (`InvalidName, invalid_name); (`InvalidValue, invalid_value)]

    (** evmc_revision *)
    let revision = int (* TODO: this should represent a Monad revision. *)

    (** evmc_vm *)
    type repr

    let repr : repr structure typ = structure "evmc_vm"

    (** evmc_destroy_fn *)
    let destroy_fn = ptr repr @-> returning void

    (** evmc_execute_fn *)
    let execute_fn =
      ptr repr
      @-> ptr Host_interface.repr
      @-> ptr Host_context.repr
      @-> revision
      @-> ptr Message.repr
      @-> ptr uint8_t
      @-> size_t
      @-> returning Result.repr

    module Capabilities = struct
      let evm1 = constant "EVMC_CAPABILITY_EVM1" uint32_t
      let ewasm = constant "EVMC_CAPABILITY_EWASM" uint32_t
      let precompiles = constant "EVMC_CAPABILITY_PRECOMPILES" uint32_t
    end

    (** evmc_get_capabilities_fn *)
    let get_capabilities_fn = ptr repr @-> returning uint32_t

    (** evmc_set_option_fn *)
    let set_option_fn = ptr repr @-> string @-> string @-> returning set_option_result

    let abi_version = field repr "abi_version" int
    let name = field repr "name" string
    let version = field repr "version" string
    let destroy = field repr "destroy" (static_funptr destroy_fn)
    let execute = field repr "execute" (static_funptr execute_fn)
    let get_capabilities = field repr "get_capabilities" (static_funptr get_capabilities_fn)
    let set_option = field repr "set_option" (static_funptr set_option_fn)
    let () = seal repr
  end
end
