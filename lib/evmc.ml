(* EVMC interface, OCaml side *)
open Utils
open Chain.Ethereum

module Result = struct
  module StatusCode = struct
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

  type t =
    { status_code : StatusCode.t
    ; gas_left : Int64.t
    ; gas_refund : Int64.t
    ; output_data : Bytes.t
    ; create_address : Address.t option }
end

module Flags = struct
  type t = Static | Delegated
end

module CallKind = struct
  (* EOFCreate is unsupported as of Monad V4 *)
  type t = Call | DelegateCall | CallCode | Create | Create2 | EOFCreate
end

module Message = struct
  type t =
    { kind : CallKind.t
    ; flags : Flags.t list
    ; depth : Int32.t
    ; gas : Uint64.t
    ; recipient : Address.t
    ; sender : Address.t
    ; input_data : Bytes.t
    ; value : Word.t
    ; create2_salt : Word.t
    ; code_address : Address.t
    ; code : Bytes.t }
end

module TxInitcode = struct
  type t = {hash : Word.t; code : Bytes.t}
end
module TxContext = struct
  type t =
    { tx_gas_price : Word.t
    ; tx_origin : Address.t
    ; block_coinbase : Address.t
    ; block_number : Uint64.t
    ; block_timestamp : Uint64.t
    ; block_gas_limit : Uint64.t
    ; block_prev_randao : Word.t
    ; chain_id : Word.t
    ; block_base_fee : Word.t
    ; blob_base_fee : Word.t
    ; blob_hashes : Word.t list
    ; initcodes : TxInitcode.t list }
end

module Host = struct
  module type SIG = sig
    include Monad.SIG
    val account_exists : Address.t -> bool t

    val get_storage : Address.t -> Word.t -> Word.t t
    val set_storage : Address.t -> Word.t -> Word.t -> unit t

    val get_balance : Address.t -> Word.t t

    val get_code_size : Address.t -> Word.t t
    val get_code_hash : Address.t -> Word.t t
    val copy_code : Address.t -> Bytes.t t

    val selfdestruct : address:Address.t -> beneficiary:Address.t -> bool t

    val call : Message.t -> Result.t t

    val get_tx_context : TxContext.t t

    val get_block_hash : Word.t -> Word.t t

    val emit_log : Address.t -> data:Bytes.t -> topics:Word.t list -> unit t

    val access_account : Address.t -> [`Warm | `Cold] t
    val access_storage : Address.t -> Word.t -> [`Warm | `Cold] t

    val get_transient_storage : Word.t -> Word.t t
    val set_transient_storage : Word.t -> Word.t -> unit t
  end

  (* Lift a host monad through a transformer stack *)
  module Lift (MT : Monad.TRANS) (M : SIG with type 'a t = 'a MT.Underlying.t) = struct
    include MT
    let account_exists acc = MT.lift (M.account_exists acc)

    let get_storage addr k = MT.lift (M.get_storage addr k)
    let set_storage addr k v = MT.lift (M.set_storage addr k v)

    let get_balance addr = MT.lift (M.get_balance addr)

    let get_code_size addr = MT.lift (M.get_code_size addr)
    let get_code_hash addr = MT.lift (M.get_code_hash addr)
    let copy_code addr = MT.lift (M.copy_code addr)

    let selfdestruct ~address ~beneficiary = MT.lift (M.selfdestruct ~address ~beneficiary)

    let call msg = MT.lift (M.call msg)

    let get_tx_context = MT.lift M.get_tx_context

    let get_block_hash i = MT.lift (M.get_block_hash i)

    let emit_log addr ~data ~topics = MT.lift (M.emit_log addr ~data ~topics)

    let access_account addr = MT.lift (M.access_account addr)
    let access_storage addr k = MT.lift (M.access_storage addr k)

    let get_transient_storage addr = MT.lift (M.get_transient_storage addr)
    let set_transient_storage addr k = MT.lift (M.set_transient_storage addr k)
  end
end

(* Dummy implementation *)
module Dummy (Rev : Chain.Monad.Revision.SIG) = struct
  open Utils
  open Chain.Ethereum
  open Lens
  open Lens.Infix

  module Traits = Chain.Monad.Traits (Rev)

  module Account = struct
    type t = {balance : Word.t; storage : Word.t Word.Map.t; code : Bytes.t}
    [@@deriving lens {submodule = true; prefix = true}]
    include TLens

    let empty = {balance = Word.zero; storage = Word.Map.empty; code = Bytes.empty}
  end
  open Account

  module StorageKey = struct
    module Impl = struct
      type t = Address.t * Word.t
      let compare (a1, w1) (a2, w2) =
        let c1 = Address.compare a1 a2 in
        if c1 = 0 then Word.compare w1 w2 else c1
    end
    include Impl
    module Set = Set.Make (Impl)
  end

  module AccruedSubstate = struct
    (* TODO: logs *)
    (** YP 6.1 *)
    type t =
      { self_destruct : Address.Set.t  (** A_s *)
      ; touched : Address.Set.t  (** A_t *)
      ; refund : Word.t  (** A_r *)
      ; accessed_addresses : Address.Set.t  (** A_a *)
      ; accessed_keys : StorageKey.Set.t  (** A_K *) }
    [@@deriving lens {submodule = true; prefix = true}]

    include TLens

    let empty =
      { self_destruct = Address.Set.empty
      ; touched = Address.Set.empty
      ; refund = Word.zero
      ; accessed_addresses = Address.Set.empty
      ; accessed_keys = StorageKey.Set.empty }
  end
  open AccruedSubstate

  module State = struct
    type t = {accounts : Account.t Address.Map.t; substate : AccruedSubstate.t}
    [@@deriving lens {submodule = true; prefix = true}]
    include TLens

    let empty = {accounts = Address.Map.empty; substate = AccruedSubstate.empty}
  end
  open State

  include Utils.Monad.State (State)

  let touch_account addr = update_field (substate |-- accessed_addresses) (Address.Set.add addr)

  let touch_storage addr key =
    let$ () = touch_account addr in
    update_field (substate |-- accessed_keys) (StorageKey.Set.add (addr, key))

  let account addr = accounts |-- Address.Map.at addr |-- get_or_default Account.empty

  (* EVMC *)
  let account_exists addr = Option.is_some <$> !(accounts |-- Address.Map.at addr)

  let get_storage addr key = !(account addr |-- storage |-- Word.Map.at key |-- get_or_default Word.zero)

  let set_storage addr key v = account addr |-- storage |-- Word.Map.at key := Some v

  let get_balance addr = !(account addr |-- balance)

  let get_code_size addr =
    let$ code = !(account addr |-- code) in
    return (Word.of_int (Bytes.length code))
  let get_code_hash _addr = todo ()
  let copy_code addr = !(account addr |-- code)

  let selfdestruct ~address ~beneficiary =
    Stdlib.ignore (address, beneficiary) ;
    todo ()
  let call _msg = todo ()

  let get_tx_context =
    return
      TxContext.
        { tx_gas_price = Word.zero
        ; tx_origin = Address.zero
        ; block_coinbase = Address.zero
        ; block_number = 0L
        ; block_timestamp = 0L
        ; block_gas_limit = 99999L
        ; block_prev_randao = Word.zero
        ; chain_id = Word.of_int Traits.chain_id
        ; block_base_fee = Word.zero
        ; blob_base_fee = Word.zero
        ; blob_hashes = []
        ; initcodes = [] }

  let get_block_hash _i = todo ()

  let emit_log _addr ~data ~topics =
    Stdlib.ignore (data, topics) ;
    todo ()

  let access_account addr : [`Warm | `Cold] t =
    let$ accessed = !(substate |-- accessed_addresses) in
    if Option.is_some (Address.Set.find_opt addr accessed) then return `Warm
    else
      let$ () = touch_account addr in
      return `Cold

  let access_storage addr key =
    let$ accessed = !(substate |-- accessed_keys) in
    if Option.is_some (StorageKey.Set.find_opt (addr, key) accessed) then return `Warm
    else
      let$ () = touch_storage addr key in
      return `Cold

  let get_transient_storage _addr _key = todo ()
  let set_transient_storage _addr _key _v = todo ()
end
