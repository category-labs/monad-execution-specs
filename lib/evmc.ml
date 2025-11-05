(** A high-level version of the {{:https://evmc.ethereum.org/}EVMC interface}. *)

open Numeric
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
    ; create_address : Address.t option }
end

module CallKind = struct
  type t = Call | DelegateCall | CallCode | Create | Create2
end

module Message = struct
  (** Equivalent to {{:https://evmc.ethereum.org/structevmc__message.html}[evmc_message]}. *)
  type t =
    { kind : CallKind.t
    ; static : bool
    ; delegated : bool (* Represents EIP-7702 delegated calls, not the DELEGATECALL opcode *)
    ; depth : int
    ; gas : Uint64.t
    ; recipient : Address.t
    ; sender : Address.t
    ; input_data : Bytes.t
    ; value : U256.t
    ; create2_salt : U256.t
    ; code_address : Address.t
    ; code : Bytes.t }
end

module TxInitcode = struct
  (** Equivalent to {{:https://evmc.ethereum.org/structevmc__tx__initcode.html}[evmc_tx_initcode]}. *)
  type t = {hash : U256.t; code : Bytes.t}
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
    ; block_prev_randao : Address.t
    ; chain_id : U256.t
    ; block_base_fee : U256.t
    ; blob_base_fee : U256.t
    ; blob_hashes : U256.t list
    ; initcodes : TxInitcode.t list }
end

module Host = struct
  (** The type of monads that can provide the EVMC host API. This mirrors the structure
      of {{:https://evmc.ethereum.org/structevmc__host__interface.html}[evmc_host_interface]}, replacing
      the explicit [evmc_host_context*] parameter with a monad which may be equivalent to a
      [evmc_host_context ->] reader monad. *)
  module type SIG = sig
    include Monad.SIG
    val account_exists : Address.t -> bool t

    val get_storage : Address.t -> U256.t -> U256.t t
    val set_storage : Address.t -> U256.t -> U256.t -> unit t

    val get_balance : Address.t -> U256.t t

    val get_code_size : Address.t -> U256.t t
    val get_code_hash : Address.t -> U256.t t
    val copy_code : Address.t -> Bytes.t t

    val selfdestruct : address:Address.t -> beneficiary:Address.t -> bool t

    val call : Message.t -> Result.t t

    val get_tx_context : TxContext.t t

    val get_block_hash : U256.t -> U256.t t

    val emit_log : Address.t -> data:Bytes.t -> topics:U256.t list -> unit t

    val access_account : Address.t -> [`Warm | `Cold] t
    val access_storage : Address.t -> U256.t -> [`Warm | `Cold] t

    val get_transient_storage : U256.t -> U256.t t
    val set_transient_storage : U256.t -> U256.t -> unit t
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

(** A dummy OCaml implementation for testing, backed by a simple mapping of accounts to storage. Does not
    use a MPT or store any cross-transaction state. *)
module DummyHost (Params : sig
  val chain_id : U256.t
end) =
struct
  open Chain.Ethereum
  open Lens.Infix

  module Account = struct
    type t = {balance : U256.t; storage : U256.t U256.Map.t; code : Bytes.t; nonce : Uint.t}
    [@@deriving lens {submodule = true; prefix = true}]
    include TLens

    let empty = {balance = U256.zero; storage = U256.Map.empty; code = Bytes.empty; nonce = Uint.zero}
  end
  open Account

  module StorageKey = struct
    module Impl = struct
      type t = Address.t * U256.t
      let compare (a1, w1) (a2, w2) =
        let c1 = Address.compare a1 a2 in
        if c1 = 0 then U256.compare w1 w2 else c1
    end
    include Impl
    module Set = Set.Make (Impl)
  end

  module Log = struct
    type t = {address : Address.t; topics : U256.t list; data : Bytes.t}
    [@@deriving lens {submodule = true; prefix = true}]

    include TLens
  end

  module AccruedSubstate = struct
    (** YP 6.1. *)
    type t =
      { self_destruct : Address.Set.t  (** A_s *)
      ; logs : Log.t list (* A_l *)
      ; touched : Address.Set.t  (** A_t *)
      ; refund : U256.t  (** A_r *)
      ; accessed_addresses : Address.Set.t  (** A_a *)
      ; accessed_keys : StorageKey.Set.t  (** A_K *) }
    [@@deriving lens {submodule = true; prefix = true}]

    include TLens

    let empty =
      { self_destruct = Address.Set.empty
      ; logs = []
      ; touched = Address.Set.empty
      ; refund = U256.zero
      ; accessed_addresses = Address.Set.empty
      ; accessed_keys = StorageKey.Set.empty }
  end
  open AccruedSubstate

  module State = struct
    type t =
      { accounts : Account.t Address.Map.t
      ; substate : AccruedSubstate.t
      ; transient_storage : U256.t U256.Map.t
      ; accounts_created_in_current_transaction : Address.Set.t (* Needed for EIP-6780 *) }
    [@@deriving lens {submodule = true; prefix = true}]
    include TLens

    let empty =
      { accounts = Address.Map.empty
      ; substate = AccruedSubstate.empty
      ; transient_storage = U256.Map.empty
      ; accounts_created_in_current_transaction = Address.Set.empty }
  end
  open State

  module M = Monad.State (State)
  include M

  let touch_account addr = M.update_field (substate |-- accessed_addresses) (Address.Set.add addr)

  let touch_storage addr key =
    M.(
      let$ () = touch_account addr in
      update_field (substate |-- accessed_keys) (StorageKey.Set.add (addr, key)) )

  let account addr = accounts |-- Address.Map.at addr |-- Option.get_or_default Account.empty

  let move_ether sender recipient amount =
    let$ () =
      update_field
        (account sender |-- balance)
        (fun eth ->
          (* TODO: check this assertion on the host side. *)
          assert (U256.(eth >= amount)) ;
          U256.(eth - amount) )
    in
    update_field (account recipient |-- balance) (fun eth -> U256.(eth + amount))

  let should_transfer (msg : Message.t) =
    U256.(msg.value > zero)
    && (match msg.kind with Call | CallCode | Create | Create2 -> true | DelegateCall -> false)
    && not msg.static

  (* YP (95) *)
  let address_for ~sender ~create2_salt ~code =
    let$ nonce = !(account sender |-- nonce) in
    return
      (Address.of_u256_truncating
         (Crypto.keccak_256
            ( match create2_salt with
            | None ->
                (* TODO: correct this once RLP is in place *)
                Address.to_bytes_be sender ^ Uint.to_bytes_be nonce
            | Some salt ->
                Bytes.make 1 '\xff'
                ^ Address.to_bytes_be sender
                ^ U256.to_bytes_be salt
                ^ U256.to_bytes_be (Crypto.keccak_256 code) ) ) )

  (** EVMC host interface.
    Note this is parameterized over the VM implementation. In practice, this means the EVMC host and the
    VM module are mutually recursive.
   *)
  module Make (Vm : Vm(M).SIG) : Host.SIG with type 'a t = 'a M.t = struct
    include M
    let account_exists addr = Option.is_some <$> !(accounts |-- Address.Map.at addr)

    let get_storage addr key =
      !(account addr |-- storage |-- U256.Map.at key |-- Option.get_or_default U256.zero)

    let set_storage addr key v = account addr |-- storage |-- U256.Map.at key := Some v

    let get_balance addr = !(account addr |-- balance)

    let get_code_size addr =
      let$ code = !(account addr |-- code) in
      return (U256.of_int (Bytes.length code))

    let get_code_hash addr =
      let$ code = !(account addr |-- code) in
      return (Crypto.keccak_256 code)

    let copy_code addr = !(account addr |-- code)

    let selfdestruct ~address ~beneficiary =
      let$ account_balance = !(account address |-- balance) in
      let$ () = move_ether address beneficiary account_balance in

      let$ created_in_current_tx = Address.Set.mem address <$> !accounts_created_in_current_transaction in
      if created_in_current_tx then
        (* Delete the account as per EIP-6780 *)
        let$ alive_before_selfdestruct = account_exists address in
        let$ () = accounts |-- Address.Map.at address := None in
        return alive_before_selfdestruct
      else return false

    let process_call (msg : Message.t) =
      let$ () = when_ (should_transfer msg) (move_ether msg.sender msg.recipient msg.value) in
      (* TODO: check whether it's a precompile *)
      Vm.execute msg msg.code

    let process_create (msg : Message.t) =
      let$ create_address =
        (* Note that we use the sender nonce _before_ increasing it *)
        address_for ~sender:msg.sender
          ~create2_salt:(if msg.kind = Create2 then Some msg.create2_salt else None)
          ~code:msg.code
      in
      let$ pre_existent_account = !(account create_address) in
      if Uint.(pre_existent_account.nonce <> zero) || pre_existent_account.code <> Bytes.empty then
        (* EIP-684 *)
        return
          Result.
            { status_code = Result.StatusCode.Contract_validation_failure
            ; gas_left = 0L
            ; gas_refund = 0L
            ; output_data = Bytes.empty
            ; create_address = None }
      else
        let$ () =
          update_field accounts_created_in_current_transaction (fun addresses ->
              Address.Set.add create_address addresses )
        in
        let$ () = account create_address |-- storage := U256.Map.empty in
        let$ () = account create_address |-- nonce := Uint.one in

        (* Ether, if any, is transferred by process_call *)
        let$ result : Result.t = process_call msg in
        match result.status_code with
        | Success ->
            let contract_code = result.output_data in
            let contract_length = Bytes.length contract_code in
            let contract_code_gas = Uint.(of_int contract_length * Gas.code_deposit_per_byte) in
            if
              (contract_length = 0 && contract_code.[0] = '\xef')
              || Uint.(contract_code_gas > of_int64 result.gas_left)
            then
              return
                { result with
                  gas_left = Int64.zero
                ; output_data = Bytes.empty
                ; status_code =
                    Result.StatusCode.(
                      if contract_code.[0] = '\xef' then Contract_validation_failure else Out_of_gas ) }
            else
              let$ () = account create_address |-- code := contract_code in
              return {result with create_address = Some create_address}
        | _ -> return result

    let call (msg : Message.t) =
      let$ initial_state = get in
      let$ result =
        match msg.kind with
        | Call | DelegateCall | CallCode -> process_call msg
        | Create | Create2 -> process_create msg
      in
      let$ () = when_ (result.status_code <> Success) (put initial_state) in
      return result

    let get_tx_context =
      return
        TxContext.
          { tx_gas_price = U256.zero
          ; tx_origin = Address.zero
          ; block_coinbase = Address.zero
          ; block_number = 0L
          ; block_timestamp = 0L
          ; block_gas_limit = 99999L
          ; block_prev_randao = Address.zero
          ; chain_id = Params.chain_id
          ; block_base_fee = U256.zero
          ; blob_base_fee = U256.zero
          ; blob_hashes = []
          ; initcodes = [] }

    let get_block_hash i =
      (* This host is not backed by an actual block database, so we return the hash of i which is enough for
         testing *)
      return (Crypto.keccak_256 (U256.to_bytes_be i))

    let emit_log address ~(data : Bytes.t) ~(topics : U256.t list) =
      let log : Log.t = {address; topics; data} in
      update_field (substate |-- logs) (fun logs -> log :: logs)

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

    let get_transient_storage key =
      !(transient_storage |-- U256.Map.at key |-- Option.get_or_default U256.zero)

    let set_transient_storage key value = transient_storage |-- U256.Map.at key := Some value
  end
end
