open Numeric
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

module State = struct
  module Chain = struct
    (** State across multiple blocks. Tracks accounts, storage, and all previously validated blocks. This
        includes the world state as per YP 4.1. *)
    type t =
      { history : Block.t list
      ; accounts : Account.t Address.Map.t (* σ[a] *)
      ; storage : U256.t U256.Map.t U256.Map.t (* σ[a]_s *) }
    [@@deriving lens {submodule = true; prefix = true}]

    include TLens

    type state = t

    let empty = {history = []; accounts = Address.Map.empty; storage = U256.Map.empty}
    type error = Invalid_transaction of Transaction.t | Invalid_block of Block.t

    module M = Monad.State (struct
      type t = state
    end)
  end

  module Transaction = struct
    (** State within a single transaction. Tracks the initial block state, any changes to its storage,
          and variables that are internal to the transaction such as the accrued substate (YP 6.1). *)
    type t =
      { initial : Chain.t
      ; state : Chain.t
      ; block : Block.t
      ; transient_storage : U256.t U256.Map.t Address.Map.t
      ; accounts_created_in_current_transaction : Address.Set.t
      ; self_destruct : Address.Set.t  (** A_s *)
      ; logs : Log.t list  (** A_l *)
      ; touched : Address.Set.t  (** A_t *)
      ; refund : U256.t  (** A_r *)
      ; accessed_addresses : Address.Set.t  (** A_a *)
      ; accessed_keys : StorageKey.Set.t  (** A_K *) }
    [@@deriving lens {submodule = true; prefix = true}]

    include TLens

    type state = t

    let make state block =
      { initial = state
      ; state
      ; block
      ; transient_storage = Address.Map.empty
      ; accounts_created_in_current_transaction = Address.Set.empty
      ; self_destruct = Address.Set.empty
      ; logs = []
      ; touched = Address.Set.empty
      ; refund = U256.zero
      ; accessed_addresses = Address.Set.empty
      ; accessed_keys = StorageKey.Set.empty }

    module M = Monad.State (struct
      type t = state
    end)
  end
end

module BlockOutput = struct
  type t
end

type validation_error = Invalid_block of Block.t | Invalid_transaction of Transaction.t
module Validation = Monad.Result (struct
  type t = validation_error
end)

type intrinsic_and_floor_gas = {intrinsic : Gas.t; floor : Gas.t}

(* YP (64) and EIP-7623 *)
let intrinsic_and_floor_gas (txn : Transaction.t) =
  let zero_bytes, nonzero_bytes =
    Bytes.fold_left
      (fun (z, nz) byte -> if byte = '\x00' then (z + 1, nz) else (z, nz + 1))
      (0, 0)
      Transaction.(data_or_initcode (call_or_create txn))
  in
  let tokens_in_calldata = zero_bytes + (4 * nonzero_bytes) in
  let calldata_gas = Gas.(~$tokens_in_calldata * tx_calldata_token_gas) in
  let calldata_floor_gas = Gas.((~$tokens_in_calldata * tx_calldata_floor_token_gas) + tx_base_gas) in
  let create_gas =
    match Transaction.call_or_create txn with
    | Call _ -> Gas.zero
    | Create {init} ->
        Gas.(tx_create_gas + (tx_initcode_gas_per_word * bytes_to_whole_words ~$(Bytes.length init)))
  in
  let transaction_gas = Gas.tx_base_gas in
  let access_list_gas =
    List.fold_left
      (fun g (access : Transaction.Access.t) ->
        Gas.(g + tx_access_list_address + (tx_access_list_storage * ~$(List.length access.storage_keys))) )
      Gas.zero (Transaction.access_list txn)
  in
  {intrinsic = Gas.(calldata_gas + create_gas + transaction_gas + access_list_gas); floor = calldata_floor_gas}

let validate_transaction (txn : Transaction.t) : (intrinsic_and_floor_gas, validation_error) Result.t =
  Result.(
    let gas_costs = intrinsic_and_floor_gas txn in

    let$ () =
      if Gas.(gas_costs.floor > txn.gas_limit || gas_costs.intrinsic > txn.gas_limit) then
        fail (Invalid_transaction txn)
      else return ()
    in

    let$ () =
      if U256.(txn.nonce >= of_uint64 Uint64.max_uint) then fail (Invalid_transaction txn) else return ()
    in

    let$ () =
      match Transaction.call_or_create txn with
      | Create {init} when Bytes.length init > 2 * Vm.max_init_code_size -> fail (Invalid_transaction txn)
      | _ -> return ()
    in

    return gas_costs )

let touch_account addr = State.Transaction.(M.update_field accessed_addresses (Address.Set.add addr))

let touch_storage addr key =
  State.Transaction.(
    M.(
      let$ () = touch_account addr in
      update_field accessed_keys (StorageKey.Set.add (addr, key)) ) )

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

module Make (Vm : sig
  val execute : Message.t -> Bytes.t -> Evmc.Result.t M.t
end) =
struct
  include M
  let account_exists addr = Option.is_some <$> !(accounts |-- Address.Map.at addr)

  let get_storage addr key =
    !(account addr |-- storage |-- U256.Map.at key |-- Option.get_or_default U256.zero)

  let set_storage addr key v =
    let$ () = account addr |-- storage |-- U256.Map.at key := Some v in
    (* TODO: make this accurate. *)
    return StorageStatus.Assigned

  let get_balance addr = !(account addr |-- balance)

  let get_code_size addr =
    let$ code = !(account addr |-- code) in
    return (Uint64.of_int (Bytes.length code))

  let get_code_hash addr =
    let$ code = !(account addr |-- code) in
    return (Crypto.keccak_256 code)

  let copy_code addr ~offset ~size =
    let$ code = !(account addr |-- code) in
    return (Bytes.sub_with_zero_padding code offset size)

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
    execute msg msg.code

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
          ; create_address = Address.zero }
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
            return {result with create_address}
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
        ; block_prev_randao = U256.zero
        ; chain_id = U256.zero
        ; block_base_fee = U256.zero
        ; blob_base_fee = U256.zero
        ; blob_hashes = []
        ; initcodes = [] }

  let get_block_hash i =
    (* This host is not backed by an actual block database, so we return the hash of i which is enough for
         testing *)
    return (Crypto.keccak_256 U256.(to_bytes_be (of_uint64 i)))

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

  let get_transient_storage _addr key =
    !(transient_storage |-- U256.Map.at key |-- Option.get_or_default U256.zero)

  let set_transient_storage _addr key value = transient_storage |-- U256.Map.at key := Some value
end
