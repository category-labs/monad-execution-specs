open Byte_string
open State
open Abi
open Type

module Type = Type
module Abi = Abi

(* Contracts are parameterized over a contract-specific error type, which has to provide at least an entry for
   an input decoding failure.
   The parameterization here is awkward because the Monad precompiles may return observable error messages that
   are not consistent. The staking precompile returns the raw string "invalid input" on (some) input parsing
   failures, but the reserve balance precompile returns "input is invalid".
 *)
module Make (Params : sig
  val address : Address.t
  type error
  val encode_error : error -> Bytes.t

  (* We would like to constrain error to be a supertype of a general "ABI error" type, but there is no
     mechanism for adding subtype constraints to a type in a functor argument. *)
  val value_non_zero : error
  val decode_error : Type.decode_error -> error
end) =
struct
  module Storage = Storage.Make (Params)
  module Type = Type
  module Abi = Abi

  open Params
  type 'a or_error = ('a, error) result

  module Function = struct
    type ('i, 'o) abi_fn = sender:Address.t -> value:U256.t -> 'i -> 'o or_error TransactionState.M.t
    type raw_fn = sender:Address.t -> value:U256.t -> Bytes.t -> Bytes.t or_error TransactionState.M.t

    type ('i, 'o) fn = Abi of ('i, 'o) abi_fn | Raw of raw_fn

    (* A few contract functions in the Staking precompile use their own input decoding conventions that differ
       from the mostly Solidity-compliant scheme in type.ml. To represent these, we allow for a class of "raw"
       functions that take input and output directly as raw bytes. *)
    type ('i, 'o) impl =
      {signature : ('i, 'o) Signature.t; gas_cost : Gas.t; payable : bool; impl : ('i, 'o) fn}

    let make
        (name : string)
        ?(payable = false)
        ~(input : 'i Tuple.t tup)
        ~(output : 'o typ)
        ~gas_cost
        (fn : ('i Tuple.t, 'o) abi_fn) =
      let signature = Signature.make name ~input ~output in
      {signature; payable; gas_cost; impl = Abi fn}

    let make_raw
        (name : string) ?(payable = false) ~(input : 'i Tuple.t tup) ~(output : 'o typ) ~gas_cost (fn : raw_fn)
        =
      let signature = Signature.make name ~input ~output in
      {signature; payable; gas_cost; impl = Raw fn}

    type t = Pack : ('i, 'o) impl -> t

    (* Monad precompiles revert with an error message on failure. All gas is consumed. *)
    let revert err : Evmc.Result.t TransactionState.M.t =
      TransactionState.M.return
        Evmc.Result.
          { status_code = StatusCode.Revert
          ; gas_left = 0L
          ; gas_refund = 0L
          ; output_data = encode_error err
          ; create_address = Address.zero }

    (** Low-level function call: invoke a smart contract function from an EVMC message, get an EVMC result.
        Returns an error directly if gas is insufficient, if a non-payable function is invoked with a nonzero
        value, or if input decoding fails.
        * On insufficient gas, returns a standard EVMC.Out_of_gas result.
        * On a decoding error or a non-payable nonzero value error, returns an EVMC.Revert error with the error
          encoded in the message's return data. The encoding is contract-specific.
     *)
    let send_message (Pack fn : t) (msg : Evmc.Message.t) : Evmc.Result.t TransactionState.M.t =
      let open TransactionState.M in
      let input = msg.input_data in
      let gas = Gas.of_uint64 msg.gas in
      if Gas.(gas < fn.gas_cost) then return (Evmc.Result.failure Out_of_gas)
      else
        let sender = msg.sender in
        let value = msg.value in
        if U256.(value <> zero) && not fn.payable then revert value_non_zero
        else
          let$ (result : _ or_error) =
            match fn.impl with
            | Raw raw_fn -> raw_fn ~sender ~value msg.input_data
            | Abi abi_fn -> (
              match dec_bytes (Tuple fn.signature.input) input with
              | Error err -> return (Error (decode_error err))
              | Ok inputs ->
                  let$ (output : _ or_error) = abi_fn ~sender ~value inputs in
                  return (Result.map (enc_bytes fn.signature.output) output) )
          in
          match result with
          | Ok output_data ->
              return
                Evmc.Result.
                  { status_code = StatusCode.Success
                  ; gas_left = Gas.(to_uint64 (gas - fn.gas_cost))
                  ; gas_refund = 0L
                  ; output_data
                  ; create_address = Address.zero }
          | Error err -> revert err
  end

  module Impl : sig
    type t = private {functions : Function.t Selector.Map.t; fallback : Function.t}
    val make : Function.t list -> fallback:Function.t -> t
  end = struct
    type t = {functions : Function.t Selector.Map.t; fallback : Function.t}
    let make (functions : Function.t list) ~(fallback : Function.t) : t =
      { functions =
          Selector.Map.of_list
            List.(map (function Function.Pack fn as f -> (fn.signature.selector, f)) functions)
      ; fallback }
  end
  include Impl

  (** Dispatch an EVMC message to one of the available functions. If no function matches, [contract.fallback]
      is used. Note that [contract.fallback] does not receive a copy of the input data. This is because Solidity
      fallback functions circumvent the usual ABI encoding/decoding process, so we'd need an ad-hoc mechanism
      to pass the input through unencoded and unpadded. Since by and large all Monad precompile fallbacks
      simply revert with an error, the added complexity is not necessary. *)
  let dispatch ({functions; fallback} : t) (msg : Evmc.Message.t) : Evmc.Result.t TransactionState.M.t =
    if Bytes.length msg.input_data < 4 then Function.send_message fallback {msg with input_data = Bytes.empty}
    else
      let selector = Selector.sub msg.input_data 0 in
      match Selector.Map.find_opt selector functions with
      | Some fn ->
          let input_data = String.sub msg.input_data 4 (String.length msg.input_data - 4) in
          Function.send_message fn {msg with input_data}
      | None -> Function.send_message fallback {msg with input_data = Bytes.empty}

  (** A generic state+error monad. Specific smart contracts will likely want to extend this with whatever
      primitives they use. *)
  module M = struct
    module St = Monad.State (TransactionState)
    module Err = Monad.Result (struct
      type t = error
    end)
    module ErrSt = Err.Trans (St)
    include St.Lift (ErrSt) (St)
    include ErrSt
    include TransactionState.TLens

    let account ?(keep_empty = false) = TransactionState.account ~keep_empty

    let ( !$ ) (l : 'a Storage.Loc.t) : 'a t = !(Storage.Loc.lens l)
    let ( $= ) (l : 'a Storage.Loc.t) (v : 'a) : unit t = Storage.Loc.lens l := v

    let emit_event ev indexed_params non_indexed_params =
      let log = Abi.Event.to_log ev Params.address indexed_params non_indexed_params in
      update_field logs (fun logs -> log :: logs)
  end
end
