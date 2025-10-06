(* EVMC interface, OCaml side *)

open Utils
open Chain.Ethereum

module Result = struct
  type status_code = Success | Failure (* | ... *)
  type t =
    { status_code : status_code
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
    { kind : [`Call]
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

    val get_transient_storage : Address.t -> Word.t t
    val set_transient_storage : Address.t -> Word.t -> unit t
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
