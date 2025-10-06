open Utils

(* EVMC interface, OCaml side *)
module Ethereum = struct
  module Address : sig
    type t
    val max_t : t
    val to_word : t -> Word.t
    val of_word : Word.t -> t option
    val of_word_masking : Word.t -> t
  end = struct
    type t = Word.t
    let max_t : Word.t = Word.of_string "0xffffffffffffffffffffffffffffffffffffffff"
    let to_word (x : t) = x
    let of_word (x : Word.t) : t option = if Word.(x > max_t) then None else Some x
    let of_word_masking (x : Word.t) : t = Word.(logand max_t x)
  end
  module Revision = struct
    type t = Berlin | Cancun | Prague (* | etc *)
  end

  module Block = struct
    module Header = struct
      type t
    end
  end
end

module Evmc = struct
  open Ethereum

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

      val get_tx_context : TxContext.t t

      val access_account : Address.t -> [`Warm | `Cold] t
    end

    (* Lift a host monad through a transformer stack *)
    module Lift (MT : Monad.TRANS) (M : SIG with type 'a t = 'a MT.Underlying.t) = struct
      include MT
      let account_exists acc = MT.lift (M.account_exists acc)

      let get_storage addr k = MT.lift (M.get_storage addr k)
      let set_storage addr k v = MT.lift (M.set_storage addr k v)

      let get_balance addr = MT.lift (M.get_balance addr)
      let get_tx_context = MT.lift M.get_tx_context

      let access_account addr = MT.lift (M.access_account addr)
    end
  end
end

module Monad = struct
  module Revision = struct
    type t = Zero | One | Two | Three | Four
    module type SIG = sig
      val rev : t
    end
  end
end

module Traits (Rev : Monad.Revision.SIG) = struct
  let monad_rev = Rev.rev
  let evm_rev =
    if Monad.Revision.(monad_rev >= Four) then Ethereum.Revision.Prague else Ethereum.Revision.Cancun

  let monad_pricing_version = if Monad.Revision.(monad_rev >= Four) then 1 else 0

  type cold_costs = {cold_account_cost : Uint64.t; cold_storage_cost : Uint64.t}
  let cold_costs =
    if monad_pricing_version >= 1 then {cold_account_cost = 10000L; cold_storage_cost = 8000L}
    else {cold_account_cost = 2500L; cold_storage_cost = 2000L}

  let chain_id = 10143 (* testnet *)
end
