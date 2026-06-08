(** MIP-4: reserve balance introspection precompile. *)

open Chain.Ethereum
open Byte_string
open Numeric

module Make (Revision : sig
  val revision : Chain.Monad.Revision.active
end) =
struct
  let address = Address.of_hex_string "0x1001"

  (* TODO: Currently the selector handling and the return value encoding are hard-coded. Once the Solidity ABI
     helpers are merged from the staking precompile, the code here should be updated. *)
  let selector_dipped_into_reserve = Bytes.(~@"0x3a61584e")
  let gas_dipped_into_reserve = Gas.(~$100)

  let revert (error_msg : string) : Evmc.Result.t =
    (* The error message is returned directly, it is not ABI-encoded. *)
    Evmc.Result.
      { status_code = StatusCode.Revert
      ; gas_left = 0L
      ; gas_refund = 0L
      ; output_data = error_msg
      ; create_address = Address.zero }

  let precompile (msg : Evmc.Message.t) : Evmc.Result.t State.TransactionState.M.t =
    State.TransactionState.M.(
      if Gas.(of_uint64 msg.gas < gas_dipped_into_reserve) then return Evmc.Result.(failure Out_of_gas)
      else if Bytes.length msg.input_data < 4 then return (revert "method not supported")
      else if Bytes.sub msg.input_data 0 4 <> selector_dipped_into_reserve then
        return (revert "method not supported")
      else if U256.(msg.value <> zero) then return (revert "value is nonzero")
      else if Bytes.length msg.input_data > 4 then return (revert "input is invalid")
      else
        let$ dipped = Reserve_balance.dipped_into_reserve Revision.revision in
        let output_data = U256.to_repr_bytes (if dipped then U256.one else U256.zero) in
        return
          Evmc.Result.
            { status_code = StatusCode.Success
            ; gas_left = Gas.(to_uint64 (of_uint64 msg.gas - gas_dipped_into_reserve))
            ; gas_refund = 0L
            ; output_data
            ; create_address = Address.zero } )
end
