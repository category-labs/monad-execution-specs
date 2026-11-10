(** MIP-4: reserve balance introspection precompile. *)

open Chain.Ethereum
open Byte_string
open Numeric

module Make (Revision : sig
  val revision : Chain.Monad.Revision.active
end) =
struct
  let address = Reserve_balance.precompile_address

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

  let introspection (msg : Evmc.Message.t) : Evmc.Result.t State.TransactionState.M.t =
    State.TransactionState.M.(
      if Gas.(of_uint64 msg.gas < gas_dipped_into_reserve) then return Evmc.Result.(failure Out_of_gas)
      else if Bytes.length msg.input_data < 4 then return (revert "method not supported")
      else if Bytes.(sub msg.input_data 0 4 <> selector_dipped_into_reserve) then
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

  let selector_get_k = Bytes.(~@"0xee39e7a0")
  let selector_get_reserve = Bytes.(~@"0x15226b54")
  let selector_set_reserve = Bytes.(~@"0x0cbbb4f6")

  let precompile (msg : Evmc.Message.t) : Evmc.Result.t State.TransactionState.M.t =
    let open State.TransactionState.M in
    let selector = if Bytes.length msg.input_data >= 4 then Bytes.sub msg.input_data 0 4 else Bytes.empty in
    let method_info =
      match Revision.revision with
      | `Eleven ->
          if String.equal selector selector_get_k then Some (100, 4)
          else if String.equal selector selector_get_reserve then Some (25_000, 36)
          else if String.equal selector selector_set_reserve then Some (150_000, 36)
          else None
      | _ -> None
    in
    match method_info with
    | None -> introspection msg
    | Some (gas, length) -> (
        let gas = Gas.of_int gas in
        if (match msg.kind with Call -> false | _ -> true) || msg.static || msg.delegated then
          return Evmc.Result.(failure Rejected)
        else if Gas.(of_uint64 msg.gas < gas) then return Evmc.Result.(failure Out_of_gas)
        else if U256.(msg.value <> zero) || Bytes.length msg.input_data <> length then
          return Evmc.Result.(failure Precompile_failure)
        else
          let encode x = U256.(to_repr_bytes (of_uint_exn x)) in
          let success output_data =
            Evmc.Result.
              { status_code = Success
              ; gas_left = Gas.(to_uint64 (of_uint64 msg.gas - gas))
              ; gas_refund = 0L
              ; output_data
              ; create_address = Address.zero }
          in
          if String.equal selector selector_get_k then
            return (success (encode Reserve_balance.execution_consensus_delay))
          else
            let$ state = get in
            let block = state.current_block.header.number in
            if String.equal selector selector_get_reserve then
              (* ABI addresses must have twelve zero high bytes, not merely
                 fit after truncating to twenty bytes. *)
              if not (String.equal (Bytes.sub msg.input_data 4 12) (Bytes.make 12 '\x00')) then
                return Evmc.Result.(failure Precompile_failure)
              else
                let account = Address.of_bytes_exn (Bytes.sub msg.input_data 16 20) in
                let record =
                  Reserve_config.read (Reserve_balance.stored_config state.world_state account) block
                in
                return (success (encode record.settled ^ encode record.pending ^ encode record.valid_from))
            else
              let value = U256.of_bytes_be_exn (Bytes.sub msg.input_data 4 32) in
              match Reserve_balance.set_reserve_balance state.world_state block msg.sender value with
              | None -> return Evmc.Result.(failure Precompile_failure)
              | Some world_state ->
                  let$ () = put {state with world_state} in
                  return (success (encode Uint.(block + Reserve_balance.execution_consensus_delay))) )
end
