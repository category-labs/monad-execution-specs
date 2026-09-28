module Base = C_evmc_template.Types (C_evmc_generated)
include Base
open Monad_lib
open Ctypes
open Common

module Message = struct
  include Message

  type t = Evmc.Message.t
  let of_c (repr : repr structure) =
    let kind = getf repr kind in
    let flags = Unsigned.UInt32.to_int64 (getf repr flags) in
    let static = Uint64.(logand flags Flags.static <> 0L) in
    let delegated = Uint64.(logand flags Flags.delegated <> 0L) in
    let depth = getf repr depth in
    let gas = getf repr gas in
    let recipient = Address.of_c (getf repr recipient) in
    let sender = Address.of_c (getf repr sender) in
    let input_data =
      let input_data = getf repr input_data in
      let input_size = getf repr input_size in
      Bytes.of_c input_data input_size
    in
    let value = Uint256be.of_c (getf repr value) in
    let create2_salt = Bytes32.of_c (getf repr create2_salt) in
    let code_address = Address.of_c (getf repr code_address) in
    let code = Bytes.empty in
    let _memory_handle = getf repr memory_handle in
    let _memory = getf repr memory in
    let memory_capacity = Unsigned.UInt32.to_int32 (getf repr memory_capacity) in
    Evmc.Message.
      { kind
      ; static
      ; delegated
      ; code
      ; depth
      ; gas
      ; recipient
      ; sender
      ; input_data
      ; value
      ; create2_salt
      ; code_address
      ; memory_capacity }
  let to_c (msg : t) : repr structure =
    let repr = make repr in
    setf repr kind msg.kind ;
    setf repr flags
      Unsigned.UInt32.(
        of_int64
          Uint64.(
            let s = if msg.static then Flags.static else zero in
            let d = if msg.delegated then Flags.delegated else zero in
            logor s d ) ) ;
    setf repr depth msg.depth ;
    setf repr gas msg.gas ;
    setf repr recipient (Address.to_c msg.recipient) ;
    setf repr sender (Address.to_c msg.sender) ;
    let pointer, size = Bytes.to_c msg.input_data ~ownership:(Tied_to repr) in
    setf repr input_data pointer ;
    setf repr input_size size ;
    setf repr value (Uint256be.to_c msg.value) ;
    setf repr create2_salt (Bytes32.to_c msg.create2_salt) ;
    setf repr code_address (Address.to_c msg.code_address) ;
    setf repr memory_handle (coerce (ptr void) (ptr uint8_t) null) ;
    setf repr memory (coerce (ptr void) (ptr uint8_t) null) ;
    setf repr memory_capacity (Unsigned.UInt32.of_int32 msg.memory_capacity) ;
    repr
end

module Result = struct
  include Base.Result
  type t = Evmc.Result.t

  let of_c (repr : repr structure) : t =
    let status_code = getf repr status_code in
    let gas_left = getf repr gas_left in
    let gas_refund = getf repr gas_refund in
    let output_data =
      let ptr = getf repr output_data in
      let size = getf repr output_size in
      Bytes.of_c ptr size
    in
    let release = getf repr release in
    let create_address = Address.of_c (getf repr create_address) in
    let result = Evmc.Result.{status_code; gas_left; gas_refund; output_data; create_address} in
    (* We have copied the result onto an OCaml managed memory block, release the original C resources. Note
       that the EVMC specification allows release to be NULL. *)
    if not (is_null (coerce (static_funptr release_result_fn) (ptr void) release)) then
      coerce (static_funptr release_result_fn) (Foreign.funptr release_result_fn) release (addr repr) ;
    result

  (* Following the EVMC API, the output buffer of a result created by [to_c] must be kept alive until the owner
     of the result calls its release function. However, using an OCaml closure (marshalled by libffi) as the
     release function can cause segmentation faults when the C driver that consumes the results is compiled
     with Clang's function sanitizer. The required [release] callback must have a native C entry point and
     free the output buffer with [free]. It is installed before returning the result. If construction raises,
     [to_c] frees the buffer itself. *)
  let to_c ~release:release_fn (res : t) : repr structure =
    let repr = make repr in
    setf repr status_code res.status_code ;
    setf repr gas_left res.gas_left ;
    setf repr gas_refund res.gas_refund ;
    setf repr release release_fn ;
    setf repr create_address (Address.to_c res.create_address) ;
    let size = Bytes.length res.output_data in
    let data_size = Unsigned.Size_t.of_int size in
    let data = if size = 0 then null else Common.malloc data_size in
    if size <> 0 && is_null data then raise Out_of_memory ;
    try
      let data_ptr = from_voidp char data in
      Bytes.iteri (fun i c -> data_ptr +@ i <-@ c) res.output_data ;
      setf repr output_data (from_voidp uint8_t data) ;
      setf repr output_size data_size ;
      repr
    with exn ->
      (* Do not leak the malloc'd memory if an exception is thrown. *)
      let backtrace = Printexc.get_raw_backtrace () in
      Common.free data ;
      Printexc.raise_with_backtrace exn backtrace
end

module Tx_context = struct
  include Tx_context
  module Initcode = struct
    include Initcode

    type t = Evmc.TxInitcode.t
    let of_c (repr : repr structure) =
      let hash = Bytes32.of_c (getf repr hash) in
      let code = Bytes.of_c (getf repr code) (getf repr code_size) in
      Evmc.TxInitcode.{hash; code}
    let to_c (ic : t) : repr structure =
      let repr = make repr in
      setf repr hash (Bytes32.to_c ic.hash) ;
      let pointer, size = Bytes.to_c ic.code ~ownership:(Tied_to repr) in
      setf repr code pointer ; setf repr code_size size ; repr
  end

  type t = Evmc.TxContext.t

  let of_c (repr : repr structure) : t =
    let tx_gas_price = Uint256be.of_c (getf repr tx_gas_price) in
    let tx_origin = Address.of_c (getf repr tx_origin) in
    let block_coinbase = Address.of_c (getf repr block_coinbase) in
    let block_number = getf repr block_number in
    let block_timestamp = getf repr block_timestamp in
    let block_gas_limit = getf repr block_gas_limit in
    let block_prev_randao = Uint256be.of_c (getf repr block_prev_randao) in
    let chain_id = Uint256be.of_c (getf repr chain_id) in
    let block_base_fee = Uint256be.of_c (getf repr block_base_fee) in
    let blob_base_fee = Uint256be.of_c (getf repr blob_base_fee) in
    let blob_hashes =
      List.of_c
        (coerce (ptr Bytes32.repr) (ptr Bytes32.t) (getf repr blob_hashes))
        (getf repr blob_hashes_count)
    in
    let initcodes = List.of_c (getf repr initcodes) (getf repr initcodes_count) |> List.map Initcode.of_c in
    Evmc.TxContext.
      { tx_gas_price
      ; tx_origin
      ; block_coinbase
      ; block_number
      ; block_timestamp
      ; block_gas_limit
      ; block_prev_randao
      ; chain_id
      ; block_base_fee
      ; blob_base_fee
      ; blob_hashes
      ; initcodes }

  let to_c (ctx : t) : repr structure =
    let repr = make repr in
    setf repr tx_gas_price (Uint256be.to_c ctx.tx_gas_price) ;
    setf repr tx_origin (Address.to_c ctx.tx_origin) ;
    setf repr block_coinbase (Address.to_c ctx.block_coinbase) ;
    setf repr block_number ctx.block_number ;
    setf repr block_timestamp ctx.block_timestamp ;
    setf repr block_gas_limit ctx.block_gas_limit ;
    setf repr block_prev_randao (Uint256be.to_c ctx.block_prev_randao) ;
    setf repr chain_id (Uint256be.to_c ctx.chain_id) ;
    setf repr block_base_fee (Uint256be.to_c ctx.block_base_fee) ;
    setf repr blob_base_fee (Uint256be.to_c ctx.blob_base_fee) ;
    (let blob_hashes_ptr, blob_hashes_len = List.to_c Bytes32.t ctx.blob_hashes ~ownership:(Tied_to repr) in
     setf repr blob_hashes (coerce (ptr Bytes32.t) (ptr Bytes32.repr) blob_hashes_ptr) ;
     setf repr blob_hashes_count blob_hashes_len ) ;
    (let initcodes_ptr, initcodes_len =
       List.to_c Initcode.repr (List.map Initcode.to_c ctx.initcodes) ~ownership:(Tied_to repr)
     in
     setf repr initcodes initcodes_ptr ;
     setf repr initcodes_count initcodes_len ) ;
    repr
end
