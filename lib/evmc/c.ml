(** C versions of the EVMC types. *)
open Numeric
open Ctypes
open Foreign
open Ocaml

(* TODO: this is not portable as it assumes that every struct is 32 bits. *)
let enum_view ~name mapping =
  let ocaml_of_c (i : Int32.t) =
    match List.find_opt (fun (index, _) -> index = i) mapping with
    | None -> failwith (Format.sprintf "Unexpected value %ld in enum %s" i name)
    | Some (_, value) -> value
  in
  let c_of_ocaml v = fst (List.find (fun (_, value) -> value = v) mapping) in
  view ~read:ocaml_of_c ~write:c_of_ocaml int32_t

module type NUMERIC = sig
  type t
  val byte_width : int
  val to_bytes_be : t -> Bytes.t
  val of_bytes_be : Bytes.t -> t
end
module Numeric_View (M : NUMERIC) = struct
  type t = M.t

  (* TODO: this is technically not right, since C cannot actually return arrays *)
  type repr = Unsigned.UInt8.t carray
  let repr : repr typ = array M.byte_width uint8_t

  let c_of_ocaml (value : M.t) : repr =
    let bytes = M.to_bytes_be value in
    let arr = CArray.make uint8_t M.byte_width in
    for i = 0 to M.byte_width - 1 do
      CArray.set arr i (Unsigned.UInt8.of_int (Char.code bytes.[i]))
    done ;
    arr

  let ocaml_of_c (bytes : repr) : M.t =
    let bytes = Bytes.init M.byte_width (fun i -> Char.chr (Unsigned.UInt8.to_int (CArray.get bytes i))) in
    M.of_bytes_be bytes

  let t = view ~write:c_of_ocaml ~read:ocaml_of_c repr

  let ptr_t =
    view ~write:(fun x -> allocate repr (c_of_ocaml x)) ~read:(fun ptr -> ocaml_of_c !@ptr) (ptr repr)
end

module Address = Numeric_View (U160)
module Bytes32 = Numeric_View (U256)
module Uint256be = Bytes32

module HostContext = struct
  type t
  let t : t structure typ = structure "evmc_host_context"
end

module Bytes = struct
  include Bytes

  let c_of_ocaml (bs : Bytes.t) =
    let size = Bytes.length bs in
    let c_size = Unsigned.Size_t.of_int size in
    let c_bytes = if size > 0 then allocate_n uint8_t ~count:size else coerce (ptr void) (ptr uint8_t) null in
    (c_bytes, c_size)

  let ocaml_of_c (buf : Unsigned.uint8 ptr) (size : Unsigned.size_t) =
    if Unsigned.Size_t.(equal size zero) then Bytes.empty
    else Bytes.init (Unsigned.Size_t.to_int size) (fun i -> Char.chr (Unsigned.UInt8.to_int !@(buf +@ i)))
end

module type REPRESENTABLE = sig
  type t
  val t : t typ
end

module List = struct
  include List

  let c_of_ocaml (type t) (t : t typ) (l : t list) : t ptr * Unsigned.size_t =
    let c_elts = Ctypes.CArray.of_list t l in
    let c_length = Unsigned.Size_t.of_int (List.length l) in
    (CArray.start c_elts, c_length)

  let ocaml_of_c (type t) (c_buf : t ptr) (c_length : Unsigned.size_t) : t list =
    if Unsigned.Size_t.(equal c_length zero) then []
    else Ctypes.CArray.(to_list (from_ptr c_buf (Unsigned.Size_t.to_int c_length)))
end

module Message = struct
  module CallKind = struct
    let mapping =
      Message.CallKind.
        [(0l, Call); (1l, DelegateCall); (2l, CallCode); (3l, Create); (4l, Create2); (5l, EOFCreate)]

    let t = enum_view ~name:"evmc_call_kind" mapping
  end

  type t = Message.t
  type repr
  let repr : repr structure typ = structure "evmc_message"
  let kind = field repr "kind" CallKind.t
  let flags = field repr "flags" uint32_t
  let depth = field repr "depth" int32_t
  let gas = field repr "gas" int64_t
  let recipient = field repr "recipient" Address.t
  let sender = field repr "sender" Address.t
  let input_data = field repr "input_data" (const (ptr uint8_t))
  let input_size = field repr "input_size" size_t
  let value = field repr "value" Uint256be.t
  let create2_salt = field repr "create2_salt" Bytes32.t
  let code_address = field repr "code_address" Address.t
  let code = field repr "code" (const (ptr uint8_t))
  let code_size = field repr "code_size" size_t
  let () = seal repr

  let c_of_ocaml (msg : Message.t) : repr structure =
    let c = make repr in
    setf c kind msg.kind ;
    setf c flags (failwith "TODO") ;
    setf c depth msg.depth ;
    setf c gas msg.gas ;
    setf c recipient msg.recipient ;
    setf c sender msg.sender ;
    (let bytes, size = Bytes.c_of_ocaml msg.input_data in
     setf c input_data bytes ; setf c input_size size ) ;
    setf c value msg.value ;
    setf c create2_salt msg.create2_salt ;
    setf c code_address msg.code_address ;
    (let bytes, size = Bytes.c_of_ocaml msg.code in
     setf c code bytes ; setf c code_size size ) ;
    c

  let ocaml_of_c (msg : repr structure) : Message.t =
    let flag_static = 1 in
    let flag_delegated = 2 in
    let flags = Unsigned.UInt32.to_int (getf msg flags) in
    Message.
      { kind = getf msg kind
      ; delegated = Int.(zero <> logand flags flag_delegated)
      ; static = Int.(zero <> logand flags flag_static)
      ; depth = getf msg depth
      ; gas = getf msg gas
      ; recipient = getf msg recipient
      ; sender = getf msg sender
      ; input_data = Bytes.ocaml_of_c (getf msg input_data) (getf msg input_size)
      ; value = getf msg value
      ; create2_salt = getf msg create2_salt
      ; code_address = getf msg code_address
      ; code = Bytes.ocaml_of_c (getf msg code) (getf msg code_size) }

  let t = view ~read:ocaml_of_c ~write:c_of_ocaml repr
end

module Result = struct
  module StatusCode = struct
    let mapping =
      Result.StatusCode.
        [ (0l, Success)
        ; (1l, Failure)
        ; (2l, Revert)
        ; (3l, Out_of_gas)
        ; (4l, Invalid_instruction)
        ; (5l, Undefined_instruction)
        ; (6l, Stack_overflow)
        ; (7l, Stack_underflow)
        ; (8l, Bad_jump_destination)
        ; (9l, Invalid_memory_access)
        ; (10l, Call_depth_exceeded)
        ; (11l, Static_mode_violation)
        ; (12l, Precompile_failure)
        ; (13l, Contract_validation_failure)
        ; (14l, Argument_out_of_range)
        ; (15l, Wasm_unreachable_instruction)
        ; (16l, Wasm_trap)
        ; (17l, Insufficient_balance)
        ; (-1l, Internal_error)
        ; (-2l, Rejected)
        ; (-3l, Out_of_memory) ]

    let t = enum_view ~name:"evmc_status_code" mapping
  end

  type t = Result.t
  type repr
  let repr : repr structure typ = structure "evmc_result"
  let status_code = field repr "status_code" StatusCode.t
  let gas_left = field repr "gas_left" int64_t
  let gas_refund = field repr "gas_refund" int64_t
  let output_data = field repr "output_data" (const (ptr uint8_t))
  let output_size = field repr "output_size" size_t
  let release = field repr "release" (funptr (ptr repr @-> returning void))
  let create_address = field repr "create_address" Address.t
  let padding = field repr "padding" (array 4 uint8_t)
  let () = seal repr

  let c_of_ocaml (res : Result.t) : repr structure =
    let c = make repr in
    setf c status_code res.status_code ;
    setf c gas_left res.gas_left ;
    setf c gas_refund res.gas_refund ;
    (let data, size = Bytes.c_of_ocaml res.output_data in
     setf c output_data data ; setf c output_size size ) ;
    setf c release (coerce (ptr void) (funptr (ptr repr @-> returning void)) null) ;
    setf c create_address (match res.create_address with None -> U160.zero | Some addr -> addr) ;
    c

  let ocaml_of_c (res : repr structure) : Result.t =
    Result.
      { status_code = getf res status_code
      ; gas_left = getf res gas_left
      ; gas_refund = getf res gas_refund
      ; output_data = Bytes.ocaml_of_c (getf res output_data) (getf res output_size)
      ; create_address =
          (let addr = getf res create_address in
           if U160.(addr = zero) then None else Some addr ) }

  let t = view ~read:ocaml_of_c ~write:c_of_ocaml repr
end

module TxInitcode = struct
  type t = TxInitcode.t
  type repr
  let repr : repr structure typ = structure "evmc_tx_initcode"
  let hash = field repr "hash" Bytes32.t
  let code = field repr "code" (const (ptr uint8_t))
  let code_size = field repr "code_size" size_t
  let () = seal repr

  let c_of_ocaml (initcode : TxInitcode.t) : repr structure =
    let c = make repr in
    setf c hash initcode.hash ;
    (let data, size = Bytes.c_of_ocaml initcode.code in
     setf c code data ; setf c code_size size ) ;
    c

  let ocaml_of_c (initcode : repr structure) : TxInitcode.t =
    TxInitcode.
      {hash = getf initcode hash; code = Bytes.ocaml_of_c (getf initcode code) (getf initcode code_size)}

  let t = view ~read:ocaml_of_c ~write:c_of_ocaml repr
end

module TxContext = struct
  type t = TxContext.t
  type repr
  let repr : repr structure typ = structure "evmc_tx_context"
  let tx_gas_price = field repr "tx_gas_price" Uint256be.t
  let tx_origin = field repr "tx_origin" Address.t
  let block_coinbase = field repr "block_coinbase" Address.t
  let block_number = field repr "block_number" int64_t
  let block_timestamp = field repr "block_timestamp" int64_t
  let block_gas_limit = field repr "block_gas_limit" int64_t
  let block_prev_randao = field repr "block_prev_randao" Uint256be.t
  let chain_id = field repr "chain_id" Uint256be.t
  let block_base_fee = field repr "block_base_fee" Uint256be.t
  let blob_base_fee = field repr "blob_base_fee" Uint256be.t
  let blob_hashes = field repr "blob_hashes" (const (ptr Bytes32.t))
  let blob_hashes_count = field repr "blob_hashes_count" size_t
  let initcodes = field repr "initcodes" (const (ptr TxInitcode.t))
  let initcodes_count = field repr "initcodes_count" size_t
  let () = seal repr

  let c_of_ocaml (tx_ctx : TxContext.t) : repr structure =
    let c = make repr in
    setf c tx_gas_price tx_ctx.tx_gas_price ;
    setf c tx_origin tx_ctx.tx_origin ;
    setf c block_coinbase tx_ctx.block_coinbase ;
    setf c block_number tx_ctx.block_number ;
    setf c block_timestamp tx_ctx.block_timestamp ;
    setf c block_gas_limit tx_ctx.block_gas_limit ;
    setf c block_prev_randao tx_ctx.block_prev_randao ;
    setf c chain_id tx_ctx.chain_id ;
    setf c block_base_fee tx_ctx.block_base_fee ;
    setf c blob_base_fee tx_ctx.blob_base_fee ;
    (let c_blob_hashes, c_blob_hashes_count = List.c_of_ocaml Bytes32.t tx_ctx.blob_hashes in
     setf c blob_hashes c_blob_hashes ;
     setf c blob_hashes_count c_blob_hashes_count ) ;
    (let c_initcodes, c_initcodes_count = List.c_of_ocaml TxInitcode.t tx_ctx.initcodes in
     setf c initcodes c_initcodes ;
     setf c initcodes_count c_initcodes_count ) ;
    c

  let ocaml_of_c (tx_ctx : repr structure) : TxContext.t =
    TxContext.
      { tx_gas_price = getf tx_ctx tx_gas_price
      ; tx_origin = getf tx_ctx tx_origin
      ; block_coinbase = getf tx_ctx block_coinbase
      ; block_number = getf tx_ctx block_number
      ; block_timestamp = getf tx_ctx block_timestamp
      ; block_gas_limit = getf tx_ctx block_gas_limit
      ; block_prev_randao = getf tx_ctx block_prev_randao
      ; chain_id = getf tx_ctx chain_id
      ; block_base_fee = getf tx_ctx block_base_fee
      ; blob_base_fee = getf tx_ctx blob_base_fee
      ; blob_hashes = List.ocaml_of_c (getf tx_ctx blob_hashes) (getf tx_ctx blob_hashes_count)
      ; initcodes = List.ocaml_of_c (getf tx_ctx initcodes) (getf tx_ctx initcodes_count) }

  let t = view ~read:ocaml_of_c ~write:c_of_ocaml repr
end

module HostInterface = struct
  type t
  let t : t structure typ = structure "evmc_host_interface"

  let foo = field t "foo" (Foreign.funptr Ctypes.(int @-> returning int))
  let account_exists =
    field t "account_exists" (funptr Ctypes.(ptr HostContext.t @-> Address.ptr_t @-> returning bool))

  let get_storage =
    field t "get_storage"
      (funptr
         Ctypes.(ptr HostContext.t @-> const Address.ptr_t @-> const Bytes32.ptr_t @-> returning Bytes32.t) )
  let set_storage =
    field t "set_storage"
      (funptr
         Ctypes.(
           ptr HostContext.t
           @-> const Address.ptr_t
           @-> const Bytes32.ptr_t
           @-> const Bytes32.ptr_t
           @-> returning void ) )

  let get_balance =
    field t "get_balance"
      (funptr Ctypes.(ptr HostContext.t @-> const Address.ptr_t @-> returning Uint256be.t))

  let get_code_size =
    field t "get_code_size" (funptr Ctypes.(ptr HostContext.t @-> const Address.ptr_t @-> returning size_t))
  let get_code_hash =
    field t "get_code_hash"
      (funptr Ctypes.(ptr HostContext.t @-> const Address.ptr_t @-> returning Bytes32.t))
  let copy_code =
    field t "copy_code"
      (funptr
         Ctypes.(
           ptr HostContext.t
           @-> const Address.ptr_t
           @-> size_t
           @-> ptr uint8_t
           @-> size_t
           @-> returning size_t ) )

  let selfdestruct =
    field t "selfdestruct"
      (funptr Ctypes.(ptr HostContext.t @-> const Address.ptr_t @-> const Address.ptr_t @-> returning bool))

  let call =
    field t "call" (funptr Ctypes.(ptr HostContext.t @-> const (ptr Message.t) @-> returning Result.t))

  let get_tx_context = field t "get_tx_context" (funptr Ctypes.(ptr HostContext.t @-> returning TxContext.t))

  let get_block_hash =
    field t "get_block_hash" (funptr Ctypes.(ptr HostContext.t @-> int64_t @-> returning Bytes32.t))

  let emit_log =
    field t "emit_log"
      (funptr
         Ctypes.(
           ptr HostContext.t
           @-> const Address.ptr_t
           @-> const (ptr uint8_t)
           @-> size_t
           @-> const (ptr Bytes32.t)
           @-> size_t
           @-> returning void ) )

  let access_status : [`Cold | `Warm] typ = enum_view ~name:"evmc_access_status" [(0l, `Cold); (1l, `Warm)]

  let access_account =
    field t "access_account"
      (funptr Ctypes.(ptr HostContext.t @-> const Address.ptr_t @-> returning access_status))
  let access_storage =
    field t "access_storage"
      (funptr
         Ctypes.(ptr HostContext.t @-> const Address.ptr_t @-> const Bytes32.ptr_t @-> returning access_status) )

  let get_transient_storage =
    field t "get_transient_storage"
      (funptr Ctypes.(ptr HostContext.t @-> const Bytes32.ptr_t @-> returning Bytes32.t))
  let set_transient_storage =
    field t "set_transient_storage"
      (funptr Ctypes.(ptr HostContext.t @-> const Bytes32.ptr_t @-> const Bytes32.ptr_t @-> returning void))
end

module Bind (M : sig
  val host_api : HostInterface.t Ctypes.structure
end) : Host.SIG = struct
  open Ctypes
  include Monad.Reader (struct
    type t = HostContext.t structure ptr
  end)

  module API = HostInterface

  let bind field =
    let$ host = read in
    return (getf M.host_api field host)

  let ( <@> ) (f : ('a -> 'b) t) (x : 'a) : 'b t = f <*> return x

  let account_exists addr = bind API.account_exists <@> addr

  let get_storage addr key = bind API.get_storage <@> addr <@> key
  let set_storage addr key value = bind API.set_storage <@> addr <@> key <@> value

  let get_balance addr = bind API.get_balance <@> addr

  let get_code_size addr =
    let$ size = bind API.get_code_size <@> addr in
    (* Conversion is necessary here as size_t does not have a fixed size *)
    return (Unsigned.Size_t.to_int64 size)
  let get_code_hash addr = bind API.get_code_hash <@> addr
  let copy_code addr =
    (* The OCaml API expects copy_code to return the entire contract code, so we have to fetch
       the code size and copy the entire contents into a temporary buffer here *)
    let$ size = Int64.to_int <$> get_code_size addr in
    let buffer = CArray.make uint8_t size in
    let$ size =
      bind API.copy_code
      <@> addr
      <@> Unsigned.Size_t.zero
      <@> CArray.start buffer
      <@> Unsigned.Size_t.of_int size
    in
    return
      (Bytes.init (Unsigned.Size_t.to_int size) (fun i ->
           Char.chr (Unsigned.UInt8.to_int (CArray.get buffer i)) ) )

  let selfdestruct ~address ~beneficiary = bind API.selfdestruct <@> address <@> beneficiary

  let call msg =
    let msg_ptr = allocate Message.t msg in
    bind API.call <@> msg_ptr

  let get_tx_context = bind API.get_tx_context

  let get_block_hash index = bind API.get_block_hash <@> index

  let emit_log address ~data ~topics =
    let c_data = allocate_n uint8_t ~count:(Bytes.length data) in
    let c_data_size = Unsigned.Size_t.of_int (Bytes.length data) in
    let c_topics = allocate_n Bytes32.t ~count:(List.length topics) in
    let c_topics_size = Unsigned.Size_t.of_int (List.length topics) in
    bind API.emit_log <@> address <@> c_data <@> c_data_size <@> c_topics <@> c_topics_size

  let access_account addr = bind API.access_account <@> addr
  let access_storage addr key = bind API.access_storage <@> addr <@> key

  let get_transient_storage key = bind API.get_transient_storage <@> key
  let set_transient_storage key value = bind API.set_transient_storage <@> key <@> value
end
