open Numeric
open Byte_string
open Lens.Infix
open Fast_lens

module Memory : sig
  type t
  val empty : t

  val read_block_at : U256.t -> U256.t -> t -> Bytes.t
  val read_word_at : U256.t -> t -> U256.t

  val write_block_at : U256.t -> Bytes.t -> t -> t
  val write_word_at : U256.t -> U256.t -> t -> t
  val write_byte_at : U256.t -> char -> t -> t

  val active_words : t -> Uint.t (* μ_i *)

  val extend_to : start:U256.t -> size_bytes:U256.t -> t -> t

  (* For debugging purposes *)
  val dump : t -> unit
end = struct
  type t =
    {contents : char U256.Map.t (* Corresponds to μ_m *); active_bytes : Uint.t (* Corresponds to μ_i * 32 *)}

  (** Check that the index start + size - 1 does not overflow U256.t. *)
  let u256_overflow_check start size_bytes =
    assert (U256.in_range Z.(U256.to_z start + U256.to_z size_bytes - one))

  (** Check that the index start + size - 1 does not exceed the active bytes. Memory must be extended
     by a call to [extend_to] beforehand. *)
  let active_bytes_overflow_check mem start size_bytes =
    assert (Uint.(mem.active_bytes >= U256.(to_uint start) + U256.(to_uint size_bytes)))

  let read_block_at start size (mem : t) =
    if U256.(size = zero) then Bytes.empty
    else (
      u256_overflow_check start size ;
      active_bytes_overflow_check mem start size ;
      let size = match U256.to_int_opt size with None -> assert false | Some sz -> sz in
      Bytes.init size (fun byte_i ->
          U256.Map.find_opt U256.(start + ~$byte_i) mem.contents |> Option.value ~default:'\x00' ) )

  let read_word_at pos (mem : t) = read_block_at pos U256.(~$32) mem |> U256.Repr.of_bytes_exn |> U256.of_repr

  let write_block_at (pos : U256.t) (bytes : Bytes.t) (mem : t) =
    let size = U256.of_int (Bytes.length bytes) in
    if U256.(size = zero) then mem
    else (
      u256_overflow_check pos size ;
      active_bytes_overflow_check mem pos size ;
      let contents =
        Seq.take (Bytes.length bytes) (Seq.ints 0)
        |> Seq.map (fun i -> (U256.(pos + ~$i), bytes.[i]))
        |> fun entries -> U256.Map.add_seq entries mem.contents
      in
      {mem with contents} )

  let write_word_at pos w = U256.to_repr w |> U256.Repr.to_bytes |> write_block_at pos

  let write_byte_at pos b (mem : t) = write_block_at pos (Bytes.make 1 b) mem

  let empty = {contents = U256.Map.empty; active_bytes = Uint.zero}

  let active_words mem = Uint.bytes_to_whole_words mem.active_bytes

  let extend_to ~start ~size_bytes mem =
    if U256.(size_bytes = zero) then mem
    else
      (* Round up to whole words. *)
      let active_words = Uint.(bytes_to_whole_words (U256.to_uint start + U256.to_uint size_bytes)) in
      let active_bytes = Uint.(max mem.active_bytes (active_words * ~$32)) in
      {mem with active_bytes}

  let dump mem =
    (* Write one word at a time *)
    let rec loop pos =
      if Uint.(pos < mem.active_bytes) then (
        Format.printf "%s: %s\n" (Uint.to_hex_string pos)
          (Bytes.to_hex_string (read_block_at (U256.of_uint_exn pos) U256.(~$32) mem)) ;
        loop Uint.(pos + ~$32) )
    in
    loop Uint.zero
end

module MachineState = struct
  (* YP 9.4.1 *)
  type t =
    { gas : Uint.t (* μ_g *)
    ; pc : U256.t (* μ_pc *)
    ; memory : Memory.t (* μ_m, μ_i *)
    ; stack_depth : int
    ; stack : U256.t list (* μ_s *)
    ; output_buffer : Bytes.t (* μ_o *)
    ; gas_refund : Integer.t
          (* A_r *)
          (* Gas refund is not part of machine state as per YP, but EVMC boundaries are split oddly: though
               most of the information in the Accrued Substate (accessed accounts, logs) is tracked by the
               EVMC host, refunds specifically must be tracked by an EVMC-compliant interpreter. *)
    }
  [@@deriving lens {submodule = true; prefix = true}]
  include TLens

  let initial =
    { gas = Uint.zero
    ; pc = U256.zero
    ; memory = Memory.empty
    ; stack_depth = 0
    ; stack = []
    ; output_buffer = Bytes.empty
    ; gas_refund = Integer.zero }
end

module ExecutionEnvironment = struct
  open Chain.Ethereum

  module ExecutionBlockHeader = struct
    (* The Yellow Paper has an Ethereum block header as part of the execution (I_H), but the EVMC context
         does not give us the full block header information, only those fields required for executing EVM
         bytecode. Otherwise, this is as YP 4.4 with the addition of the chain ID β, which is an ambient
         parameter in the Yellow Paper but is integrated as part of the block environment in the Ethereum
         executable spec. *)
    type t =
      { coinbase : Address.t (* H_c *)
      ; number : U256.t (* H_i *)
      ; timestamp : U256.t (* H_s *)
      ; gas_limit : U256.t (* H_l *)
      ; prev_randao : U256.t (* H_a *)
      ; base_fee : U256.t (* H_f *)
      ; chain_id : U256.t (* β *) }
    [@@deriving lens {submodule = true; prefix = true}]
    include TLens

    let of_tx_context (ctx : Evmc.TxContext.t) : t =
      { coinbase = ctx.block_coinbase
      ; number = U256.of_uint64 ctx.block_number
      ; timestamp = U256.of_uint64 ctx.block_timestamp
      ; gas_limit = U256.of_uint64 ctx.block_gas_limit
      ; prev_randao = ctx.block_prev_randao
      ; base_fee = ctx.block_base_fee
      ; chain_id = ctx.chain_id }

    let empty =
      { coinbase = Address.zero
      ; number = U256.zero
      ; timestamp = U256.zero
      ; gas_limit = U256.zero
      ; prev_randao = U256.zero
      ; base_fee = U256.zero
      ; chain_id = U256.zero }
  end
  include ExecutionBlockHeader

  (* YP 9.3 *)
  type t =
    { address : Address.t (* I_a *)
    ; origin : Address.t (* I_o *)
    ; price : U256.t (* I_p *)
    ; data : Bytes.t (* I_d *)
    ; sender : Address.t (* I_s *)
    ; value : U256.t (* I_v *)
    ; bytecode : Bytes.t (* I_b *)
    ; header : ExecutionBlockHeader.t (* I_H *)
    ; depth : int (* I_e *)
    ; write_permission : bool (* I_w *)
    ; blob_versioned_hashes : B32.t list (* EIP-4844 *)
    ; blob_base_fee : U256.t (* EIP-7516 *) }
  [@@deriving lens {submodule = true; prefix = true}]
  include TLens

  let make (ctx : Evmc.TxContext.t) (msg : Evmc.Message.t) (code : Bytes.t) : t =
    { address = msg.recipient
    ; origin = ctx.tx_origin
    ; price = ctx.tx_gas_price
    ; data = msg.input_data
    ; sender = msg.sender
    ; value = msg.value
    ; bytecode = code
    ; header = ExecutionBlockHeader.of_tx_context ctx
    ; depth = Int32.to_int msg.depth
    ; write_permission = not msg.static
    ; blob_versioned_hashes = ctx.blob_hashes
    ; blob_base_fee = ctx.blob_base_fee }

  let empty =
    { address = Address.zero
    ; origin = Address.zero
    ; price = U256.zero
    ; data = ""
    ; sender = Address.zero
    ; value = U256.zero
    ; bytecode = ""
    ; header = ExecutionBlockHeader.empty
    ; depth = 0
    ; write_permission = false
    ; blob_versioned_hashes = []
    ; blob_base_fee = U256.zero }
end

module Context = struct
  type t =
    { execution_environment : ExecutionEnvironment.t (* I *)
    ; machine_state : MachineState.t (* μ *)
    ; jump_destinations : U256.Set.t (* D(c) *)
    ; initial_storage : U256.t U256.Map.t
          (* Cached initial values of storage cells modified in the transaction, to compute sstore costs *) }
  [@@deriving lens {submodule = true; prefix = true}]
  include TLens

  let valid_jump_destinations code =
    let rec loop i valid_destinations =
      if i >= Bytes.length code then valid_destinations
      else
        match code.[i] with
        | '\x5b' -> loop (i + 1) U256.(Set.add ~$i valid_destinations)
        | '\x60' .. '\x7f' as opcode ->
            let push_bytes = Char.code opcode - 0x60 + 1 in
            loop (i + 1 + push_bytes) valid_destinations
        | _ -> loop (i + 1) valid_destinations
    in
    loop 0 U256.Set.empty

  let make (ctx : Evmc.TxContext.t) (msg : Evmc.Message.t) (code : Bytes.t) : t =
    { execution_environment = ExecutionEnvironment.make ctx msg code
    ; machine_state = {MachineState.initial with gas = Uint.of_uint64 msg.gas}
    ; jump_destinations = valid_jump_destinations code
    ; initial_storage = U256.Map.empty }

  let empty =
    { execution_environment = ExecutionEnvironment.empty
    ; machine_state = MachineState.initial
    ; jump_destinations = U256.Set.empty
    ; initial_storage = U256.Map.empty }
end

let max_stack_depth = 1024

(* Monad §TODO: maximum contract code size is larger than Ethereum. *)
let max_code_size = 128 * 1024
let max_init_code_size = 2 * max_code_size

module Make
    (Params : sig
      val trace : bool
    end)
    (Host : Evmc.Host.SIG) =
struct
  open MachineState
  open ExecutionEnvironment
  open Context

  let trace ?(print = Params.trace) msg =
    if print then (
      Format.print_string (msg ()) ;
      Format.print_flush () )
    else ()

  module Ethereum = Chain.Ethereum
  module Address = Ethereum.Address

  module St = Monad.State (Context)
  module StatusCode = Evmc.Result.StatusCode
  module Err = Monad.Result (Evmc.Result.StatusCode)

  module M = struct
    module StHost = St.Trans (Host)
    module ErrStHost = Err.Trans (StHost)

    include St.Lift (ErrStHost) (StHost)
    include ErrStHost

    module HostAPI = struct
      module Base = Evmc.Host.Lift (ErrStHost) (Evmc.Host.Lift (StHost) (Host))

      let host_trace ?print msg = trace ?print (fun () -> Format.sprintf "[OCaml] Host call: %s\n" (msg ()))

      (* TODO: trace other API calls. *)
      let account_exists addr =
        host_trace (fun () -> Format.sprintf "account_exists %s" (Address.to_short_hex_string addr)) ;
        Base.account_exists addr

      let get_storage addr key =
        host_trace (fun () ->
            Format.sprintf "get_storage %s %s" (Address.to_short_hex_string addr)
              (B32.to_short_hex_string key) ) ;
        Base.get_storage addr key

      let set_storage addr key v =
        host_trace (fun () ->
            Format.sprintf "set_storage %s %s %s" (Address.to_short_hex_string addr)
              (B32.to_short_hex_string key) (B32.to_short_hex_string v) ) ;
        Base.set_storage addr key v

      let get_balance addr =
        host_trace (fun () -> Format.sprintf "get_balance %s" (Address.to_short_hex_string addr)) ;
        Base.get_balance addr

      let access_account addr =
        host_trace (fun () -> Format.sprintf "access_account %s" (Address.to_short_hex_string addr)) ;
        Base.access_account addr

      let access_storage addr key =
        host_trace (fun () ->
            Format.sprintf "access_storage %s %s" (Address.to_short_hex_string addr)
              (B32.to_short_hex_string key) ) ;
        Base.access_storage addr key

      let get_code_size addr =
        host_trace (fun () -> Format.sprintf "get_code_size %s" (Address.to_short_hex_string addr)) ;
        Base.get_code_size addr

      let get_code_hash addr =
        host_trace (fun () -> Format.sprintf "get_code_hash %s" (Address.to_short_hex_string addr)) ;
        Base.get_code_hash addr

      let copy_code addr ~offset ~size =
        host_trace (fun () ->
            Format.sprintf "copy_code %s %d %d" (Address.to_short_hex_string addr) offset size ) ;
        Base.copy_code addr ~offset ~size

      let get_block_hash id =
        host_trace (fun () -> Format.sprintf "get_block_hash %Ld" id) ;
        Base.get_block_hash id

      let call (msg : Evmc.Message.t) =
        host_trace (fun () ->
            Format.sprintf "call to %s (gas = %Ld)" (Address.to_short_hex_string msg.recipient) msg.gas ) ;
        let$ result = Base.call msg in
        trace (fun () ->
            Format.sprintf "\tReturned %s\n" (Evmc.Result.StatusCode.to_string result.status_code) ) ;
        return result

      let selfdestruct ~address ~beneficiary =
        host_trace (fun () ->
            Format.sprintf "selfdestruct ~address:%s ~beneficiary:%s"
              (Address.to_short_hex_string address)
              (Address.to_short_hex_string beneficiary) ) ;
        Base.selfdestruct ~address ~beneficiary

      let emit_log addr ~data ~topics =
        host_trace (fun () ->
            Format.sprintf "emit_log %s %s [%s]" (Address.to_short_hex_string addr)
              (Bytes.to_short_hex_string data)
              (List.fold_left
                 (fun acc topic -> Format.sprintf "%s, %s" acc (B32.to_short_hex_string topic))
                 "" topics ) ) ;
        Base.emit_log addr ~data ~topics

      let get_transient_storage addr key =
        host_trace (fun () ->
            Format.sprintf "get_transient_storage %s %s" (Address.to_short_hex_string addr)
              (B32.to_short_hex_string key) ) ;
        Base.get_transient_storage addr key

      let set_transient_storage addr key v =
        host_trace (fun () ->
            Format.sprintf "set_transient_storage %s %s %s" (Address.to_short_hex_string addr)
              (B32.to_short_hex_string key) (B32.to_short_hex_string v) ) ;
        Base.set_transient_storage addr key v
    end
  end
  open M

  let spend (amount : Uint.t) =
    let$ state = get in
    let gas_remaining = state.machine_state.gas in
    if Uint.(gas_remaining < amount) then fail Out_of_gas
    else put (state.^(machine_state |-- gas) <- Uint.(gas_remaining - amount))

  let check_write_permissions =
    let$ can_write = !(execution_environment |-- write_permission) in
    if can_write then return () else fail Static_mode_violation

  let check_jump_destination (destination : U256.t) =
    let$ valid_destinations = !jump_destinations in
    if U256.Set.mem destination valid_destinations then return () else fail Bad_jump_destination

  let self : Address.t M.t = !(execution_environment |-- address)

  let push (x : U256.t) : unit M.t =
    let$ state = get in
    if state.machine_state.stack_depth >= max_stack_depth then fail Stack_overflow
    else
      put
        { state with
          machine_state =
            { state.machine_state with
              stack_depth = state.machine_state.stack_depth + 1
            ; stack = x :: state.machine_state.stack } }

  let pop : U256.t M.t =
    let$ state = get in
    match state.machine_state.stack with
    | [] -> fail Stack_underflow
    | hd :: tl ->
        let$ () =
          put
            { state with
              machine_state =
                {state.machine_state with stack = tl; stack_depth = state.machine_state.stack_depth - 1} }
        in
        return hd

  let finish_execution : bool M.t = return false
  let update_pc_and_continue (f : U256.t -> U256.t) : bool M.t =
    update_field (machine_state |-- pc) f >> return true
  let increase_pc_and_continue : bool M.t = update_pc_and_continue U256.(( + ) one)

  type opcode_impl = bool M.t

  (* General undefined opcode *)
  let undefined : opcode_impl = fail Undefined_instruction

  (* Designated invalid opcode 0xfe *)
  let invalid : opcode_impl = fail Invalid_instruction

  let stop =
    (* Stack *)
    (* Gas *)
    (* Operation *)
    (* PC *)
    finish_execution

  let add =
    (* Stack *)
    let$ x = pop in
    let$ y = pop in

    (* Gas *)
    let$ () = spend Gas.very_low in

    (* Operation *)
    let$ () = push U256.(x + y) in

    (* PC *)
    increase_pc_and_continue

  let mul =
    (* Stack *)
    let$ x = pop in
    let$ y = pop in

    (* Gas *)
    let$ () = spend Gas.low in

    (* Operation *)
    let$ () = push U256.(x * y) in

    (* PC *)
    increase_pc_and_continue

  let sub =
    (* Stack *)
    let$ x = pop in
    let$ y = pop in

    (* Gas *)
    let$ () = spend Gas.very_low in

    (* Operation *)
    let$ () = push U256.(x - y) in

    (* PC *)
    increase_pc_and_continue

  let udiv =
    (* Stack *)
    let$ dividend = pop in
    let$ divisor = pop in

    (* Gas *)
    let$ () = spend Gas.low in

    (* Operation **)
    let$ () = push U256.(if divisor = zero then zero else dividend / divisor) in

    (* PC *)
    increase_pc_and_continue

  let sdiv =
    (* Stack *)
    let$ dividend = U256.as_signed <$> pop in
    let$ divisor = U256.as_signed <$> pop in

    (* Gas *)
    let$ () = spend Gas.low in

    (* Operation *)
    let$ () = push I256.(as_unsigned (if divisor = zero then zero else dividend / divisor)) in

    (* PC *)
    increase_pc_and_continue

  let umod =
    (* Stack *)
    let$ x = pop in
    let$ y = pop in

    (* Gas *)
    let$ () = spend Gas.low in

    (* Operation *)
    let$ () = push U256.(if y = zero then zero else modulo x y) in

    (* PC *)
    increase_pc_and_continue

  let smod =
    (* Stack *)
    let$ x = U256.as_signed <$> pop in
    let$ y = U256.as_signed <$> pop in

    (* Gas *)
    let$ () = spend Gas.low in

    (* Operation *)
    let$ () = push I256.(as_unsigned (if y = zero then zero else modulo x y)) in

    (* PC *)
    increase_pc_and_continue

  let addmod =
    (* Stack *)
    let$ x = pop in
    let$ y = pop in
    let$ m = pop in

    (* Gas *)
    let$ () = spend Gas.mid in

    (* Operation *)
    let$ () = push U256.(if m = zero then zero else addmod x y m) in

    (* PC *)
    increase_pc_and_continue

  let mulmod =
    (* Stack *)
    let$ x = pop in
    let$ y = pop in
    let$ m = pop in

    (* Gas *)
    let$ () = spend Gas.mid in

    (* Operation *)
    let$ () = push U256.(if m = zero then zero else mulmod x y m) in

    (* PC *)
    increase_pc_and_continue

  let exp =
    (* Stack *)
    let$ base = pop in
    let$ exponent = pop in

    (* Gas *)
    let exponent_bytes = Uint.of_int (U256.significant_bytes exponent) in
    let$ () = spend Gas.(exp_base_cost + (exp_cost_per_byte * exponent_bytes)) in

    (* Operation *)
    let$ () = push U256.(exp base exponent) in

    (* PC *)
    increase_pc_and_continue

  let signextend =
    (* Stack *)
    let$ byte_index = pop in
    let$ x = pop in

    (* Gas *)
    let$ () = spend Gas.low in

    (* Operation *)
    let$ () =
      push
        U256.(
          match to_int_opt byte_index with
          | Some i when Stdlib.(i < 32) -> I256.as_unsigned (sign_extend i x)
          | Some _ | None -> x )
    in

    (* PC *)
    increase_pc_and_continue

  let lt =
    (* Stack *)
    let$ x = pop in
    let$ y = pop in

    (* Gas *)
    let$ () = spend Gas.very_low in

    (* Operation *)
    let$ () = push U256.(of_bool (x < y)) in

    (* PC *)
    increase_pc_and_continue

  let gt =
    (* Stack *)
    let$ x = pop in
    let$ y = pop in

    (* Gas *)
    let$ () = spend Gas.very_low in

    (* Operation *)
    let$ () = push U256.(of_bool (x > y)) in

    (* PC *)
    increase_pc_and_continue

  let slt =
    (* Stack *)
    let$ x = U256.as_signed <$> pop in
    let$ y = U256.as_signed <$> pop in

    (* Gas *)
    let$ () = spend Gas.very_low in

    (* Operation *)
    let$ () = push (U256.of_bool (x < y)) in

    (* PC *)
    increase_pc_and_continue

  let sgt =
    (* Stack *)
    let$ x = U256.as_signed <$> pop in
    let$ y = U256.as_signed <$> pop in

    (* Gas *)
    let$ () = spend Gas.very_low in

    (* Operation *)
    let$ () = push (U256.of_bool (x > y)) in

    (* PC *)
    increase_pc_and_continue

  let eq =
    (* Stack *)
    let$ x = pop in
    let$ y = pop in

    (* Gas *)
    let$ () = spend Gas.very_low in

    (* Operation *)
    let$ () = push U256.(of_bool (x = y)) in

    (* PC *)
    increase_pc_and_continue

  let is_zero =
    (* Stack *)
    let$ x = pop in

    (* Gas *)
    let$ () = spend Gas.very_low in

    (* Operation *)
    let$ () = push U256.(of_bool (x = zero)) in

    (* PC *)
    increase_pc_and_continue

  let bitwise_and =
    (* Stack *)
    let$ x = pop in
    let$ y = pop in

    (* Gas *)
    let$ () = spend Gas.very_low in

    (* Operation *)
    let$ () = push U256.(logand x y) in

    (* PC *)
    increase_pc_and_continue

  let bitwise_or =
    (* Stack *)
    let$ x = pop in
    let$ y = pop in

    (* Gas *)
    let$ () = spend Gas.very_low in

    (* Operation *)
    let$ () = push U256.(logor x y) in

    (* PC *)
    increase_pc_and_continue

  let bitwise_xor =
    (* Stack *)
    let$ x = pop in
    let$ y = pop in

    (* Gas *)
    let$ () = spend Gas.very_low in

    (* Operation *)
    let$ () = push U256.(logxor x y) in

    (* PC *)
    increase_pc_and_continue

  let bitwise_not =
    (* Stack *)
    let$ x = pop in

    (* Gas *)
    let$ () = spend Gas.very_low in

    (* Operation *)
    let$ () = push U256.(lognot x) in

    (* PC *)
    increase_pc_and_continue

  let byte =
    (* Stack *)
    let$ index_be = pop in
    let$ x = pop in

    (* Gas *)
    let$ () = spend Gas.very_low in

    (* Operation *)
    let$ () =
      push
        ( match U256.to_int_opt index_be with
        | Some index_be when index_be < 32 ->
            let index_le = 31 - index_be in
            U256.(of_byte (byte ~index_le x))
        | _ -> U256.zero )
    in

    (* PC *)
    increase_pc_and_continue

  let logical_shift_opcode_impl shift_fn =
    (* Stack *)
    let$ shift_amount = pop in
    let$ value = pop in

    (* Gas *)
    let$ () = spend Gas.very_low in

    (* Operation *)
    let shifted =
      U256.(
        match to_int_opt shift_amount with
        | None -> U256.zero
        | Some s when Stdlib.(s >= 256) -> U256.zero
        | Some s -> shift_fn value s )
    in
    let$ () = push shifted in

    (* PC *)
    increase_pc_and_continue

  let shl = logical_shift_opcode_impl U256.shift_left
  let shr = logical_shift_opcode_impl U256.shift_right

  let sar =
    (* Stack *)
    let$ shift_amount = pop in
    let$ value = U256.as_signed <$> pop in

    (* Gas *)
    let$ () = spend Gas.very_low in

    (* Operation *)
    let full_shift = I256.(if value < zero then ~$(-1) else zero) in
    let shifted =
      match U256.to_int_opt shift_amount with
      | None -> full_shift
      | Some s when Stdlib.(s >= 256) -> full_shift
      | Some s -> I256.shift_right value s
    in
    let$ () = push (I256.as_unsigned shifted) in

    (* PC *)
    increase_pc_and_continue

  let extend_memory_to ~start ~size_bytes : Uint.t M.t =
    if U256.(size_bytes = zero) then return Uint.zero
    else
      let$ current_memory_words = Memory.active_words <$> !(machine_state |-- memory) in
      let$ () = update_field (machine_state |-- memory) (Memory.extend_to ~start ~size_bytes) in
      let$ new_memory_words = Memory.active_words <$> !(machine_state |-- memory) in
      if Uint.(current_memory_words >= new_memory_words) then return Uint.zero
      else return Gas.(memory_cost new_memory_words - memory_cost current_memory_words)

  let keccak =
    (* Stack *)
    let$ start = pop in
    let$ size_bytes = pop in

    (* Gas *)
    let num_hashed_words = U256.bytes_to_whole_words size_bytes in
    let$ memory_extension_gas = extend_memory_to ~start ~size_bytes in
    let$ () =
      spend
        Gas.(
          keccak256_base_cost
          + (keccak256_cost_per_word * U256.to_uint num_hashed_words)
          + memory_extension_gas )
    in

    (* Operation *)
    let$ bytes = Memory.read_block_at start size_bytes <$> !(machine_state |-- memory) in
    let$ () = push (U256.of_repr (Crypto.keccak_256 bytes)) in

    (* PC *)
    increase_pc_and_continue

  let fetch_environment_variable_opcode_impl (field : Context.t -> U256.t) =
    (* Stack *)
    (* Gas *)
    let$ () = spend Gas.base in

    (* Operation *)
    let$ ctx = get in
    let$ () = push (field ctx) in

    (* PC *)
    increase_pc_and_continue

  let address =
    fetch_environment_variable_opcode_impl (fun ctx -> Address.to_u256 ctx.execution_environment.address)
  let origin =
    fetch_environment_variable_opcode_impl (fun ctx -> Address.to_u256 ctx.execution_environment.origin)
  let caller =
    fetch_environment_variable_opcode_impl (fun ctx -> Address.to_u256 ctx.execution_environment.sender)
  let callvalue = fetch_environment_variable_opcode_impl (execution_environment |-- value).get

  let balance =
    (* Stack *)
    let$ address = Address.of_u256_truncating <$> pop in

    (* Gas *)
    let$ access_gas = Gas.account_access_cost <$> HostAPI.access_account address in
    let$ () = spend access_gas in

    (* Operation *)
    let$ balance = HostAPI.get_balance address in
    let$ () = push balance in

    (* PC *)
    increase_pc_and_continue

  let calldataload =
    (* Stack *)
    let$ i = pop in

    (* Gas *)
    let$ () = spend Gas.very_low in

    (* Operation *)
    let$ data = !(execution_environment |-- data) in
    let$ () =
      push
        ( match U256.to_int_opt i with
        | None -> U256.zero (* Index exceeds max theoretical data size *)
        | Some i -> U256.of_repr (B32.sub_with_zero_padding data i) )
    in

    (* PC *)
    increase_pc_and_continue

  let calldatasize =
    fetch_environment_variable_opcode_impl (fun ctx ->
        U256.of_int (Bytes.length ctx.execution_environment.data) )

  let codesize =
    fetch_environment_variable_opcode_impl (fun ctx ->
        U256.of_int (Bytes.length ctx.execution_environment.bytecode) )

  let copy_input_data_opcode_impl data_location =
    (* Stack *)
    let$ dst_start = pop in
    let$ src_start = pop in
    let$ size_bytes = pop in

    (* Gas *)
    let n_words = U256.(to_uint (bytes_to_whole_words size_bytes)) in
    let$ memory_extension_gas = extend_memory_to ~start:dst_start ~size_bytes in
    let$ () = spend Gas.(very_low + (n_words * copy_cost_per_word) + memory_extension_gas) in

    (* Operation *)
    let$ data = !data_location in
    let block =
      match (U256.to_int_opt src_start, U256.to_int_opt size_bytes) with
      | Some src_start, Some size -> Bytes.sub_with_zero_padding data src_start size
      | _, Some size -> Bytes.make size '\x00'
      | _, None -> assert false
    in
    let$ () = update_field (machine_state |-- memory) (Memory.write_block_at dst_start block) in

    (* PC *)
    increase_pc_and_continue

  let calldatacopy = copy_input_data_opcode_impl (execution_environment |-- data)

  let codecopy = copy_input_data_opcode_impl (execution_environment |-- bytecode)

  let gasprice = fetch_environment_variable_opcode_impl (execution_environment |-- price).get

  let extcodesize =
    (* Stack *)
    let$ address = Address.of_u256_truncating <$> pop in

    (* Gas *)
    let$ access_gas = Gas.account_access_cost <$> HostAPI.access_account address in
    let$ () = spend access_gas in

    (* Operation *)
    let$ size = U256.of_int64 <$> HostAPI.get_code_size address in
    let$ () = push size in

    (* PC *)
    increase_pc_and_continue

  let extcodecopy =
    (* Stack *)
    let$ address = Address.of_u256_truncating <$> pop in
    let$ dst_start = pop in
    let$ src_start = pop in
    let$ size_bytes = pop in

    (* Gas *)
    let$ access_gas = Gas.account_access_cost <$> HostAPI.access_account address in
    let n_words = U256.(to_uint (bytes_to_whole_words size_bytes)) in
    let$ memory_extension_gas = extend_memory_to ~start:dst_start ~size_bytes in
    let$ () = spend Gas.((n_words * copy_cost_per_word) + memory_extension_gas + access_gas) in

    (* Operation *)
    let$ block =
      match (U256.to_int_opt src_start, U256.to_int_opt size_bytes) with
      | _, Some 0 -> return Bytes.empty (* No need for the copy_code call *)
      | Some offset, Some size -> HostAPI.copy_code address ~offset ~size
      | None, Some size -> return (Bytes.make size '\x00')
      | _, None -> assert false (* This should have caused an OOG error. *)
    in
    let$ () = update_field (machine_state |-- memory) (Memory.write_block_at dst_start block) in

    (* PC *)
    increase_pc_and_continue

  let extcodehash =
    (* Stack *)
    let$ address = Address.of_u256_truncating <$> pop in

    (* Gas *)
    let$ access_gas = Gas.account_access_cost <$> HostAPI.access_account address in
    let$ () = spend access_gas in

    (* Operation *)
    let$ hash = Option.value ~default:B32.zeros <$> HostAPI.get_code_hash address in
    let$ () = push (U256.of_repr hash) in

    (* PC *)
    increase_pc_and_continue

  let returndatasize =
    fetch_environment_variable_opcode_impl (fun ctx ->
        U256.of_int (Bytes.length ctx.machine_state.output_buffer) )

  let returndatacopy =
    (* Stack *)
    let$ dst_start = pop in
    let$ src_start = pop in
    let$ size_bytes = pop in

    (* Gas *)
    let$ data = !(machine_state |-- output_buffer) in
    (* Unlike similar opcodes, returndatacopy fails on out-of-bounds memory access. We check this before
       extending the memory and spending gas. *)
    (* YP (158) *)
    let$ src_start, size =
      match (U256.to_int_opt src_start, U256.to_int_opt size_bytes) with
      | None, _ | _, None -> fail Invalid_memory_access
      | Some start, Some sz when start + sz > Bytes.length data -> fail Invalid_memory_access
      | Some start, Some sz -> return (start, sz)
    in

    let n_words = U256.(to_uint (bytes_to_whole_words size_bytes)) in
    let$ memory_extension_gas = extend_memory_to ~start:dst_start ~size_bytes in
    let$ () = spend Gas.(very_low + (n_words * copy_cost_per_word) + memory_extension_gas) in

    (* Operation *)
    let block = Bytes.sub data src_start size in
    let$ () = update_field (machine_state |-- memory) (Memory.write_block_at dst_start block) in

    (* PC *)
    increase_pc_and_continue

  let blockhash =
    (* Stack *)
    let$ block_num = U256.to_uint <$> pop in

    (* Gas *)
    let$ () = spend Gas.block_hash_cost in

    (* Operation *)
    let$ current_block_num = U256.to_uint <$> !(execution_environment |-- header |-- number) in
    let$ hash =
      if Uint.(current_block_num <= block_num || current_block_num > block_num + ~$256) then return U256.zero
      else
        let$ hash = HostAPI.get_block_hash (Uint.to_int64 block_num) in
        match hash with Some hash -> return (U256.of_repr hash) | None -> fail Argument_out_of_range
    in
    let$ () = push hash in

    (* PC *)
    increase_pc_and_continue

  let coinbase =
    fetch_environment_variable_opcode_impl (fun ctx ->
        Address.to_u256 ctx.execution_environment.header.coinbase )

  let timestamp = fetch_environment_variable_opcode_impl (execution_environment |-- header |-- timestamp).get

  let number = fetch_environment_variable_opcode_impl (execution_environment |-- header |-- number).get

  let prevrandao =
    fetch_environment_variable_opcode_impl (execution_environment |-- header |-- prev_randao).get

  let gaslimit = fetch_environment_variable_opcode_impl (execution_environment |-- header |-- gas_limit).get

  (* The yellow paper gets the chain ID directly as the ambient variable β, as opposed to fetching it
     from a specific field in the execution environment. The executable specs, on the other hand, does get
     it from the block environment. *)
  let chainid = fetch_environment_variable_opcode_impl (execution_environment |-- header |-- chain_id).get

  let selfbalance =
    (* Stack *)
    (* Gas *)
    let$ () = spend Gas.low in

    (* Operation *)
    let$ self_addr = self in
    let$ balance = HostAPI.get_balance self_addr in
    let$ () = push balance in

    (* PC *)
    increase_pc_and_continue

  let basefee = fetch_environment_variable_opcode_impl (execution_environment |-- header |-- base_fee).get

  (* EIP-4844 *)
  let blobhash =
    (* Stack *)
    let$ index = pop in

    (* Gas *)
    let$ () = spend Gas.very_low in

    (* Operation *)
    let$ hashes = !(execution_environment |-- blob_versioned_hashes) in
    let hash =
      match U256.to_int_opt index with
      | None -> U256.zero
      | Some i -> ( match List.nth_opt hashes i with None -> U256.zero | Some h -> U256.of_repr h )
    in
    let$ () = push hash in

    (* PC *)
    increase_pc_and_continue

  (* EIP-7516 *)
  let blobbasefee =
    (* Stack *)
    (* Gas *)
    let$ () = spend Gas.base in

    (* Operation *)
    let$ fee = !(execution_environment |-- blob_base_fee) in
    let$ () = push fee in

    (* PC *)
    increase_pc_and_continue

  let pop_ =
    (* Stack *)
    let$ _ = pop in

    (* Gas *)
    let$ () = spend Gas.base in

    (* Operation *)
    (* PC *)
    increase_pc_and_continue

  let push_ i : opcode_impl =
    assert (i >= 0) ;
    assert (i <= 32) ;
    (* Stack *)
    (* Gas *)
    let$ () = spend (if i = 0 then Gas.base else Gas.very_low) in

    (* Operation *)
    let$ here = U256.to_int <$> !(machine_state |-- pc) in
    let$ code = !(execution_environment |-- bytecode) in
    let$ () = push (U256.of_uint_exn (Uint.of_bytes_be (Bytes.sub_with_zero_padding code (here + 1) i))) in

    (* PC *)
    update_pc_and_continue (fun pc -> U256.(pc + one + ~$i))

  let dup i =
    assert (i >= 1) ;
    assert (i <= 16) ;
    (* Stack *)
    let$ nth_elt =
      !(machine_state |-- stack)
      |> M.fmap (fun l -> List.nth_opt l (i - 1))
      >>= M.Option.or_fail Stack_underflow
    in

    (* Gas *)
    let$ () = spend Gas.very_low in

    (* Operation *)
    let$ () = push nth_elt in

    (* PC *)
    increase_pc_and_continue

  let rec replace_list i x l =
    match (i, l) with
    | 0, y :: ys -> Some (y, x :: ys)
    | _, [] -> None
    | i, y :: ys -> (
      match replace_list (i - 1) x ys with Some (y1, ys') -> Some (y1, y :: ys') | None -> None )

  let swap i =
    assert (i >= 1) ;
    assert (i <= 16) ;
    (* Stack *)
    let$ first = pop in
    let$ nth, stack' =
      !(machine_state |-- stack) |> M.fmap (replace_list (i - 1) first) >>= Option.or_fail Stack_underflow
    in
    let$ () = machine_state |-- stack := stack' in

    (* Gas *)
    let$ () = spend Gas.very_low in

    (* Operation *)
    let$ () = push nth in

    (* PC *)
    increase_pc_and_continue

  (* MEMORY *)
  let mload =
    (* Stack *)
    let$ pos = pop in

    (* Gas *)
    let$ memory_extension_gas = extend_memory_to ~start:pos ~size_bytes:U256.(~$32) in
    let$ () = spend Gas.(very_low + memory_extension_gas) in

    (* Operation *)
    let$ mem = Memory.read_word_at pos <$> !(machine_state |-- memory) in
    let$ () = push mem in

    (* PC *)
    increase_pc_and_continue

  let mstore =
    (* Stack *)
    let$ pos = pop in
    let$ value = pop in

    (* Gas *)
    let$ memory_extension_gas = extend_memory_to ~start:pos ~size_bytes:U256.(~$32) in
    let$ () = spend Gas.(very_low + memory_extension_gas) in

    (* Operation *)
    let$ () = update_field (machine_state |-- memory) (Memory.write_word_at pos value) in

    (* PC *)
    increase_pc_and_continue

  let mstore8 =
    (* Stack *)
    let$ pos = pop in
    let$ value = pop in

    (* Gas *)
    let$ memory_extension_gas = extend_memory_to ~start:pos ~size_bytes:U256.one in
    let$ () = spend Gas.(very_low + memory_extension_gas) in

    (* Operation *)
    let$ () =
      update_field (machine_state |-- memory) (Memory.write_byte_at pos U256.(byte ~index_le:0 value))
    in

    (* PC *)
    increase_pc_and_continue

  let sload =
    (* Stack *)
    let$ key = pop in

    (* Gas *)
    let$ self_addr = self in
    let$ access = HostAPI.access_storage self_addr (U256.to_repr key) in
    let$ () = spend Gas.(match access with `Cold -> cold_sload_cost | `Warm -> warm_access_cost) in

    (* Operation *)
    let$ value = U256.of_repr <$> HostAPI.get_storage self_addr (U256.to_repr key) in
    let$ () = push value in

    (* PC *)
    increase_pc_and_continue

  let sstore =
    (* Stack *)
    let$ key = pop in
    let$ value' = pop in

    (* Gas *)
    (* Protection against reentrancy attacks, see EIP-2200 *)
    let$ current_gas = !(machine_state |-- gas) in
    let$ () = when_ Gas.(current_gas <= call_stipend) (fail Out_of_gas) in

    (* Operation *)
    (* Exceptionally, this is done before spending gas, as we use the host StorageStatus.t to calculate gas
       costs. *)
    let$ () = check_write_permissions in
    let$ self_addr = self in
    let$ access = HostAPI.access_storage self_addr (U256.to_repr key) in
    let$ storage_status = HostAPI.set_storage self_addr (U256.to_repr key) (U256.to_repr value') in

    let access_gas = Gas.(match access with `Warm -> zero | `Cold -> cold_sload_cost) in
    let update_gas =
      match storage_status with
      | Added -> Gas.sset_cost
      | Deleted | Modified -> Gas.sreset_cost
      | _ -> Gas.warm_access_cost
    in
    let$ () = spend Gas.(access_gas + update_gas) in

    (* The refund here can be negative as we may be undoing a previous positive refund *)
    let refund =
      Integer.(
        match storage_status with
        | Deleted | ModifiedDeleted -> Gas.(as_signed sclear_refund)
        | DeletedAdded -> zero - Gas.(as_signed sclear_refund)
        | DeletedRestored ->
            Gas.(as_signed sreset_cost) - Gas.(as_signed warm_access_cost) - Gas.(as_signed sclear_refund)
        | AddedDeleted -> Gas.(as_signed sset_cost) - Gas.(as_signed warm_access_cost)
        | ModifiedRestored -> Gas.(as_signed sreset_cost) - Gas.(as_signed warm_access_cost)
        | Assigned | Added | Modified -> zero )
    in
    let$ () =
      (* Overall gas refund is non-negative, but we have to do signed addition here *)
      update_field (machine_state |-- gas_refund) (fun r -> Integer.(r + refund))
    in

    (* PC *)
    increase_pc_and_continue

  let jump =
    (* Stack *)
    let$ new_pc = pop in

    (* Gas *)
    let$ () = spend Gas.mid in

    (* Operation *)
    let$ () = check_jump_destination new_pc in

    (* PC *)
    update_pc_and_continue (fun _ -> new_pc)

  let jumpi =
    (* Stack *)
    let$ new_pc = pop in
    let$ condition = pop in

    (* Gas *)
    let$ () = spend Gas.high in

    (* Operation *)
    (* PC *)
    if U256.is_zero condition then increase_pc_and_continue
    else
      let$ () = check_jump_destination new_pc in
      update_pc_and_continue (fun _ -> new_pc)

  let pc_ = fetch_environment_variable_opcode_impl (machine_state |-- pc).get

  let msize =
    fetch_environment_variable_opcode_impl (fun ctx ->
        U256.of_uint_truncating Uint.(~$32 * Memory.active_words ctx.machine_state.memory) )

  let gas_ =
    (* Stack *)
    (* Gas *)
    let$ () = spend Gas.base in

    (* Operation *)
    let$ current_gas = !(machine_state |-- gas) in
    let$ () = push (U256.of_uint_truncating current_gas) in

    (* PC *)
    increase_pc_and_continue

  let jumpdest =
    (* Stack *)
    (* Gas *)
    let$ () = spend Gas.jumpdest in

    (* Operation *)
    (* PC *)
    increase_pc_and_continue

  let tload =
    (* Stack *)
    let$ key = pop in

    (* Gas *)
    let$ () = spend Gas.warm_access_cost in

    (* Operation *)
    let$ self_addr = self in
    let$ value = U256.of_repr <$> HostAPI.get_transient_storage self_addr (U256.to_repr key) in
    let$ () = push value in

    (* PC *)
    increase_pc_and_continue

  let tstore =
    (* Stack *)
    let$ key = pop in
    let$ value = pop in

    (* Gas *)
    let$ () = spend Gas.warm_access_cost in

    (* Operation *)
    let$ () = check_write_permissions in
    let$ self_addr = self in
    let$ () = HostAPI.set_transient_storage self_addr (U256.to_repr key) (U256.to_repr value) in

    (* PC *)
    increase_pc_and_continue

  let mcopy =
    (* Stack *)
    let$ dst_start = pop in
    let$ src_start = pop in
    let$ size_bytes = pop in

    (* Gas *)
    let n_words = U256.(to_uint (bytes_to_whole_words size_bytes)) in
    let$ memory_extension_gas = extend_memory_to ~start:U256.(max src_start dst_start) ~size_bytes in
    let$ () = spend Gas.(very_low + (n_words * copy_cost_per_word) + memory_extension_gas) in

    (* Operation *)
    let$ block = Memory.read_block_at src_start size_bytes <$> !(machine_state |-- memory) in
    let$ () = update_field (machine_state |-- memory) (Memory.write_block_at dst_start block) in

    (* PC *)
    increase_pc_and_continue

  let log n_topics =
    assert (n_topics >= 0 && n_topics <= 4) ;
    (* Stack *)
    let$ start = pop in
    let$ size_bytes = pop in

    let$ topics : B32.t list =
      List.of_seq <$> (Seq.(take n_topics (ints 0)) |> Seq.mapM ~f:(fun _ -> U256.to_repr <$> pop))
    in

    (* Gas *)
    let$ memory_extension_gas = extend_memory_to ~start ~size_bytes in
    let$ () =
      spend
        Gas.(
          log_cost
          + (log_cost_per_byte * U256.to_uint size_bytes)
          + (log_cost_per_topic * ~$n_topics)
          + memory_extension_gas )
    in

    (* Operation *)
    let$ () = check_write_permissions in
    let$ self_addr = self in
    let$ data = Memory.read_block_at start size_bytes <$> !(machine_state |-- memory) in
    let$ () = HostAPI.emit_log self_addr ~data ~topics in

    (* PC *)
    increase_pc_and_continue

  let merge_child_gas_and_refund ~status_code ~gas_left ~gas_refund =
    let$ () = update_field (machine_state |-- gas) (fun g -> Uint.(g + of_int64 gas_left)) in
    if status_code = Evmc.Result.StatusCode.Success then
      update_field (machine_state |-- MachineState.gas_refund) (fun g -> Integer.(g + of_int64 gas_refund))
    else return (assert (Int64.(gas_refund = zero)))

  type delegation =
    | Delegated of {code_address : Address.t; delegation_access_gas : Uint.t}
    | Direct of {code : Bytes.t}

  let generic_call_impl
      ~(kind : Evmc.Message.CallKind.t)
      ~(call_gas : U256.t)
      ~(value : U256.t)
      ~(sender : Address.t)
      ~(recipient : Address.t)
      ~(code_address : Address.t)
      ~(delegation : delegation)
      ~(static : bool)
      ~(input_start : U256.t)
      ~(input_size : U256.t)
      ~(output_start : U256.t)
      ~(output_size : U256.t) =
    let$ () = machine_state |-- output_buffer := Bytes.empty in

    let$ new_depth = ( + ) 1 <$> !(execution_environment |-- depth) in
    if new_depth > max_stack_depth then
      let$ () = update_field (machine_state |-- gas) (fun g -> Uint.(g + U256.to_uint call_gas)) in
      push U256.zero
    else
      let$ input_data = Memory.read_block_at input_start input_size <$> !(machine_state |-- memory) in
      let delegated = match delegation with Direct _ -> false | Delegated _ -> true in
      let message =
        Evmc.(
          Message.
            { kind
            ; delegated
            ; static
            ; depth = Int32.of_int new_depth
            ; gas = U256.to_uint64 call_gas
            ; recipient
            ; sender
            ; input_data
            ; value
            ; create2_salt = B32.zeros
            ; code_address
            ; code = Bytes.empty } )
      in
      let$ {status_code; gas_left; gas_refund; output_data; create_address} = HostAPI.call message in
      let$ () = merge_child_gas_and_refund ~status_code ~gas_left ~gas_refund in
      assert (Address.(zero = create_address)) ;

      let$ () = machine_state |-- output_buffer := output_data in
      if status_code = Evmc.Result.StatusCode.Success then
        let$ () = push U256.one in
        let truncated_output =
          match U256.to_int_opt output_size with
          | None -> output_data
          | Some i -> Bytes.sub output_data 0 (min i (Bytes.length output_data))
        in
        update_field (machine_state |-- memory) (Memory.write_block_at output_start truncated_output)
      else push U256.zero

  let generic_create_impl
      ~(kind : Evmc.Message.CallKind.t)
      ~(create2_salt : B32.t)
      ~(endowment : U256.t)
      ~(input_start : U256.t)
      ~(input_size_bytes : U256.t) =
    let$ () = when_ U256.(input_size_bytes > ~$max_init_code_size) (fail Out_of_gas) in

    let$ () = check_write_permissions in

    let$ new_depth = ( + ) 1 <$> !(execution_environment |-- depth) in
    let$ self_addr = self in
    let$ self_balance = HostAPI.get_balance self_addr in
    if self_balance < endowment || new_depth > max_stack_depth then push U256.zero
    else
      let$ create_message_gas = Uint.minus_1_64th <$> !(machine_state |-- gas) in
      let$ () = update_field (machine_state |-- gas) (fun g -> Uint.(g - create_message_gas)) in

      let$ () = machine_state |-- output_buffer := Bytes.empty in
      let$ call_data = Memory.read_block_at input_start input_size_bytes <$> !(machine_state |-- memory) in

      let message =
        Evmc.(
          Message.
            { kind
            ; delegated = false
            ; static = false
            ; depth = Int32.of_int new_depth
            ; gas = Uint.to_int64 create_message_gas
            ; recipient = Address.zero
            ; sender = self_addr
            ; input_data = call_data
            ; value = endowment
            ; create2_salt
            ; code_address = Address.zero
            ; code = Bytes.empty } )
      in
      let$ {status_code; gas_left; gas_refund; output_data; create_address} = HostAPI.call message in
      let$ () = merge_child_gas_and_refund ~status_code ~gas_left ~gas_refund in
      if status_code = Evmc.Result.StatusCode.Success then
        let$ () = machine_state |-- output_buffer := Bytes.empty in
        push (Address.to_u256 create_address)
      else
        let$ () = machine_state |-- output_buffer := output_data in
        push U256.zero

  let create =
    (* Stack *)
    let$ endowment = pop in
    let$ input_start = pop in
    let$ input_size_bytes = pop in

    (* Gas *)
    let$ memory_extension_gas = extend_memory_to ~start:input_start ~size_bytes:input_size_bytes in
    let$ () =
      spend
        Gas.(
          memory_extension_gas
          + create_cost
          + (create_cost_per_initcode_word * U256.(to_uint (bytes_to_whole_words input_size_bytes))) )
    in

    (* Operation *)
    let$ () =
      generic_create_impl ~create2_salt:B32.zeros ~kind:Evmc.Message.CallKind.Create ~endowment ~input_start
        ~input_size_bytes
    in

    (* PC *)
    increase_pc_and_continue

  let access_delegation (addr : Address.t) : delegation M.t =
    let$ code = HostAPI.copy_code addr ~offset:0 ~size:Delegation.eoa_delegated_code_length in
    match Delegation.get_delegated_address code with
    | None -> return (Direct {code})
    | Some code_address ->
        let$ delegation_access_gas = Gas.account_access_cost <$> HostAPI.access_account code_address in
        return (Delegated {code_address; delegation_access_gas})

  let call_opcode_impl
      ~kind
      ~gas
      ~value
      ~sender
      ~recipient
      ~code_address
      ~input_start
      ~input_size
      ~output_start
      ~output_size
      ~static_call =
    (* Gas *)
    let$ input_memory_extension_gas = extend_memory_to ~start:input_start ~size_bytes:input_size in
    let$ output_memory_extension_gas = extend_memory_to ~start:output_start ~size_bytes:output_size in
    let memory_extension_gas = Gas.(max input_memory_extension_gas output_memory_extension_gas) in

    let$ access_gas = Gas.account_access_cost <$> HostAPI.access_account code_address in
    let$ delegation = access_delegation code_address in
    let code_address, access_gas =
      match delegation with
      | Direct _delegation -> (code_address, access_gas)
      | Delegated {delegation_access_gas; code_address} ->
          (code_address, Gas.(access_gas + delegation_access_gas))
    in

    let transfer_value = kind <> Evmc.Message.CallKind.DelegateCall && U256.(value <> zero) in

    let$ target_is_alive = HostAPI.account_exists recipient in
    let create_gas = Gas.(if transfer_value && not target_is_alive then new_account_cost else zero) in

    let transfer_gas = Gas.(if transfer_value then call_value else zero) in

    let$ gas_left = !(machine_state |-- MachineState.gas) in
    let Gas.{caller_spent_gas; callee_available_gas} =
      Gas.call_gas ~value ~gas ~gas_left ~memory_cost:memory_extension_gas
        ~extra_cost:Uint.(access_gas + transfer_gas + create_gas)
    in

    let$ () = spend Gas.(caller_spent_gas + memory_extension_gas) in

    (* Operation *)
    let$ () = when_ transfer_value check_write_permissions in

    let$ in_static_context = not <$> !(execution_environment |-- write_permission) in
    let static = static_call || in_static_context in

    let$ self_addr = self in
    let$ self_balance = HostAPI.get_balance self_addr in
    let$ () =
      if transfer_value && U256.(self_balance < value) then
        let$ () = push U256.zero in
        let$ () = update_field (machine_state |-- MachineState.gas) (fun g -> Uint.(g + caller_spent_gas)) in
        machine_state |-- output_buffer := Bytes.empty
      else
        generic_call_impl ~kind
          ~call_gas:U256.(of_uint_exn callee_available_gas)
          ~value ~sender ~recipient ~code_address ~input_start ~input_size ~output_start ~output_size
          ~delegation ~static
    in

    (* PC *)
    increase_pc_and_continue

  let call =
    (* Stack *)
    let$ gas = U256.to_uint <$> pop in
    let$ recipient = Address.of_u256_truncating <$> pop in
    let$ value = pop in
    let$ input_start = pop in
    let$ input_size = pop in
    let$ output_start = pop in
    let$ output_size = pop in

    let$ self_addr = self in
    call_opcode_impl
      ~kind:Evmc.Message.CallKind.Call
      ~gas
      ~sender:self_addr
      ~recipient
      ~code_address:recipient
      ~value
      ~input_start
      ~input_size
      ~output_start
      ~output_size
      ~static_call:false
  [@@ocamlformat "disable"]

  let callcode =
    (* Stack *)
    let$ gas = U256.to_uint <$> pop in
    let$ code_address = Address.of_u256_truncating <$> pop in
    let$ value = pop in
    let$ input_start = pop in
    let$ input_size = pop in
    let$ output_start = pop in
    let$ output_size = pop in

    let$ self_addr = self in
    call_opcode_impl
      ~kind:Evmc.Message.CallKind.CallCode
      ~gas
      ~value
      ~sender:self_addr
      ~recipient:self_addr
      ~code_address
      ~input_start
      ~input_size
      ~output_start
      ~output_size
      ~static_call:false
  [@@ocamlformat "disable"]

  let return_ =
    (* Stack *)
    let$ start = pop in
    let$ size_bytes = pop in

    (* Gas *)
    let$ () =
      (* We do not spend gas when copying a zero-size return value *)
      when_
        U256.(size_bytes > zero)
        (let$ memory_extension_gas = extend_memory_to ~start ~size_bytes in
         spend memory_extension_gas )
    in

    (* Operation *)
    let$ result = Memory.read_block_at start size_bytes <$> !(machine_state |-- memory) in
    let$ () = machine_state |-- output_buffer := result in

    (* PC *)
    finish_execution

  let delegatecall =
    (* Stack *)
    let$ gas = U256.to_uint <$> pop in
    let$ code_address = Address.of_u256_truncating <$> pop in
    let$ input_start = pop in
    let$ input_size = pop in
    let$ output_start = pop in
    let$ output_size = pop in

    let$ original_sender = !(execution_environment |-- sender) in
    let$ original_value = !(execution_environment |-- value) in

    let$ self_addr = self in

    call_opcode_impl ~kind:Evmc.Message.CallKind.DelegateCall
      ~gas
      ~sender:original_sender
      ~recipient:self_addr
      ~code_address
      ~value:original_value
      ~input_start
      ~input_size
      ~output_start
      ~output_size
      ~static_call:false
  [@@ocamlformat "disable"]

  let create2 =
    (* Stack *)
    let$ endowment = pop in
    let$ input_start = pop in
    let$ input_size_bytes = pop in
    let$ create2_salt = U256.to_repr <$> pop in

    (* Gas *)
    let$ memory_extension_gas = extend_memory_to ~start:input_start ~size_bytes:input_size_bytes in
    let input_size_in_words = U256.(to_uint (bytes_to_whole_words input_size_bytes)) in
    let$ () =
      spend
        Gas.(
          memory_extension_gas
          + create_cost
          + (keccak256_cost_per_word * input_size_in_words)
          + (create_cost_per_initcode_word * input_size_in_words) )
    in

    (* Operation *)
    let$ () =
      generic_create_impl ~kind:Evmc.Message.CallKind.Create2 ~endowment ~input_start ~input_size_bytes
        ~create2_salt
    in

    (* PC *)
    increase_pc_and_continue

  let staticcall =
    (* Stack *)
    let$ gas = U256.to_uint <$> pop in
    let$ recipient = Address.of_u256_truncating <$> pop in
    let$ input_start = pop in
    let$ input_size = pop in
    let$ output_start = pop in
    let$ output_size = pop in

    let$ self_addr = self in
    call_opcode_impl
      ~kind:Evmc.Message.CallKind.Call
      ~gas
      ~sender:self_addr
      ~recipient
      ~code_address:recipient
      ~value:U256.zero
      ~input_start
      ~input_size
      ~output_start
      ~output_size
      ~static_call:true
  [@@ocamlformat "disable"]

  let revert =
    (* Stack *)
    let$ start = pop in
    let$ size_bytes = pop in

    (* Gas *)
    let$ () =
      (* We do not spend gas when copying a zero-size return value *)
      when_
        U256.(size_bytes > zero)
        (let$ memory_extension_gas = extend_memory_to ~start ~size_bytes in
         spend memory_extension_gas )
    in

    (* Operation *)
    let$ result = Memory.read_block_at start size_bytes <$> !(machine_state |-- memory) in
    let$ () = machine_state |-- output_buffer := result in

    (* PC *)
    fail Revert

  let selfdestruct =
    (* Stack *)
    let$ beneficiary = Address.of_u256_truncating <$> pop in

    (* Gas *)
    let$ access = HostAPI.access_account beneficiary in
    (* Unlike in most other cases, the access cost for selfdestruct with a warm beneficiary is zero, rather
       than Gas.warm_access_cost, see C_selfdestruct in YP. *)
    let access_gas = match access with `Cold -> Gas.cold_account_access_cost | `Warm -> Gas.zero in
    let$ self_addr = self in
    let$ self_balance = HostAPI.get_balance self_addr in
    let$ beneficiary_exists = HostAPI.account_exists beneficiary in
    let new_account_gas =
      Gas.(
        if (not beneficiary_exists) && U256.(self_balance <> zero) then self_destruct_new_account_cost
        else zero )
    in
    let$ () = spend Gas.(self_destruct_cost + access_gas + new_account_gas) in

    (* Operation *)
    let$ () = check_write_permissions in
    (* EIP-3529 removed gas refunds from selfdestruct, so we do not need to check the return value. *)
    let$ () = ignore <$> HostAPI.selfdestruct ~address:self_addr ~beneficiary in

    (* PC *)
    finish_execution

  let execute_opcode (opcode : Opcode.t) =
    let impl =
      match opcode with
      (* Arithmetic *)
      | Add -> add
      | Mul -> mul
      | Sub -> sub
      | Udiv -> udiv
      | Sdiv -> sdiv
      | Umod -> umod
      | Smod -> smod
      | Addmod -> addmod
      | Mulmod -> mulmod
      | Exp -> exp
      | Signextend -> signextend
      (* Comparison *)
      | Lt -> lt
      | Gt -> gt
      | Slt -> slt
      | Sgt -> sgt
      | Eq -> eq
      | Iszero -> is_zero
      (* Bitwise *)
      | And -> bitwise_and
      | Or -> bitwise_or
      | Xor -> bitwise_xor
      | Not -> bitwise_not
      | Byte -> byte
      | Shl -> shl
      | Shr -> shr
      | Sar -> sar
      (* Cryptography *)
      | Keccak -> keccak
      (* Environment *)
      | Address -> address
      | Balance -> balance
      | Origin -> origin
      | Caller -> caller
      | Callvalue -> callvalue
      | Calldataload -> calldataload
      | Calldatasize -> calldatasize
      | Calldatacopy -> calldatacopy
      | Codesize -> codesize
      | Codecopy -> codecopy
      | Gasprice -> gasprice
      | Extcodesize -> extcodesize
      | Extcodecopy -> extcodecopy
      | Returndatasize -> returndatasize
      | Returndatacopy -> returndatacopy
      | Extcodehash -> extcodehash
      | Blockhash -> blockhash
      | Coinbase -> coinbase
      | Timestamp -> timestamp
      | Number -> number
      | Prevrandao -> prevrandao
      | Gaslimit -> gaslimit
      | Chainid -> chainid
      | Selfbalance -> selfbalance
      | Basefee -> basefee
      | Blobhash -> blobhash
      | Blobbasefee -> blobbasefee
      | Gas -> gas_
      (* Memory and storage *)
      | Msize -> msize
      | Mload -> mload
      | Mstore -> mstore
      | Mstore8 -> mstore8
      | Sload -> sload
      | Sstore -> sstore
      | Tload -> tload
      | Tstore -> tstore
      | Mcopy -> mcopy
      (* Control flow *)
      | Jump -> jump
      | Jumpi -> jumpi
      | Pc -> pc_
      | Jumpdest -> jumpdest
      | Stop -> stop
      | Return -> return_
      | Revert -> revert
      (* Stack *)
      | Pop -> pop_
      | Push i -> push_ i
      | Dup i -> dup i
      | Swap i -> swap i
      (* System *)
      | Log i -> log i
      | Create -> create
      | Call -> call
      | Callcode -> callcode
      | Delegatecall -> delegatecall
      | Create2 -> create2
      | Staticcall -> staticcall
      | Selfdestruct -> selfdestruct
      (* Error *)
      | Invalid -> invalid
      | Undefined _ -> undefined
    in
    impl

  let trace_stack =
    if Params.trace then ( fun stack ->
      Format.printf "<top>\n" ;
      List.iter (fun elt -> Format.printf "%s\n" (U256.to_string elt)) stack ;
      Format.printf "<bottom>\n" ;
      Format.print_flush () )
    else fun _ -> ()

  let trace_state =
    if Params.trace then (
      let$ ms = !machine_state in
      Format.printf "PC: %s\n" (U256.to_string ms.pc) ;
      Format.printf "Gas: %s\n" (Uint.to_string ms.gas) ;
      Format.printf "Stack: \n" ;
      trace_stack ms.stack ;
      Format.printf "Memory: \n" ;
      Memory.dump ms.memory ;
      Format.print_flush () ;
      return () )
    else return ()

  let rec run (code : Bytes.t) : unit M.t =
    let$ () = trace_state in
    let$ pc = !(machine_state |-- pc) in
    let opcode =
      (* YP (157) *)
      match U256.to_int_opt pc with
      | Some pc when pc < Bytes.length code -> Opcode.of_byte code.[pc]
      | _ -> Opcode.Stop
    in
    trace (fun () ->
        let info = Opcode.info opcode in
        Format.sprintf "Executing opcode 0x%x(%s)\n" (Char.code info.byte) info.name ) ;
    let$ continue = execute_opcode opcode in
    if continue then run code else return ()

  let execute (msg : Evmc.Message.t) (code : Bytes.t) : Evmc.Result.t Host.t =
    trace (fun () -> "Start execution\n") ;
    trace (fun () -> Format.sprintf "Bytecode: %s\n" (Bytes.to_hex_string code)) ;
    let open Host in
    let open Monad.Make (Host) in
    let$ tx_context = get_tx_context in
    let ctx = Context.make tx_context msg code in
    let$ res, ctx = M.StHost.run (run code) ctx in
    trace (fun () -> "Finished execution\n") ;
    return
      ( match res with
      | Ok () ->
          trace (fun () ->
              Format.sprintf "Execution OK, returning [[%s]]\n"
                (Bytes.to_hex_string ctx.machine_state.output_buffer) ) ;
          Evmc.Result.
            { status_code = Success
            ; gas_left = Uint.to_uint64 ctx.machine_state.gas
            ; gas_refund = Integer.to_int64 ctx.machine_state.gas_refund
            ; output_data = ctx.machine_state.output_buffer
            ; create_address = Address.zero }
      | Error err -> (
          trace (fun () -> Format.sprintf "Execution ERROR: %s\n" (Evmc.Result.StatusCode.to_string err)) ;
          match err with
          | Success -> assert false
          | Revert ->
              (* If a contract finishes with a REVERT instruction, remaining gas is refunded and the output
               buffer is returned, see YP (152) *)
              Evmc.Result.
                { status_code = err
                ; gas_left = Uint.to_uint64 ctx.machine_state.gas
                ; gas_refund = 0L
                ; output_data = ctx.machine_state.output_buffer
                ; create_address = Address.zero }
          | _ -> Evmc.Result.failure err ) )
end
