open Numeric
open Byte_string

module Make
    (Params : sig
      include Chain.Monad.PARAMS
      val trace : bool
    end)
    (Host : Evmc.HOST) =
struct
  module Memory : sig
    type t
    val empty : memory_capacity:Uint.t -> t

    val max_memory_usage : Uint.t

    val read_block_at : U256.t -> U256.t -> t -> Bytes.t
    val read_word_at : U256.t -> t -> U256.t

    val write_block_at : U256.t -> Bytes.t -> t -> t
    val write_word_at : U256.t -> U256.t -> t -> t
    val write_byte_at : U256.t -> char -> t -> t

    val active_words : t -> Uint.t (* μ_i *)

    val extend_to : start:U256.t -> size_bytes:U256.t -> t -> t option

    val available_memory_size : t -> Uint.t

    (* For debugging purposes *)
    val dump : t -> unit
  end = struct
    (* Memory is represented as an int-indexed map of 32-byte words. In principle, Ethereum memory should
       support up to 256-bit byte indexing, but in practice memory expansion costs and gas limits make
       it impossible to go beyond an int.
       MIP-3 further adds a hard 8MB limit on memory size. *)
    module M = Map.Make (Int)
    type t =
      { contents : B32.t M.t (* Corresponds to μ_m *)
      ; active_bytes : Uint.t (* Corresponds to μ_i * 32 *)
      ; memory_capacity : Uint.t (* Total memory capacity in bytes. *) }

    let max_memory_usage =
      match Params.revision with
      | `Eight -> Uint.zero
      | `Nine ->
          (* MIP-3. *)
          Uint.of_int (8 * 1024 * 1024)

    (** Check that the index start + size - 1 does not overflow U256.t. *)
    let overflow_check start size_bytes = assert (start + size_bytes > start)

    (** Check that the index start + size - 1 does not exceed the active bytes. Memory must be extended
        by a call to [extend_to] beforehand. *)
    let active_bytes_overflow_check mem start size_bytes =
      assert (Uint.(mem.active_bytes >= ~$start + ~$size_bytes))

    let alignment_mask = 32 - 1

    let is_aligned (addr : int) = addr land alignment_mask = 0

    let align (addr : int) = (addr land lnot alignment_mask, addr land alignment_mask)

    let read_aligned (addr : int) (mem : t) : B32.t =
      assert (is_aligned addr) ;
      Option.value ~default:B32.zeros (M.find_opt addr mem.contents)

    let write_aligned (addr : int) (v : B32.t) (mem : t) : t =
      assert (is_aligned addr) ;
      {mem with contents = M.add addr v mem.contents}

    let read_block_at start size (mem : t) =
      if U256.(size = zero) then Bytes.empty
      else
        let start = U256.to_int start in
        let size = U256.to_int size in
        overflow_check start size ;
        active_bytes_overflow_check mem start size ;
        let start, offset = align start in
        let n_words = ((size + 31) / 32) + if offset = 0 then 0 else 1 in
        let words =
          List.init n_words (fun w_index -> B32.to_bytes (read_aligned (start + (w_index * 32)) mem))
        in
        let block = Bytes.(concat empty words) in
        Bytes.sub block offset size

    let read_word_at pos (mem : t) : U256.t =
      let pos' = U256.to_int pos in
      if is_aligned pos' then
        (* Aligned reads are cheaper. *)
        U256.of_repr (read_aligned pos' mem)
      else read_block_at pos U256.(~$32) mem |> U256.Repr.of_bytes_exn |> U256.of_repr

    let write_block_at (start : U256.t) (bytes : Bytes.t) (mem : t) =
      if Bytes.(bytes = empty) then mem
      else
        let start = U256.to_int start in
        let size = Bytes.length bytes in
        overflow_check start size ;
        active_bytes_overflow_check mem start size ;
        let size = Bytes.length bytes in
        let start, offset = align start in
        (* Whole aligned words touched, including the trailing word the misalignment spills into. *)
        let n_words = (offset + size + 31) / 32 in
        let suffix_len = (n_words * 32) - offset - size in
        (* The write fully overwrites every interior word, so only the two boundary words must be
           read first: the [offset]-byte prefix of the first word and the [suffix_len]-byte tail of
           the last word are preserved; everything between comes from [bytes]. *)
        let prefix =
          if offset = 0 then Bytes.empty else Bytes.sub (B32.to_bytes (read_aligned start mem)) 0 offset
        in
        let suffix =
          if suffix_len = 0 then Bytes.empty
          else
            let last = B32.to_bytes (read_aligned (start + ((n_words - 1) * 32)) mem) in
            Bytes.sub last (32 - suffix_len) suffix_len
        in
        (* [buffer] is exactly [n_words] aligned words laid end to end. *)
        let buffer = Bytes.concat Bytes.empty [prefix; bytes; suffix] in
        List.fold_left
          (fun mem w_index -> write_aligned (start + (w_index * 32)) (B32.sub buffer (w_index * 32)) mem)
          mem (List.init n_words Fun.id)

    let write_word_at (pos : U256.t) (w : U256.t) (mem : t) : t =
      let pos' = U256.to_int pos in
      if is_aligned pos' then write_aligned pos' (U256.to_repr w) mem
      else write_block_at pos (U256.to_repr_bytes w) mem

    let write_byte_at pos b (mem : t) = write_block_at pos (Bytes.make 1 b) mem

    let empty ~memory_capacity =
      assert (memory_capacity <= max_memory_usage) ;
      {contents = M.empty; active_bytes = Uint.zero; memory_capacity}

    let active_words mem = Uint.(bytes_to_whole_words mem.active_bytes)

    let available_memory_size =
      match Params.revision with
      | `Eight -> fun _mem -> max_memory_usage
      | `Nine -> fun mem -> Uint.(mem.memory_capacity - mem.active_bytes)

    let extend_to_monad_eight ~start ~size_bytes mem =
      if U256.(size_bytes = zero) then Some mem
      else
        (* Round up to whole words. *)
        let active_words = Uint.(bytes_to_whole_words (U256.to_uint start + U256.to_uint size_bytes)) in
        let active_bytes = Uint.(max mem.active_bytes (active_words * ~$32)) in
        Some {mem with active_bytes}

    let extend_to_monad_nine ~start ~size_bytes mem =
      if U256.(size_bytes = zero) then Some mem
      else
        (* Round up to whole words. *)
        let active_words = Uint.(bytes_to_whole_words (U256.to_uint start + U256.to_uint size_bytes)) in
        let active_bytes = Uint.(max mem.active_bytes (active_words * ~$32)) in
        (* MIP-3: enforce the per-call budget, not the global 8 MB ceiling. *)
        if Uint.(active_bytes <= mem.memory_capacity) then Some {mem with active_bytes} else None

    let extend_to =
      match Params.revision with `Eight -> extend_to_monad_eight | `Nine -> extend_to_monad_nine

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
      ; stack : U256.t list (* μ_s *)
      ; stack_depth : int
      ; output_buffer : Bytes.t (* μ_o *)
      ; gas_refund : Integer.t
            (* A_r *)
            (* Gas refund is not part of machine state as per YP, but EVMC boundaries are split oddly: though
               most of the information in the Accrued Substate (accessed accounts, logs) is tracked by the
               EVMC host, refunds specifically must be tracked by an EVMC-compliant interpreter. *)
      ; host : Host.t }
    [@@deriving lens {submodule = true; prefix = true}]
    include TLens

    let initial ~host ~gas ~memory_capacity =
      { gas
      ; pc = U256.zero
      ; memory = Memory.empty ~memory_capacity
      ; stack = []
      ; stack_depth = 0
      ; output_buffer = Bytes.empty
      ; gas_refund = Integer.zero
      ; host }
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
  end

  let max_stack_depth = 1024

  (* Monad §TODO: maximum contract code size is larger than Ethereum. *)
  let max_code_size = 128 * 1024
  let max_init_code_size = 2 * max_code_size

  let trace ?(print = Params.trace) msg =
    if print then (
      Format.print_string (msg ()) ;
      Format.print_flush () )
    else ()

  module Address = Chain.Ethereum.Address

  module M = struct
    include Monad.Result_state (struct
      type state = MachineState.t
      type error = Evmc.Result.StatusCode.t
    end)

    module HostAPI = struct
      module Base = Host

      let host_trace ?print msg = trace ?print (fun () -> Format.sprintf "[OCaml] Host call: %s\n" (msg ()))

      let lift (fn : Host.t -> 'a * Host.t) : 'a t =
       fun state ->
        let result, host = fn state.host in
        (Ok result, {state with host})

      (* TODO: trace other API calls. *)
      let account_exists addr =
        host_trace (fun () -> Format.sprintf "account_exists %s" (Address.to_short_hex_string addr)) ;
        lift (Base.account_exists addr)

      let get_storage addr key =
        host_trace (fun () ->
            Format.sprintf "get_storage %s %s" (Address.to_short_hex_string addr)
              (B32.to_short_hex_string key) ) ;
        lift (Base.get_storage addr key)

      let set_storage addr key v =
        host_trace (fun () ->
            Format.sprintf "set_storage %s %s %s" (Address.to_short_hex_string addr)
              (B32.to_short_hex_string key) (B32.to_short_hex_string v) ) ;
        lift (Base.set_storage addr key v)

      let get_balance addr =
        host_trace (fun () -> Format.sprintf "get_balance %s" (Address.to_short_hex_string addr)) ;
        lift (Base.get_balance addr)

      let access_account addr =
        host_trace (fun () -> Format.sprintf "access_account %s" (Address.to_short_hex_string addr)) ;
        lift (Base.access_account addr)

      let access_storage addr key =
        host_trace (fun () ->
            Format.sprintf "access_storage %s %s" (Address.to_short_hex_string addr)
              (B32.to_short_hex_string key) ) ;
        lift (Base.access_storage addr key)

      let get_code_size addr =
        host_trace (fun () -> Format.sprintf "get_code_size %s" (Address.to_short_hex_string addr)) ;
        lift (Base.get_code_size addr)

      let get_code_hash addr =
        host_trace (fun () -> Format.sprintf "get_code_hash %s" (Address.to_short_hex_string addr)) ;
        lift (Base.get_code_hash addr)

      let copy_code addr ~offset ~size =
        host_trace (fun () ->
            Format.sprintf "copy_code %s %d %d" (Address.to_short_hex_string addr) offset size ) ;
        lift (Base.copy_code addr ~offset ~size)

      let get_block_hash id =
        host_trace (fun () -> Format.sprintf "get_block_hash %Ld" id) ;
        lift (Base.get_block_hash id)

      let call (msg : Evmc.Message.t) =
        host_trace (fun () ->
            Format.sprintf "call to %s (gas = %Ld)" (Address.to_short_hex_string msg.recipient) msg.gas ) ;
        let$ result = lift (Base.call msg) in
        trace (fun () ->
            Format.sprintf "\tReturned %s\n" (Evmc.Result.StatusCode.to_string result.status_code) ) ;
        trace (fun () -> Format.sprintf "\tOutput buffer %s\n" (Bytes.to_hex_string result.output_data)) ;
        return result

      let selfdestruct ~address ~beneficiary =
        host_trace (fun () ->
            Format.sprintf "selfdestruct ~address:%s ~beneficiary:%s"
              (Address.to_short_hex_string address)
              (Address.to_short_hex_string beneficiary) ) ;
        lift (Base.selfdestruct ~address ~beneficiary)

      let emit_log addr ~data ~topics =
        host_trace (fun () ->
            Format.sprintf "emit_log %s %s [%s]" (Address.to_short_hex_string addr)
              (Bytes.to_short_hex_string data)
              (List.fold_left
                 (fun acc topic -> Format.sprintf "%s, %s" acc (B32.to_short_hex_string topic))
                 "" topics ) ) ;
        lift (Base.emit_log addr ~data ~topics)

      let get_transient_storage addr key =
        host_trace (fun () ->
            Format.sprintf "get_transient_storage %s %s" (Address.to_short_hex_string addr)
              (B32.to_short_hex_string key) ) ;
        lift (Base.get_transient_storage addr key)

      let set_transient_storage addr key v =
        host_trace (fun () ->
            Format.sprintf "set_transient_storage %s %s %s" (Address.to_short_hex_string addr)
              (B32.to_short_hex_string key) (B32.to_short_hex_string v) ) ;
        lift (Base.set_transient_storage addr key v)
    end
  end
  open M

  (* Frequently used helpers are written in direct style for performance. *)
  let spend (amount : Gas.t) : unit M.t =
   fun s ->
    if Gas.(s.gas < amount) then (Error Out_of_gas, s) else (Ok (), {s with gas = Gas.(s.gas - amount)})

  let push (x : U256.t) : unit M.t =
   fun s ->
    if s.stack_depth >= max_stack_depth then (Error Stack_overflow, s)
    else (Ok (), {s with stack = x :: s.stack; stack_depth = s.stack_depth + 1})
  let pop : U256.t M.t =
   fun s ->
    match s.stack with
    | x0 :: tl -> (Ok x0, {s with stack = tl; stack_depth = s.stack_depth - 1})
    | _ -> (Error Stack_underflow, s)

  let pop2 : (U256.t * U256.t) M.t =
   fun s ->
    match s.stack with
    | x0 :: x1 :: tl -> (Ok (x0, x1), {s with stack = tl; stack_depth = s.stack_depth - 2})
    | _ -> (Error Stack_underflow, s)

  let pop3 : (U256.t * U256.t * U256.t) M.t =
   fun s ->
    match s.stack with
    | x0 :: x1 :: x2 :: tl -> (Ok (x0, x1, x2), {s with stack = tl; stack_depth = s.stack_depth - 3})
    | _ -> (Error Stack_underflow, s)

  let update_pc_and_continue (f : U256.t -> U256.t) : bool M.t =
   fun s ->
    let s = {s with pc = f s.pc} in
    (Ok true, s)

  let increase_pc_and_continue : bool M.t = update_pc_and_continue U256.(( + ) one)

  let finish_execution ~return_output : bool M.t =
    let$ () = when_ (not return_output) (MachineState.output_buffer := Bytes.empty) in
    return false

  type opcode_impl = bool M.t

  module Executor (C : sig
    val execution_environment : ExecutionEnvironment.t
  end) =
  struct
    open C

    open MachineState
    open ExecutionEnvironment

    let jump_destinations : U256.Set.t =
      let rec loop i valid_destinations =
        if i >= Bytes.length execution_environment.bytecode then valid_destinations
        else
          match execution_environment.bytecode.[i] with
          | '\x5b' -> loop (i + 1) U256.(Set.add ~$i valid_destinations)
          | '\x60' .. '\x7f' as opcode ->
              let push_bytes = Char.code opcode - 0x60 + 1 in
              loop (i + 1 + push_bytes) valid_destinations
          | _ -> loop (i + 1) valid_destinations
      in
      loop 0 U256.Set.empty

    let check_write_permissions =
      let can_write = execution_environment.write_permission in
      if can_write then return () else fail Static_mode_violation

    let check_jump_destination (destination : U256.t) =
      if U256.Set.mem destination jump_destinations then return () else fail Bad_jump_destination

    let self : Address.t = execution_environment.address

    (* General undefined opcode *)
    let undefined : opcode_impl = fail Undefined_instruction

    (* Designated invalid opcode 0xfe *)
    let invalid : opcode_impl = fail Invalid_instruction

    let stop =
      (* Stack *)
      (* Gas *)
      (* Operation *)
      (* PC *)
      finish_execution ~return_output:false

    let add =
      (* Stack *)
      let$ x, y = pop2 in

      (* Gas *)
      let$ () = spend Gas.very_low in

      (* Operation *)
      let$ () = push U256.(x + y) in

      (* PC *)
      increase_pc_and_continue

    let mul =
      (* Stack *)
      let$ x, y = pop2 in

      (* Gas *)
      let$ () = spend Gas.low in

      (* Operation *)
      let$ () = push U256.(x * y) in

      (* PC *)
      increase_pc_and_continue

    let sub =
      (* Stack *)
      let$ x, y = pop2 in

      (* Gas *)
      let$ () = spend Gas.very_low in

      (* Operation *)
      let$ () = push U256.(x - y) in

      (* PC *)
      increase_pc_and_continue

    let udiv =
      (* Stack *)
      let$ dividend, divisor = pop2 in

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
      let$ x, y = pop2 in

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
      let$ x, y, m = pop3 in

      (* Gas *)
      let$ () = spend Gas.mid in

      (* Operation *)
      let$ () = push U256.(if m = zero then zero else addmod x y m) in

      (* PC *)
      increase_pc_and_continue

    let mulmod =
      (* Stack *)
      let$ x, y, m = pop3 in

      (* Gas *)
      let$ () = spend Gas.mid in

      (* Operation *)
      let$ () = push U256.(if m = zero then zero else mulmod x y m) in

      (* PC *)
      increase_pc_and_continue

    let exp =
      (* Stack *)
      let$ base, exponent = pop2 in

      (* Gas *)
      let exponent_bytes = Uint.of_int (U256.significant_bytes exponent) in
      let$ () = spend Gas.(exp_base_cost + (exp_cost_per_byte * exponent_bytes)) in

      (* Operation *)
      let$ () = push U256.(exp base exponent) in

      (* PC *)
      increase_pc_and_continue

    let signextend =
      (* Stack *)
      let$ byte_index, x = pop2 in

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
      let$ x, y = pop2 in

      (* Gas *)
      let$ () = spend Gas.very_low in

      (* Operation *)
      let$ () = push U256.(of_bool (x < y)) in

      (* PC *)
      increase_pc_and_continue

    let gt =
      (* Stack *)
      let$ x, y = pop2 in

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
      let$ x, y = pop2 in

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
      let$ x, y = pop2 in

      (* Gas *)
      let$ () = spend Gas.very_low in

      (* Operation *)
      let$ () = push U256.(logand x y) in

      (* PC *)
      increase_pc_and_continue

    let bitwise_or =
      (* Stack *)
      let$ x, y = pop2 in

      (* Gas *)
      let$ () = spend Gas.very_low in

      (* Operation *)
      let$ () = push U256.(logor x y) in

      (* PC *)
      increase_pc_and_continue

    let bitwise_xor =
      (* Stack *)
      let$ x, y = pop2 in

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
      let$ index_be, x = pop2 in

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
      let$ shift_amount, value = pop2 in

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
        let$ current = !memory in
        let current_active_words = Memory.active_words current in
        let$ extended = Memory.extend_to ~start ~size_bytes current |> Option.or_fail Out_of_memory in
        let$ () = memory := extended in
        let$ new_active_words = Memory.active_words <$> !memory in
        if Uint.(current_active_words >= new_active_words) then return Uint.zero
        else
          return
            Gas.(
              memory_cost Params.revision new_active_words - memory_cost Params.revision current_active_words )

    let keccak =
      (* Stack *)
      let$ start, size_bytes = pop2 in

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
      let$ bytes = Memory.read_block_at start size_bytes <$> !memory in
      let$ () = push (U256.of_repr (Crypto.keccak_256 bytes)) in

      (* PC *)
      increase_pc_and_continue

    let fetch_environment_variable_opcode_impl (value : U256.t) =
      (* Stack *)
      (* Gas *)
      let$ () = spend Gas.base in

      (* Operation *)
      let$ () = push value in

      (* PC *)
      increase_pc_and_continue

    let fetch_environment_variable_opcode_impl' (value : U256.t M.t) =
      (* Stack *)
      (* Gas *)
      let$ () = spend Gas.base in

      (* Operation *)
      let$ value = value in
      let$ () = push value in

      (* PC *)
      increase_pc_and_continue

    let address = fetch_environment_variable_opcode_impl (Address.to_u256 execution_environment.address)
    let origin = fetch_environment_variable_opcode_impl (Address.to_u256 execution_environment.origin)
    let caller = fetch_environment_variable_opcode_impl (Address.to_u256 execution_environment.sender)
    let callvalue = fetch_environment_variable_opcode_impl execution_environment.value

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
      let data = execution_environment.data in
      let$ () =
        push
          ( match U256.to_int_opt i with
          | None -> U256.zero (* Index exceeds max theoretical data size *)
          | Some i -> U256.of_repr (B32.sub_with_zero_padding data i) )
      in

      (* PC *)
      increase_pc_and_continue

    let calldatasize =
      fetch_environment_variable_opcode_impl (U256.of_int (Bytes.length execution_environment.data))

    let codesize =
      fetch_environment_variable_opcode_impl (U256.of_int (Bytes.length execution_environment.bytecode))

    let copy_input_data_opcode_impl data =
      (* Stack *)
      let$ dst_start, src_start, size_bytes = pop3 in

      (* Gas *)
      let n_words = U256.(to_uint (bytes_to_whole_words size_bytes)) in
      let$ memory_extension_gas = extend_memory_to ~start:dst_start ~size_bytes in
      let$ () = spend Gas.(very_low + (n_words * copy_cost_per_word) + memory_extension_gas) in

      (* Operation *)
      let block =
        match (U256.to_int_opt src_start, U256.to_int_opt size_bytes) with
        | Some src_start, Some size -> Bytes.sub_with_zero_padding data src_start size
        | _, Some size -> Bytes.make size '\x00'
        | _, None -> assert false
      in
      let$ () = update_field memory (Memory.write_block_at dst_start block) in

      (* PC *)
      increase_pc_and_continue

    let calldatacopy = copy_input_data_opcode_impl execution_environment.data

    let codecopy = copy_input_data_opcode_impl execution_environment.bytecode

    let gasprice = fetch_environment_variable_opcode_impl execution_environment.price

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
      let$ dst_start, src_start, size_bytes = pop3 in

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
      let$ () = update_field memory (Memory.write_block_at dst_start block) in

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
      (* TODO: this needs a legit implementation. *)
      fetch_environment_variable_opcode_impl' (U256.of_int <$> (Bytes.length <$> !output_buffer))

    let returndatacopy =
      (* Stack *)
      let$ dst_start, src_start, size_bytes = pop3 in

      (* Gas *)
      let$ data = !output_buffer in
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
      let$ () = update_field memory (Memory.write_block_at dst_start block) in

      (* PC *)
      increase_pc_and_continue

    let blockhash =
      (* Stack *)
      let$ block_num = U256.to_uint <$> pop in

      (* Gas *)
      let$ () = spend Gas.block_hash_cost in

      (* Operation *)
      let current_block_num = U256.to_uint execution_environment.header.number in
      let$ hash =
        if Uint.(current_block_num <= block_num || current_block_num > block_num + ~$256) then
          return U256.zero
        else
          let$ hash = HostAPI.get_block_hash (Uint.to_int64 block_num) in
          match hash with Some hash -> return (U256.of_repr hash) | None -> fail Argument_out_of_range
      in
      let$ () = push hash in

      (* PC *)
      increase_pc_and_continue

    let coinbase =
      fetch_environment_variable_opcode_impl (Address.to_u256 execution_environment.header.coinbase)

    let timestamp = fetch_environment_variable_opcode_impl execution_environment.header.timestamp

    let number = fetch_environment_variable_opcode_impl execution_environment.header.number

    let prevrandao = fetch_environment_variable_opcode_impl execution_environment.header.prev_randao

    let gaslimit = fetch_environment_variable_opcode_impl execution_environment.header.gas_limit

    (* The yellow paper gets the chain ID directly as the ambient variable β, as opposed to fetching it
     from a specific field in the execution environment. The executable specs, on the other hand, does get
     it from the block environment. *)
    let chainid = fetch_environment_variable_opcode_impl execution_environment.header.chain_id

    let selfbalance =
      (* Stack *)
      (* Gas *)
      let$ () = spend Gas.low in

      (* Operation *)
      let$ balance = HostAPI.get_balance self in
      let$ () = push balance in

      (* PC *)
      increase_pc_and_continue

    let basefee = fetch_environment_variable_opcode_impl execution_environment.header.base_fee

    (* EIP-4844 *)
    let blobhash =
      (* Stack *)
      let$ index = pop in

      (* Gas *)
      let$ () = spend Gas.very_low in

      (* Operation *)
      let hashes = execution_environment.blob_versioned_hashes in
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
      let$ () = push execution_environment.blob_base_fee in

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
      let$ here = U256.to_int <$> !pc in
      let code = execution_environment.bytecode in
      let$ () = push (U256.of_uint_exn (Uint.of_bytes_be (Bytes.sub_with_zero_padding code (here + 1) i))) in

      (* PC *)
      update_pc_and_continue (fun pc -> U256.(pc + one + ~$i))

    let dup i =
      assert (i >= 1) ;
      assert (i <= 16) ;
      (* Stack *)
      let$ nth_elt =
        !stack |> M.fmap (fun l -> List.nth_opt l (i - 1)) >>= M.Option.or_fail Stack_underflow
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
      let$ nth, stack' = !stack |> M.fmap (replace_list (i - 1) first) >>= Option.or_fail Stack_underflow in
      let$ () = stack := stack' in

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
      let$ mem = Memory.read_word_at pos <$> !memory in
      let$ () = push mem in

      (* PC *)
      increase_pc_and_continue

    let mstore =
      (* Stack *)
      let$ pos, value = pop2 in

      (* Gas *)
      let$ memory_extension_gas = extend_memory_to ~start:pos ~size_bytes:U256.(~$32) in
      let$ () = spend Gas.(very_low + memory_extension_gas) in

      (* Operation *)
      let$ () = update_field memory (Memory.write_word_at pos value) in

      (* PC *)
      increase_pc_and_continue

    let mstore8 =
      (* Stack *)
      let$ pos, value = pop2 in

      (* Gas *)
      let$ memory_extension_gas = extend_memory_to ~start:pos ~size_bytes:U256.one in
      let$ () = spend Gas.(very_low + memory_extension_gas) in

      (* Operation *)
      let$ () = update_field memory (Memory.write_byte_at pos U256.(byte ~index_le:0 value)) in

      (* PC *)
      increase_pc_and_continue

    let sload =
      (* Stack *)
      let$ key = pop in

      (* Gas *)
      let$ access = HostAPI.access_storage self (U256.to_repr key) in
      let$ () = spend Gas.(match access with `Cold -> cold_sload_cost | `Warm -> warm_access_cost) in

      (* Operation *)
      let$ value = U256.of_repr <$> HostAPI.get_storage self (U256.to_repr key) in
      let$ () = push value in

      (* PC *)
      increase_pc_and_continue

    let sstore =
      (* Stack *)
      let$ key, value' = pop2 in

      (* Gas *)
      (* Protection against reentrancy attacks, see EIP-2200 *)
      let$ current_gas = !gas in
      let$ () = when_ Gas.(current_gas <= call_stipend) (fail Out_of_gas) in

      (* Operation *)
      (* Exceptionally, this is done before spending gas, as we use the host StorageStatus.t to calculate gas
       costs. *)
      let$ () = check_write_permissions in

      let$ access = HostAPI.access_storage self (U256.to_repr key) in
      let$ storage_status = HostAPI.set_storage self (U256.to_repr key) (U256.to_repr value') in

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
        update_field gas_refund (fun r -> Integer.(r + refund))
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
      let$ new_pc, condition = pop2 in

      (* Gas *)
      let$ () = spend Gas.high in

      (* Operation *)
      (* PC *)
      if U256.is_zero condition then increase_pc_and_continue
      else
        let$ () = check_jump_destination new_pc in
        update_pc_and_continue (fun _ -> new_pc)

    let pc_ = fetch_environment_variable_opcode_impl' !pc

    let msize =
      fetch_environment_variable_opcode_impl'
        (let$ memory = !memory in
         return (U256.of_uint_truncating Uint.(~$32 * Memory.active_words memory)) )

    let gas_ =
      (* Stack *)
      (* Gas *)
      let$ () = spend Gas.base in

      (* Operation *)
      let$ current_gas = !gas in
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
      let$ value = U256.of_repr <$> HostAPI.get_transient_storage self (U256.to_repr key) in
      let$ () = push value in

      (* PC *)
      increase_pc_and_continue

    let tstore =
      (* Stack *)
      let$ key, value = pop2 in

      (* Gas *)
      let$ () = spend Gas.warm_access_cost in

      (* Operation *)
      let$ () = check_write_permissions in

      let$ () = HostAPI.set_transient_storage self (U256.to_repr key) (U256.to_repr value) in

      (* PC *)
      increase_pc_and_continue

    (* EIP-5656. *)
    let mcopy =
      (* Stack *)
      let$ dst_start, src_start, size_bytes = pop3 in

      (* Gas *)
      let n_words = U256.(to_uint (bytes_to_whole_words size_bytes)) in
      let$ memory_extension_gas = extend_memory_to ~start:U256.(max src_start dst_start) ~size_bytes in
      let$ () = spend Gas.(very_low + (n_words * copy_cost_per_word) + memory_extension_gas) in

      (* Operation *)
      let$ block = Memory.read_block_at src_start size_bytes <$> !memory in
      let$ () = update_field memory (Memory.write_block_at dst_start block) in

      (* PC *)
      increase_pc_and_continue

    let log n_topics =
      assert (n_topics >= 0 && n_topics <= 4) ;
      (* Stack *)
      let$ start, size_bytes = pop2 in

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

      let$ data = Memory.read_block_at start size_bytes <$> !memory in
      let$ () = HostAPI.emit_log self ~data ~topics in

      (* PC *)
      increase_pc_and_continue

    let merge_child_gas_and_refund ~status_code ~gas_left ~gas_refund =
      let$ () = update_field gas (fun g -> Uint.(g + of_int64 gas_left)) in
      if status_code = Evmc.Result.StatusCode.Success then
        update_field MachineState.gas_refund (fun g -> Integer.(g + of_int64 gas_refund))
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
      let$ () = output_buffer := Bytes.empty in

      let new_depth = execution_environment.depth + 1 in
      if new_depth > max_stack_depth then
        let$ () = update_field gas (fun g -> Uint.(g + U256.to_uint call_gas)) in
        push U256.zero
      else
        let$ mem = !memory in
        let input_data = Memory.read_block_at input_start input_size mem in
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
              ; code = Bytes.empty
              ; memory_capacity = Uint.to_uint32 (Memory.available_memory_size mem) } )
        in
        let$ {status_code; gas_left; gas_refund; output_data; create_address} = HostAPI.call message in
        let$ () = merge_child_gas_and_refund ~status_code ~gas_left ~gas_refund in
        assert (Address.(zero = create_address)) ;

        let$ () = output_buffer := output_data in
        let$ () =
          let truncated_output =
            match U256.to_int_opt output_size with
            | None -> output_data
            | Some i -> Bytes.sub output_data 0 (min i (Bytes.length output_data))
          in
          update_field memory (Memory.write_block_at output_start truncated_output)
        in
        push (if status_code = Success then U256.one else U256.zero)

    let access_delegation (addr : Address.t) : delegation M.t =
      let$ code = HostAPI.copy_code addr ~offset:0 ~size:Delegation.eoa_delegated_code_length in
      match Delegation.get_delegated_address code with
      | None -> return (Direct {code})
      | Some code_address ->
          let$ delegation_access_gas = Gas.account_access_cost <$> HostAPI.access_account code_address in
          return (Delegated {code_address; delegation_access_gas})

    let generic_create_impl
        ~(kind : Evmc.Message.CallKind.t)
        ~(create2_salt : B32.t)
        ~(endowment : U256.t)
        ~(input_start : U256.t)
        ~(input_size_bytes : U256.t) =
      let$ () = when_ U256.(input_size_bytes > ~$max_init_code_size) (fail Out_of_gas) in

      let$ () = check_write_permissions in

      let new_depth = execution_environment.depth + 1 in

      let$ self_balance = HostAPI.get_balance self in
      if self_balance < endowment || new_depth > max_stack_depth then push U256.zero
      else
        let$ () =
          (* Monad §TODO: delegated EOAs cannot call CREATE/CREATE2. *)
          let$ delegation = access_delegation self in
          match delegation with Delegated _ -> fail Create_from_delegated_eoa | Direct _ -> return ()
        in
        let$ create_message_gas = Uint.minus_1_64th <$> !gas in
        let$ () = update_field gas (fun g -> Uint.(g - create_message_gas)) in

        let$ () = output_buffer := Bytes.empty in
        let$ mem = !memory in
        let call_data = Memory.read_block_at input_start input_size_bytes mem in

        let message =
          Evmc.(
            Message.
              { kind
              ; delegated = false
              ; static = false
              ; depth = Int32.of_int new_depth
              ; gas = Uint.to_int64 create_message_gas
              ; recipient = Address.zero
              ; sender = self
              ; input_data = call_data
              ; value = endowment
              ; create2_salt
              ; code_address = Address.zero
              ; code = Bytes.empty
              ; memory_capacity = Uint.to_uint32 (Memory.available_memory_size mem) } )
        in
        let$ {status_code; gas_left; gas_refund; output_data; create_address} = HostAPI.call message in
        let$ () = merge_child_gas_and_refund ~status_code ~gas_left ~gas_refund in
        if status_code = Evmc.Result.StatusCode.Success then
          let$ () = spend Gas.(code_deposit_per_byte * ~$(Bytes.length output_data)) in
          let$ () = output_buffer := Bytes.empty in
          push (Address.to_u256 create_address)
        else
          let$ () = output_buffer := output_data in
          push U256.zero

    let create =
      (* Stack *)
      let$ endowment, input_start, input_size_bytes = pop3 in

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
      let access_gas =
        match delegation with
        | Direct _delegation -> access_gas
        | Delegated {delegation_access_gas; _} -> Gas.(access_gas + delegation_access_gas)
      in

      let transfer_value = kind <> Evmc.Message.CallKind.DelegateCall && U256.(value <> zero) in

      let$ target_is_alive = HostAPI.account_exists recipient in
      let create_gas = Gas.(if transfer_value && not target_is_alive then new_account_cost else zero) in

      let transfer_gas = Gas.(if transfer_value then call_value else zero) in

      let$ gas_left = !MachineState.gas in
      let Gas.{caller_spent_gas; callee_available_gas} =
        Gas.call_gas ~transfer_value ~gas ~gas_left ~memory_cost:memory_extension_gas
          ~extra_cost:Uint.(access_gas + transfer_gas + create_gas)
      in

      let$ () = spend Gas.(caller_spent_gas + memory_extension_gas) in

      (* Operation *)
      let$ () = when_ transfer_value check_write_permissions in

      let in_static_context = not execution_environment.write_permission in
      let static = static_call || in_static_context in

      let$ self_balance = HostAPI.get_balance self in
      let call_depth = execution_environment.depth in
      let$ () =
        if (transfer_value && U256.(self_balance < value)) || call_depth >= max_stack_depth then
          let$ () = push U256.zero in
          let$ () = update_field MachineState.gas (fun g -> Uint.(g + callee_available_gas)) in
          output_buffer := Bytes.empty
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
    let$ (value, input_start, input_size) = pop3 in
    let$ (output_start, output_size) = pop2 in

    
    call_opcode_impl
      ~kind:Evmc.Message.CallKind.Call
      ~gas
      ~sender:self
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
    let$ (value, input_start, input_size) = pop3 in
    let$ (output_start, output_size) = pop2 in

    
    call_opcode_impl
      ~kind:Evmc.Message.CallKind.CallCode
      ~gas
      ~value
      ~sender:self
      ~recipient:self
      ~code_address
      ~input_start
      ~input_size
      ~output_start
      ~output_size
      ~static_call:false
  [@@ocamlformat "disable"]

    let return_ =
      (* Stack *)
      let$ start, size_bytes = pop2 in

      (* Gas *)
      let$ () =
        (* We do not spend gas when copying a zero-size return value *)
        when_
          U256.(size_bytes > zero)
          (let$ memory_extension_gas = extend_memory_to ~start ~size_bytes in
           spend memory_extension_gas )
      in

      (* Operation *)
      let$ result = Memory.read_block_at start size_bytes <$> !memory in
      let$ () = output_buffer := result in

      (* PC *)
      finish_execution ~return_output:true

    let delegatecall =
    (* Stack *)
    let$ gas = U256.to_uint <$> pop in
    let$ code_address = Address.of_u256_truncating <$> pop in
    let$ (input_start, input_size, output_start) = pop3 in
    let$ output_size = pop in

    let original_sender = execution_environment.sender in
    let original_value = execution_environment.value in

    

    call_opcode_impl ~kind:Evmc.Message.CallKind.DelegateCall
      ~gas
      ~sender:original_sender
      ~recipient:self
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
      let$ endowment, input_start, input_size_bytes = pop3 in
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
    let$ (input_start, input_size, output_start) = pop3 in
    let$ output_size = pop in

    
    call_opcode_impl
      ~kind:Evmc.Message.CallKind.Call
      ~gas
      ~sender:self
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
      let$ start, size_bytes = pop2 in

      (* Gas *)
      let$ () =
        (* We do not spend gas when copying a zero-size return value *)
        when_
          U256.(size_bytes > zero)
          (let$ memory_extension_gas = extend_memory_to ~start ~size_bytes in
           spend memory_extension_gas )
      in

      (* Operation *)
      let$ result = Memory.read_block_at start size_bytes <$> !memory in
      let$ () = output_buffer := result in

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
      let$ self_balance = HostAPI.get_balance self in
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
      let$ () = ignore <$> HostAPI.selfdestruct ~address:self ~beneficiary in

      (* PC *)
      finish_execution ~return_output:false

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
      if Params.trace then ( fun s ->
        Format.printf "PC: %s\n" (U256.to_string s.pc) ;
        Format.printf "Gas: %s\n" (Uint.to_string s.gas) ;
        Format.printf "Stack: \n" ;
        trace_stack s.stack ;
        Format.printf "Memory: \n" ;
        Memory.dump s.memory ;
        Format.print_flush () )
      else fun _ -> ()

    let rec run (s : MachineState.t) =
      (* The dispatch loop runs on each opcode so it's written in direct style for performance. *)
      trace_state s ;
      let pc = s.pc in
      let opcode =
        (* YP (157) *)
        match U256.to_int_opt pc with
        | Some pc when pc < Bytes.length execution_environment.bytecode ->
            Opcode.of_byte execution_environment.bytecode.[pc]
        | _ -> Opcode.Stop
      in
      trace (fun () ->
          let info = Opcode.info opcode in
          Format.sprintf "Executing opcode 0x%x(%s)\n" (Char.code info.byte) info.name ) ;
      let result, s = execute_opcode opcode s in
      match result with Ok continue -> if continue then run s else (Ok (), s) | Error err -> (Error err, s)
  end

  let execute (msg : Evmc.Message.t) (code : Bytes.t) : Host.t -> Evmc.Result.t * Host.t =
    trace (fun () -> "Start execution\n") ;
    trace (fun () -> Format.sprintf "Bytecode: %s\n" (Bytes.to_hex_string code)) ;
    let open Host in
    let open Monad.State (Host) in
    let$ tx_context = get_tx_context in
    let$ host = get in
    let module Exe = Executor (struct
      let execution_environment = ExecutionEnvironment.make tx_context msg code
    end) in
    let gas = Gas.of_uint64 msg.gas in
    let memory_capacity = Uint.of_uint32 msg.memory_capacity in
    let state = MachineState.initial ~host ~gas ~memory_capacity in
    let res, state = Exe.run state in
    trace (fun () -> "Finished execution\n") ;
    (* Propagate host updates back to the caller. *)
    let$ () = put state.host in
    return
      ( match res with
      | Ok () ->
          trace (fun () ->
              Format.sprintf "Execution OK, returning [[%s]]\n" (Bytes.to_hex_string state.output_buffer) ) ;
          Evmc.Result.
            { status_code = Success
            ; gas_left = Uint.to_uint64 state.gas
            ; gas_refund = Integer.to_int64 state.gas_refund
            ; output_data = state.output_buffer
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
                ; gas_left = Uint.to_uint64 state.gas
                ; gas_refund = 0L
                ; output_data = state.output_buffer
                ; create_address = Address.zero }
          | _ -> Evmc.Result.failure err ) )
end
