open Utils
open Numeric
open Lens.Infix

module Bytecode = struct
  type instr
end

module Make (Rev : Chain.Monad.Revision.SIG) (Host : Evmc.Host.SIG) = struct
  module Host = struct
    include Host
    include Monad.Make (Host)
  end
  module Traits = Chain.Monad.Traits (Rev)

  module Memory : sig
    type t
    val empty : t

    val read_block_at : U256.t -> U256.t -> t -> Bytes.t
    val read_word_at : U256.t -> t -> U256.t

    val write_block_at : U256.t -> Bytes.t -> t -> t
    val write_word_at : U256.t -> U256.t -> t -> t
    val write_byte_at : U256.t -> char -> t -> t

    (* For debugging purposes *)
    val dump : t -> unit
  end = struct
    type t = char U256.Map.t
    let read_block_at start size (mem : t) =
      let size = match U256.to_int_opt size with None -> assert false | Some sz -> sz in
      Bytes.init size (fun byte_i ->
          U256.Map.find_opt U256.(start + ~$byte_i) mem |> Option.value ~default:'\x00' )

    let read_word_at pos (mem : t) =
      let bytes_be =
        Bytes.init 32 (fun byte_i ->
            U256.Map.find_opt U256.(pos + ~$byte_i) mem |> Option.value ~default:'\x00' )
      in
      U256.of_bytes_be bytes_be

    let write_block_at (pos : U256.t) (bytes : Bytes.t) (mem : t) =
      Seq.take (Bytes.length bytes) (Seq.ints 0)
      |> Seq.map (fun i -> (U256.(pos + ~$i), bytes.[i]))
      |> fun entries -> U256.Map.add_seq entries mem

    let write_word_at pos w = write_block_at pos (U256.to_bytes_be w)

    let write_byte_at pos b (mem : t) = U256.Map.add pos b mem

    let empty = U256.Map.empty

    let dump mem =
      U256.Map.to_seq mem
      |> Seq.iter (fun (k, v) -> Format.printf "%s => 0x%x\n" (U256.to_short_hex_string k) (Char.code v))
  end

  module MachineState = struct
    (* YP 9.4.1 *)
    type t =
      { gas : U256.t (* mu_g *)
      ; pc : U256.t (* mu_pc *)
      ; memory : Memory.t (* mu_m *)
      ; active_memory_words : U256.t (* mu_i *)
      ; stack : U256.t list (* mu_s *)
      ; output_buffer : Bytes.t (* mu_o *)
      ; gas_refund : Uint.t
            (* A_r *)
            (*
             * Gas refund is not part of machine state as per YP, but EVMC boundaries are split oddly: though
             * most of the information in the Accrued Substate (accessed accounts, logs) is tracked by the
             * EVMC host, refunds specifically must be tracked by an EVMC-compliant interpreter
             *)
      }
    [@@deriving lens {submodule = true; prefix = true}]
    include TLens

    let initial =
      { gas = U256.zero
      ; pc = U256.zero
      ; memory = Memory.empty
      ; active_memory_words = U256.zero
      ; stack = []
      ; output_buffer = Bytes.empty
      ; gas_refund = Uint.zero }
  end
  open MachineState

  module ExecutionEnvironment = struct
    open Chain.Ethereum

    module ExecutionBlockHeader = struct
      (*
       * The Yellow Paper has an Ethereum block header as part of the execution (I_H), but the EVMC context
       * does not give us the full block header information, only those fields required for executing EVM
       * bytecode
       * Otherwise, this is as YP 4.4
       *)
      type t =
        { coinbase : Address.t (* H_c *)
        ; number : U256.t (* H_i *)
        ; timestamp : U256.t (* H_s *)
        ; gas_limit : U256.t (* H_l *)
        ; prev_randao : Address.t (* H_a *)
        ; base_fee : U256.t (* H_f *) }
      [@@deriving lens {submodule = true; prefix = true}]
      include TLens

      let of_tx_context (ctx : Evmc.TxContext.t) : t =
        { coinbase = ctx.block_coinbase
        ; number = U256.of_uint64 ctx.block_number
        ; timestamp = U256.of_uint64 ctx.block_timestamp
        ; gas_limit = U256.of_uint64 ctx.block_gas_limit
        ; prev_randao = ctx.block_prev_randao
        ; base_fee = ctx.block_base_fee }
    end
    include ExecutionBlockHeader

    (* YP 9.3 *)
    type t =
      { address : Address.t (* I_a *)
      ; origin : Address.t (* I_o *)
      ; price : U256.t (* I_p *)
      ; data : Bytes.t (* I_d *)
      ; sender : Address.t (* I_s *)
      ; value : U256.t (* I_w *)
      ; bytes : Bytes.t (* I_b *)
      ; header : ExecutionBlockHeader.t (* I_H *)
      ; depth : int
      ; write_permission : bool (* I_w *)
      ; blob_versioned_hashes : U256.t list (* EIP-4844 *)
      ; blob_base_fee : U256.t (* EIP-7516 *) }
    [@@deriving lens {submodule = true; prefix = true}]
    include TLens

    let make (ctx : Evmc.TxContext.t) (msg : Evmc.Message.t) : t =
      { address = msg.recipient
      ; origin = ctx.tx_origin
      ; price = ctx.tx_gas_price
      ; data = msg.input_data
      ; sender = msg.sender
      ; value = msg.value
      ; bytes = msg.code
      ; header = ExecutionBlockHeader.of_tx_context ctx
      ; depth = msg.depth
      ; write_permission = not (List.mem Evmc.Flags.Static msg.flags)
      ; blob_versioned_hashes = ctx.blob_hashes
      ; blob_base_fee = ctx.blob_base_fee }
  end
  open ExecutionEnvironment

  module Context = struct
    type t =
      { execution_environment : ExecutionEnvironment.t
      ; machine_state : MachineState.t
      ; jump_destinations : U256.Set.t (* D(c) *)
      ; initial_storage : U256.t U256.Map.t
            (* Cached initial values of storage cells modified in the transaction, to compute sstore costs *)
      }
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

    let make (ctx : Evmc.TxContext.t) (msg : Evmc.Message.t) : t =
      assert (U256.(ctx.chain_id = ~$Traits.chain_id)) ;
      { execution_environment = ExecutionEnvironment.make ctx msg
      ; machine_state = {MachineState.initial with gas = U256.of_uint64 msg.gas}
      ; jump_destinations = valid_jump_destinations msg.code
      ; initial_storage = U256.Map.empty }
  end
  open Context

  module St = Monad.State (Context)
  module StatusCode = Evmc.Result.StatusCode
  module Err = Monad.Result (Evmc.Result.StatusCode)

  module M = struct
    module StHost = St.Trans (Host)
    module ErrStHost = Err.Trans (StHost)

    include ErrStHost
    include St.Lift (ErrStHost) (StHost)
    module HostAPI = Evmc.Host.Lift (ErrStHost) (Evmc.Host.Lift (StHost) (Host))
  end
  open M

  module Ethereum = Chain.Ethereum
  module Address = Ethereum.Address

  let max_stack_depth = 1024
  let max_code_size = 0x6000
  let max_init_code_size = 2 * max_code_size

  let spend (amount : Uint.t) =
    let$ gas_remaining = !(machine_state |-- gas) in
    if Uint.(U256.to_unbounded gas_remaining < amount) then fail Out_of_gas
    else machine_state |-- gas := U256.(gas_remaining - of_unbounded amount)

  let check_write_permissions =
    let$ can_write = !(execution_environment |-- write_permission) in
    if can_write then return () else fail Static_mode_violation

  let check_jump_destination (destination : U256.t) =
    let$ valid_destinations = !jump_destinations in
    if U256.Set.mem destination valid_destinations then return () else fail Bad_jump_destination

  let self : Address.t M.t = !(execution_environment |-- address)

  let push (x : U256.t) : unit M.t =
    let$ s = !(machine_state |-- stack) in
    if List.length s >= max_stack_depth then fail Stack_overflow else machine_state |-- stack := x :: s

  let pop : U256.t M.t =
    let$ s = !(machine_state |-- stack) in
    match s with
    | [] -> fail Stack_underflow
    | hd :: tl ->
        let$ () = machine_state |-- stack := tl in
        return hd

  let finish_execution : bool M.t = return false
  let update_pc_and_continue (f : U256.t -> U256.t) : bool M.t =
    update_field (machine_state |-- pc) f >> return true
  let increase_pc_and_continue : bool M.t = update_pc_and_continue U256.(( + ) one)

  type opcode_impl = bool M.t

  (* General undefined opcode *)
  let undefined : opcode_impl = fail Undefined_instruction

  (* Enable an instruction only from a certain EVM revision *)
  let since rev impl = if Traits.evm_rev >= rev then impl else undefined

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
    let$ () = spend Gas.(base_exp_cost + (exp_cost_per_byte * exponent_bytes)) in

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
          | Some i when Stdlib.(i < 256) -> I256.as_unsigned (sign_extend i x)
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
    let$ byte_index = pop in
    let$ x = pop in

    (* Gas *)
    let$ () = spend Gas.very_low in

    (* Operation *)
    let$ () = push U256.(if byte_index >= ~$32 then zero else of_byte (byte (to_int byte_index) x)) in

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

  let shl = since Ethereum.Revision.Constantinople (logical_shift_opcode_impl U256.shift_left)
  let shr = since Ethereum.Revision.Constantinople (logical_shift_opcode_impl U256.shift_right)

  let sar =
    since Ethereum.Revision.Constantinople
      ((* Stack *)
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
       increase_pc_and_continue )

  let extend_memory_to (new_address : U256.t) : Uint.t M.t =
    let new_size = U256.(new_address + one) in
    let$ current_memory_words = !(machine_state |-- active_memory_words) in
    let new_memory_words = U256.bytes_to_whole_words new_size in
    if U256.(current_memory_words >= new_memory_words) then return Uint.zero
    else
      let$ () = machine_state |-- active_memory_words := new_memory_words in
      return Gas.(memory_cost new_memory_words - memory_cost current_memory_words)

  let keccak =
    (* Stack *)
    let$ input_start = pop in
    let$ input_size = pop in

    (* Gas *)
    let num_hashed_words = U256.bytes_to_whole_words input_size in
    let$ memory_extension_gas = extend_memory_to U256.(input_start + input_size) in
    let$ () =
      spend
        Gas.(
          base_keccak256_cost
          + (keccak256_cost_per_word * U256.to_unbounded num_hashed_words)
          + memory_extension_gas )
    in

    (* Operation *)
    let$ bytes = Memory.read_block_at input_start input_size <$> !(machine_state |-- memory) in
    let$ () = push (Crypto.keccak_256 bytes) in

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
        | Some i -> U256.of_bytes_be (Bytes.sub_with_zero_padding data i 32) )
    in

    (* PC *)
    increase_pc_and_continue

  let calldatasize =
    (* Stack *)
    (* Gas *)
    let$ () = spend Gas.base in

    (* Operation *)
    let$ data = !(execution_environment |-- data) in
    let$ () = push U256.(of_int (Bytes.length data)) in

    (* PC *)
    increase_pc_and_continue

  let codesize =
    (* Stack *)
    (* Gas *)
    let$ () = spend Gas.base in

    (* Operation *)
    let$ size = Bytes.length <$> !(execution_environment |-- bytes) in
    let$ () = push (U256.of_int size) in

    (* PC *)
    increase_pc_and_continue

  let copy_input_data_opcode_impl data_location =
    (* Stack *)
    let$ dst_start = pop in
    let$ src_start = pop in
    let$ size = pop in

    (* Gas *)
    let n_words = U256.(to_unbounded (bytes_to_whole_words size)) in
    let$ memory_extension_gas = extend_memory_to U256.(dst_start + size) in
    let$ () = spend Gas.(very_low + (n_words * word_copy_cost) + memory_extension_gas) in

    (* Operation *)
    let$ data = !data_location in
    let block =
      match (U256.to_int_opt src_start, U256.to_int_opt size) with
      | Some src_start, Some size -> Bytes.sub_with_zero_padding data src_start size
      | _, Some size -> Bytes.make size '\x00'
      | _, None -> assert false
    in
    let$ () = update_field (machine_state |-- memory) (Memory.write_block_at dst_start block) in

    (* PC *)
    increase_pc_and_continue

  let calldatacopy = copy_input_data_opcode_impl (execution_environment |-- data)

  let codecopy = copy_input_data_opcode_impl (execution_environment |-- bytes)

  let gasprice = fetch_environment_variable_opcode_impl (execution_environment |-- price).get

  let extcodesize =
    (* Stack *)
    let$ address = Address.of_u256_truncating <$> pop in

    (* Gas *)
    let$ access_gas = Gas.account_access_cost <$> HostAPI.access_account address in
    let$ () = spend access_gas in

    (* Operation *)
    let$ size = HostAPI.get_code_size address in
    let$ () = push size in

    (* PC *)
    increase_pc_and_continue

  let extcodecopy =
    (* Stack *)
    let$ address = Address.of_u256_truncating <$> pop in
    let$ dst_start = pop in
    let$ src_start = pop in
    let$ size = pop in

    (* Gas *)
    let$ access_gas = Gas.account_access_cost <$> HostAPI.access_account address in
    let n_words = U256.(to_unbounded (bytes_to_whole_words size)) in
    let$ memory_extension_gas = extend_memory_to U256.(dst_start + size) in
    let$ () = spend Gas.(very_low + (n_words * word_copy_cost) + memory_extension_gas + access_gas) in

    (* Operation *)
    let$ data = HostAPI.copy_code address in
    let block =
      match (U256.to_int_opt src_start, U256.to_int_opt size) with
      | Some src_start, Some size -> Bytes.sub_with_zero_padding data src_start size
      | _, Some size -> Bytes.make size '\x00'
      | _, None -> assert false
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
    let$ hash = HostAPI.get_code_hash address in
    let$ () = push hash in

    (* PC *)
    increase_pc_and_continue

  let returndatasize =
    fetch_environment_variable_opcode_impl (fun ctx ->
        U256.of_int (Bytes.length ctx.machine_state.output_buffer) )

  let returndatacopy =
    (* Stack *)
    let$ dst_start = pop in
    let$ src_start = pop in
    let$ size = pop in

    (* Gas *)
    let n_words = U256.(to_unbounded (bytes_to_whole_words size)) in
    let$ memory_extension_gas = extend_memory_to U256.(dst_start + size) in
    let$ () = spend Gas.(very_low + (n_words * word_copy_cost) + memory_extension_gas) in

    (* Operation *)
    let$ data = !(machine_state |-- output_buffer) in
    (* Unlike similar opcodes, returndatacopy fails on out-of-bounds memory access *)
    (* YP (158) *)
    let$ src_start, size =
      match (U256.to_int_opt src_start, U256.to_int_opt size) with
      | None, _ | _, None -> fail Invalid_memory_access
      | Some start, Some sz when start + sz >= Bytes.length data -> fail Invalid_memory_access
      | Some start, Some sz -> return (start, sz)
    in
    let block = Bytes.sub data src_start size in
    let$ () = update_field (machine_state |-- memory) (Memory.write_block_at dst_start block) in

    (* PC *)
    increase_pc_and_continue

  let blockhash =
    (* Stack *)
    let$ block_num = pop in

    (* Gas *)
    let$ () = spend Gas.block_hash_cost in

    (* Operation *)
    let$ current_block_num = !(execution_environment |-- header |-- number) in
    let$ hash =
      if U256.(current_block_num <= block_num || current_block_num - ~$256 > block_num) then return U256.zero
      else HostAPI.get_block_hash block_num
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
    fetch_environment_variable_opcode_impl (fun ctx ->
        Address.to_u256 ctx.execution_environment.header.prev_randao )

  let gaslimit = fetch_environment_variable_opcode_impl (execution_environment |-- header |-- gas_limit).get

  (*
   * The yellow paper gets the chain ID directly as the ambient variable Beta, as opposed to fetching it
   * from a specific field in the execution environment. The executable specs, on the other hand, does get
   * it from an environment field
   *)
  let chainid = fetch_environment_variable_opcode_impl (fun _ -> U256.of_int Traits.chain_id)

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

  let basefee = fetch_environment_variable_opcode_impl (execution_environment |-- header |-- gas_limit).get

  (* EIP-4844 *)
  let blobhash =
    since Chain.Ethereum.Revision.Cancun
      ((* Stack *)
       let$ index = pop in

       (* Gas *)
       let$ () = spend Gas.very_low in

       (* Operation *)
       let$ hashes = !(execution_environment |-- blob_versioned_hashes) in
       let hash =
         match U256.to_int_opt index with
         | None -> U256.zero
         | Some i -> Option.value ~default:U256.zero (List.nth_opt hashes i)
       in
       let$ () = push hash in

       (* PC *)
       increase_pc_and_continue )

  (* EIP-7516 *)
  let blobbasefee =
    since Chain.Ethereum.Revision.Cancun
      ((* Stack *)
       (* Gas *)
       let$ () = spend Gas.base in

       (* Operation *)
       let$ fee = !(execution_environment |-- blob_base_fee) in
       let$ () = push fee in

       (* PC *)
       increase_pc_and_continue )

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
    let$ code = !(execution_environment |-- bytes) in
    let$ () = push (U256.of_bytes_be (Bytes.sub_with_zero_padding code (here + 1) i)) in

    (* PC *)
    update_pc_and_continue (fun pc -> U256.(pc + one + ~$i))

  let dup i =
    assert (i >= 1) ;
    assert (i <= 16) ;
    (* Stack *)
    let$ nth_elt =
      !(machine_state |-- stack)
      |> M.fmap (fun l -> List.nth_opt l (i - 1))
      >>= Option.or_fail Stack_underflow
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
      !(machine_state |-- stack) |> M.fmap (replace_list i first) >>= Option.or_fail Stack_underflow
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
    let$ memory_extension_gas = extend_memory_to U256.(pos + ~$31) in
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
    let$ memory_extension_gas = extend_memory_to U256.(pos + ~$31) in
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
    let$ memory_extension_gas = extend_memory_to pos in
    let$ () = spend Gas.(very_low + memory_extension_gas) in

    (* Operation *)
    let$ () = update_field (machine_state |-- memory) (Memory.write_byte_at pos U256.(byte 0 value)) in

    (* PC *)
    increase_pc_and_continue

  let sload =
    (* Stack *)
    let$ key = pop in

    (* Gas *)
    let$ self_addr = self in
    let$ access = HostAPI.access_storage self_addr key in
    let$ () = spend Gas.(match access with `Cold -> cold_sload_cost | `Warm -> warm_access_cost) in

    (* Operation *)
    let$ value = HostAPI.get_storage self_addr key in
    let$ () = push value in

    (* PC *)
    increase_pc_and_continue

  let sstore =
    (* Stack *)
    let$ key = pop in
    let$ value' = pop in

    (* Gas *)
    let$ self_addr = self in
    let$ access = HostAPI.access_storage self_addr key in
    let$ value = HostAPI.get_storage self_addr key in
    let$ value0 = !(initial_storage |-- U256.Map.at key |-- Lens.get_or_default value) in
    (*
     * If the storage slot had already been written to, then initial_storage contained an entry for it and so
     * this code does not change its value. If it had not been written to, then we store the value we get from
     * storage, before the first update
     *)
    let$ () = initial_storage |-- U256.Map.at key := Some value0 in
    let access_gas = Gas.(match access with `Warm -> zero | `Cold -> cold_sload_cost) in
    let update_gas =
      match () with
      | () when U256.(value = value' || value0 <> value) -> Gas.warm_access_cost
      | () when U256.(value <> value' && value0 = value && value0 = zero) -> Gas.sset_cost
      | () when not U256.(value <> value' && value0 = value && value0 <> zero) -> assert false
      | () -> Gas.sreset_cost
    in
    let$ () = spend Gas.(access_gas + update_gas) in

    (* Operation *)
    let$ () = check_write_permissions in
    let$ () = HostAPI.set_storage self_addr key value' in
    (* The refund here can be negative as we may be undoing a previous positive refund *)
    let refund : Integer.t =
      match () with
      | () when U256.(value <> value' && value0 = value && value' = zero) -> Gas.(as_signed sclear_refund)
      | () when U256.(value <> value' && value0 <> value) ->
          let r_dirtyclear =
            match () with
            | () when U256.(value0 <> zero && value = zero) -> Integer.(zero - Gas.(as_signed sclear_refund))
            | () when U256.(value0 <> zero && value' = zero) -> Gas.(as_signed sclear_refund)
            | () -> Integer.zero
          in
          let r_dirtyreset =
            match () with
            | () when U256.(value0 = value' && value0 = zero) ->
                Integer.(Gas.(as_signed sset_cost) - Gas.(as_signed warm_access_cost))
            | () when U256.(value0 = value' && value0 <> zero) ->
                Integer.(Gas.(as_signed sreset_cost) - Gas.(as_signed warm_access_cost))
            | () -> Integer.zero
          in
          Integer.(r_dirtyclear + r_dirtyreset)
      | () -> Integer.zero
    in
    let$ () =
      (* Overall gas refund is non-negative, but we have to do signed addition here *)
      update_field (machine_state |-- gas_refund) (fun r ->
          Integer.(as_unsigned_exn (Uint.as_signed r + refund)) )
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
    fetch_environment_variable_opcode_impl (fun ctx -> U256.(~$8 * ctx.machine_state.active_memory_words))

  let gas_ =
    (* Stack *)
    (* Gas *)
    let$ () = spend Gas.very_low in

    (* Operation *)
    let$ current_gas = !(machine_state |-- gas) in
    let$ () = push current_gas in

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
    let$ value = HostAPI.get_transient_storage key in
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
    let$ () = HostAPI.set_transient_storage key value in

    (* PC *)
    increase_pc_and_continue

  let mcopy =
    (* Stack *)
    let$ dst_start = pop in
    let$ src_start = pop in
    let$ size = pop in

    (* Gas *)
    let n_words = U256.(to_unbounded (bytes_to_whole_words size)) in
    let copy_cost = Gas.(n_words * word_copy_cost) in
    let$ memory_expansion_cost = extend_memory_to U256.(max src_start dst_start + size) in
    let$ () = spend Gas.(very_low + copy_cost + memory_expansion_cost) in

    (* Operation *)
    let$ block = Memory.read_block_at src_start size <$> !(machine_state |-- memory) in
    let$ () = update_field (machine_state |-- memory) (Memory.write_block_at dst_start block) in

    (* PC *)
    increase_pc_and_continue

  let log n_topics =
    assert (n_topics >= 0 && n_topics <= 4) ;
    (* Stack *)
    let$ src_start = pop in
    let$ size = pop in

    let$ topics = List.mapM (List.of_seq Seq.(take n_topics (ints 0))) ~f:(fun _ -> pop) in

    (* Gas *)
    let$ memory_extension_gas = extend_memory_to U256.(src_start + size) in
    let$ () =
      spend
        Gas.(
          log_cost
          + (log_cost_per_byte * U256.to_unbounded size)
          + (log_cost_per_topic * ~$n_topics)
          + memory_extension_gas )
    in

    (* Operation *)
    let$ () = check_write_permissions in
    let$ self_addr = self in
    let$ data = Memory.read_block_at src_start size <$> !(machine_state |-- memory) in
    let$ () = HostAPI.emit_log self_addr ~data ~topics in

    (* PC *)
    increase_pc_and_continue

  let merge_child_gas_and_refund ~status_code ~gas_left ~gas_refund =
    let$ () = update_field (machine_state |-- gas) (fun g -> U256.(g + of_int64 gas_left)) in
    if status_code = Evmc.Result.StatusCode.Success then
      update_field (machine_state |-- MachineState.gas_refund) (fun g -> Uint.(g + of_int64 gas_refund))
    else return (assert (Int64.(gas_refund = zero)))

  let generic_call_impl
      ~(kind : Evmc.CallKind.t)
      ~(call_gas : U256.t)
      ~(value : U256.t)
      ~(sender : Address.t)
      ~(recipient : Address.t)
      ~(code_address : Address.t)
      ~(delegated : bool)
      ~(static : bool)
      ~(input_start : U256.t)
      ~(input_size : U256.t)
      ~(output_start : U256.t)
      ~(output_size : U256.t) =
    let$ () = machine_state |-- output_buffer := Bytes.empty in

    let$ new_depth = ( + ) 1 <$> !(execution_environment |-- depth) in
    if new_depth > max_stack_depth then
      let$ () = update_field (machine_state |-- gas) (fun g -> U256.(g + call_gas)) in
      push U256.zero
    else
      let$ input_data = Memory.read_block_at input_start input_size <$> !(machine_state |-- memory) in
      let$ code = HostAPI.copy_code code_address in
      let flags = Evmc.Flags.((if delegated then [Delegated] else []) @ if static then [Static] else []) in
      let message =
        Evmc.(
          Message.
            { kind
            ; flags
            ; depth = new_depth
            ; gas = U256.to_uint64 call_gas
            ; recipient
            ; sender
            ; input_data
            ; value
            ; create2_salt = U256.zero
            ; code_address
            ; code } )
      in
      let$ {status_code; gas_left; gas_refund; output_data; create_address} = HostAPI.call message in
      let$ () = merge_child_gas_and_refund ~status_code ~gas_left ~gas_refund in
      assert (Option.is_none create_address) ;

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
      ~(kind : Evmc.CallKind.t)
      ~(create2_salt : U256.t)
      ~(endowment : U256.t)
      ~(input_start : U256.t)
      ~(input_size : U256.t) =
    let$ () = when_ U256.(input_size > ~$max_init_code_size) (fail Out_of_gas) in

    let$ () = check_write_permissions in

    let$ new_depth = ( + ) 1 <$> !(execution_environment |-- depth) in
    let$ self_addr = self in
    let$ self_balance = HostAPI.get_balance self_addr in
    if self_balance < endowment || new_depth > max_stack_depth then push U256.zero
    else
      let$ create_message_gas = U256.minus_1_64th <$> !(machine_state |-- gas) in
      let$ () = update_field (machine_state |-- gas) (fun g -> U256.(g - create_message_gas)) in

      let$ () = machine_state |-- output_buffer := Bytes.empty in
      let$ call_data = Memory.read_block_at input_start input_size <$> !(machine_state |-- memory) in

      let message =
        Evmc.(
          Message.
            { kind
            ; flags = []
            ; depth = new_depth
            ; gas = U256.to_int64 create_message_gas
            ; recipient = Address.zero
            ; sender = self_addr
            ; input_data = Bytes.empty
            ; value = endowment
            ; create2_salt
            ; code_address = Address.zero
            ; code = call_data } )
      in
      let$ {status_code; gas_left; gas_refund; output_data; create_address} = HostAPI.call message in
      let$ () = merge_child_gas_and_refund ~status_code ~gas_left ~gas_refund in
      if status_code = Evmc.Result.StatusCode.Success then (
        assert (Option.is_some create_address) ;
        let$ () = machine_state |-- output_buffer := Bytes.empty in
        push (Address.to_u256 (Option.get create_address)) )
      else
        let$ () = machine_state |-- output_buffer := output_data in
        push U256.zero

  let create =
    (* Stack *)
    let$ endowment = pop in
    let$ input_start = pop in
    let$ input_size = pop in

    (* Gas *)
    let$ memory_extension_gas = extend_memory_to U256.(input_start + input_size) in
    let$ () =
      spend
        Gas.(
          memory_extension_gas
          + create_cost
          + (create_cost_per_initcode_word * U256.(to_unbounded (bytes_to_whole_words input_size))) )
    in

    (* Operation *)
    let$ () =
      generic_create_impl ~create2_salt:U256.zero ~kind:Evmc.CallKind.Create ~endowment ~input_start
        ~input_size
    in

    (* PC *)
    increase_pc_and_continue

  type delegation = {delegated : bool; code_address : Address.t; delegation_access_gas : Uint.t}

  let access_delegation (addr : Address.t) =
    let$ code = HostAPI.copy_code addr in
    match Delegation.get_delegated_address code with
    | None -> return {delegated = false; code_address = addr; delegation_access_gas = Gas.zero}
    | Some address ->
        let$ delegation_access_gas = Gas.account_access_cost <$> HostAPI.access_account address in
        return {delegated = true; code_address = address; delegation_access_gas}

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
    if U256.(value > zero) then assert (kind = Evmc.CallKind.Call || kind = Evmc.CallKind.CallCode) ;

    (* Gas *)
    let$ memory_extension_gas =
      extend_memory_to U256.(max (input_start + input_size) (output_start + output_size))
    in

    let$ access_gas = Gas.account_access_cost <$> HostAPI.access_account recipient in
    let$ {delegated; code_address; delegation_access_gas} = access_delegation code_address in
    let access_gas = Gas.(access_gas + delegation_access_gas) in

    let$ target_is_alive = HostAPI.account_exists recipient in
    if kind <> Evmc.CallKind.Call then assert target_is_alive ;
    let create_gas = Gas.(if U256.(value = zero) || target_is_alive then zero else new_account_cost) in

    let transfer_gas = Gas.(if U256.(value = zero) then zero else call_value) in

    let$ gas_left = U256.to_unbounded <$> !(machine_state |-- MachineState.gas) in
    let Gas.{caller_spent_gas; callee_available_gas} =
      Gas.call_gas ~value ~gas ~gas_left ~memory_cost:memory_extension_gas
        ~extra_cost:Uint.(access_gas + transfer_gas + create_gas)
    in

    let$ () = spend Gas.(caller_spent_gas + memory_extension_gas) in

    (* Operation *)
    let$ () = when_ U256.(value <> zero) check_write_permissions in

    let$ in_static_context = not <$> !(execution_environment |-- write_permission) in
    let static = static_call || in_static_context in

    let$ self_addr = self in
    let$ self_balance = HostAPI.get_balance self_addr in
    let$ () =
      if U256.(self_balance < value) then
        let$ () = push U256.zero in
        let$ () =
          update_field (machine_state |-- MachineState.gas) (fun g ->
              U256.(g + of_unbounded caller_spent_gas) )
        in
        machine_state |-- output_buffer := Bytes.empty
      else
        generic_call_impl ~kind
          ~call_gas:U256.(of_unbounded callee_available_gas)
          ~value ~sender ~recipient ~code_address ~input_start ~input_size ~output_start ~output_size
          ~delegated ~static
    in

    (* PC *)
    increase_pc_and_continue

  let call =
    (* Stack *)
    let$ gas = U256.to_unbounded <$> pop in
    let$ recipient = Address.of_u256_truncating <$> pop in
    let$ value = pop in
    let$ input_start = pop in
    let$ input_size = pop in
    let$ output_start = pop in
    let$ output_size = pop in

    let$ self_addr = self in
    call_opcode_impl
      ~kind:Evmc.CallKind.Call
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
    let$ gas = U256.to_unbounded <$> pop in
    let$ code_address = Address.of_u256_truncating <$> pop in
    let$ value = pop in
    let$ input_start = pop in
    let$ input_size = pop in
    let$ output_start = pop in
    let$ output_size = pop in

    let$ self_addr = self in
    call_opcode_impl
      ~kind:Evmc.CallKind.CallCode
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
    let$ pos = pop in
    let$ size = pop in

    (* Gas *)
    let$ () =
      (* We do not spend gas when copying a zero-size return value *)
      when_
        U256.(size > zero)
        (let$ memory_extension_gas = extend_memory_to U256.(pos + size - one) in
         spend memory_extension_gas )
    in

    (* Operation *)
    let$ result = Memory.read_block_at pos size <$> !(machine_state |-- memory) in
    let$ () = machine_state |-- output_buffer := result in

    (* PC *)
    finish_execution

  let delegatecall =
    (* Stack *)
    let$ gas = U256.to_unbounded <$> pop in
    let$ code_address = Address.of_u256_truncating <$> pop in
    let$ input_start = pop in
    let$ input_size = pop in
    let$ output_start = pop in
    let$ output_size = pop in

    let$ original_sender = !(execution_environment |-- sender) in
    let$ original_value = !(execution_environment |-- value) in

    let$ self_addr = self in

    call_opcode_impl ~kind:Evmc.CallKind.DelegateCall
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
    let$ input_size = pop in
    let$ create2_salt = pop in

    (* Gas *)
    let$ memory_extension_gas = extend_memory_to U256.(input_start + input_size) in
    let input_size_in_words = U256.(to_unbounded (bytes_to_whole_words input_size)) in
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
      generic_create_impl ~kind:Evmc.CallKind.Create2 ~endowment ~input_start ~input_size ~create2_salt
    in

    (* PC *)
    increase_pc_and_continue

  let staticcall =
    (* Stack *)
    let$ gas = U256.to_unbounded <$> pop in
    let$ recipient = Address.of_u256_truncating <$> pop in
    let$ input_start = pop in
    let$ input_size = pop in
    let$ output_start = pop in
    let$ output_size = pop in

    let$ self_addr = self in
    call_opcode_impl
      ~kind:Evmc.CallKind.Call
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
    let$ pos = pop in
    let$ size = pop in

    (* Gas *)
    let$ () =
      (* We do not spend gas when copying a zero-size return value *)
      when_
        U256.(size > zero)
        (let$ memory_extension_gas = extend_memory_to U256.(pos + size - one) in
         spend memory_extension_gas )
    in

    (* Operation *)
    let$ result = Memory.read_block_at pos size <$> !(machine_state |-- memory) in
    let$ () = machine_state |-- output_buffer := result in

    (* PC *)
    fail Revert

  let selfdestruct =
    (* Stack *)
    let$ beneficiary = Address.of_u256_truncating <$> pop in

    (* Gas *)
    let$ access_gas = Gas.account_access_cost <$> HostAPI.access_account beneficiary in
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

  let trace_stack stack =
    Format.printf "<top>\n" ;
    List.iter (fun elt -> Format.printf "%s\n" (U256.to_string elt)) stack ;
    Format.printf "<bottom>\n"

  let trace_memory ms =
    (* Write one word at a time *)
    let rec loop pos =
      if U256.(pos < ms.active_memory_words) then (
        Format.printf "%s: %s\n" (U256.to_short_hex_string pos)
          (Bytes.to_hex_string (Memory.read_block_at pos U256.(~$32) ms.memory)) ;
        loop U256.(pos + ~$32) )
    in
    loop U256.zero

  let trace_state =
    let$ ms = !machine_state in
    Format.printf "PC: %s\n" (U256.to_string ms.pc) ;
    Format.printf "Gas: %s\n" (U256.to_string ms.gas) ;
    Format.printf "Stack: \n" ;
    trace_stack ms.stack ;
    Format.printf "Memory: \n" ;
    trace_memory ms ;
    return ()

  let rec run ?(trace = false) (code : Bytes.t) : unit M.t =
    let$ () = when_ trace trace_state in
    let$ pc = !(machine_state |-- pc) in
    let opcode =
      (* YP (157) *)
      match U256.to_int_opt pc with
      | Some pc when pc < Bytes.length code -> Opcode.of_byte code.[pc]
      | _ -> Opcode.Stop
    in
    ( if trace then
        let info = Opcode.info opcode in
        Format.printf "Executing opcode 0x%x(%s)\n" (Char.code info.byte) info.name ) ;
    let$ continue = execute_opcode opcode in
    if continue then run ~trace code else return ()

  let call ?(trace = false) (msg : Evmc.Message.t) : Evmc.Result.t Host.t =
    Host.(
      let$ tx_context = get_tx_context in
      let ctx = Context.make tx_context msg in
      let$ res, ctx = run ~trace msg.code ctx in
      return
        ( match res with
        | Ok () ->
            Evmc.Result.
              { status_code = Success
              ; gas_left = U256.to_uint64 ctx.machine_state.gas
              ; gas_refund = 0L
              ; output_data = ctx.machine_state.output_buffer
              ; create_address = None }
        | Error err -> (
          match err with
          | Success -> assert false
          | Revert ->
              (*
               * If a contract finishes with a REVERT instruction, remaining gas is refunded and the output
               * buffer is read, see YP (152)
               *)
              Evmc.Result.
                { status_code = err
                ; gas_left = U256.to_uint64 ctx.machine_state.gas
                ; gas_refund = 0L
                ; output_data = ctx.machine_state.output_buffer
                ; create_address = None }
          | _ ->
              Evmc.Result.
                { status_code = err
                ; gas_left = 0L
                ; gas_refund = 0L
                ; output_data = Bytes.empty
                ; create_address = None } ) ) )
end
