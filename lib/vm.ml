open Utils
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

    val read_block_at : Word.t -> Word.t -> t -> Bytes.t
    val read_word_at : Word.t -> t -> Word.t

    val write_block_at : Word.t -> Bytes.t -> t -> t
    val write_word_at : Word.t -> Word.t -> t -> t
    val write_byte_at : Word.t -> char -> t -> t
  end = struct
    type t = char Word.Map.t
    let read_block_at start size (mem : t) =
      let size = match Word.to_int_opt size with None -> raise Internal_error | Some sz -> sz in
      Bytes.init size (fun byte_i ->
          Word.Map.find_opt Word.(start + ~$byte_i) mem |> Option.value ~default:'\x00' )

    let read_word_at pos (mem : t) =
      let bytes_be =
        Bytes.init 32 (fun byte_i ->
            Word.Map.find_opt Word.(pos + ~$byte_i) mem |> Option.value ~default:'\x00' )
      in
      Word.of_bytes_be bytes_be

    let write_block_at (pos : Word.t) (bytes : Bytes.t) (mem : t) =
      Seq.take (Bytes.length bytes) (Seq.ints 0)
      |> Seq.map (fun i -> (Word.(pos + ~$i), bytes.[i]))
      |> fun entries -> Word.Map.add_seq entries mem

    let write_word_at pos w = write_block_at pos (Word.to_bytes32_be w)

    let write_byte_at pos b (mem : t) = Word.Map.add pos b mem

    let empty = Word.Map.empty
  end

  module MachineState = struct
    (* YP 9.4.1 *)
    type t =
      { gas : Word.t (* mu_g *)
      ; pc : Word.t (* mu_pc *)
      ; memory : Memory.t (* mu_m *)
      ; active_memory_words : Word.t (* mu_i *)
      ; stack : Word.t list (* mu_s *)
      ; output_buffer : Bytes.t (* mu_o *) }
    [@@deriving lens {submodule = true; prefix = true}]
    include TLens

    let initial =
      { gas = Word.zero
      ; pc = Word.zero
      ; memory = Memory.empty
      ; active_memory_words = Word.zero
      ; stack = []
      ; output_buffer = Bytes.empty }
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
        ; number : Word.t (* H_i *)
        ; timestamp : Word.t (* H_s *)
        ; gas_limit : Word.t (* H_l *)
        ; prev_randao : Word.t (* H_a *)
        ; base_fee : Word.t (* H_f *) }
      [@@deriving lens {submodule = true; prefix = true}]
      include TLens

      let of_tx_context (ctx : Evmc.TxContext.t) : t =
        { coinbase = ctx.block_coinbase
        ; number = Word.of_uint64 ctx.block_number
        ; timestamp = Word.of_uint64 ctx.block_timestamp
        ; gas_limit = Word.of_uint64 ctx.block_gas_limit
        ; prev_randao = ctx.block_prev_randao
        ; base_fee = ctx.block_base_fee }
    end
    include ExecutionBlockHeader

    (* YP 9.3 *)
    type t =
      { address : Address.t (* I_a *)
      ; origin : Address.t (* I_o *)
      ; price : Word.t (* I_p *)
      ; data : Bytes.t (* I_d *)
      ; sender : Address.t (* I_s *)
      ; value : Word.t (* I_w *)
      ; bytes : Bytes.t (* I_b *)
      ; header : ExecutionBlockHeader.t (* I_H *)
      ; write_permission : bool (* I_w *)
      ; blob_versioned_hashes : Word.t list (* EIP-4844 *)
      ; blob_base_fee : Word.t (* EIP-7516 *) }
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
      ; write_permission = not (List.mem Evmc.Flags.Static msg.flags)
      ; blob_versioned_hashes = ctx.blob_hashes
      ; blob_base_fee = ctx.blob_base_fee }
  end
  open ExecutionEnvironment

  module Context = struct
    type t =
      { execution_environment : ExecutionEnvironment.t
      ; machine_state : MachineState.t
      ; jump_destinations : Word.Set.t (* D(c) *)
      ; initial_storage : Word.t Word.Map.t
            (* Cached initial values of storage cells modified in the transaction, to compute sstore costs *)
      }
    [@@deriving lens {submodule = true; prefix = true}]
    include TLens

    let valid_jump_destinations code =
      let rec loop i valid_destinations =
        if i >= Bytes.length code then valid_destinations
        else
          match code.[i] with
          | '\x5b' -> loop (i + 1) Word.(Set.add ~$i valid_destinations)
          | '\x60' .. '\x7f' as opcode ->
              let push_bytes = Char.code opcode - 0x60 + 1 in
              loop (i + 1 + push_bytes) valid_destinations
          | _ -> loop (i + 1) valid_destinations
      in
      loop 0 Word.Set.empty

    let make (ctx : Evmc.TxContext.t) (msg : Evmc.Message.t) : t =
      if Word.(ctx.chain_id <> ~$Traits.chain_id) then raise Internal_error ;
      { execution_environment = ExecutionEnvironment.make ctx msg
      ; machine_state = {MachineState.initial with gas = Word.of_uint64 msg.gas}
      ; jump_destinations = valid_jump_destinations msg.code
      ; initial_storage = Word.Map.empty }
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
    include Evmc.Host.Lift (ErrStHost) (Evmc.Host.Lift (StHost) (Host))
  end
  open M

  module Ethereum = Chain.Ethereum
  module Address = Ethereum.Address

  let max_stack_depth = 1024

  let spend (amount : Word.t) =
    let$ gas_remaining = !(machine_state |-- gas) in
    if Word.(gas_remaining < amount) then fail Out_of_gas
    else machine_state |-- gas := Word.(gas_remaining - amount)

  let check_jump_destination (destination : Word.t) =
    let$ valid_destinations = !jump_destinations in
    if Word.Set.mem destination valid_destinations then return () else fail Bad_jump_destination

  let push (x : Word.t) : unit M.t =
    let$ s = !(machine_state |-- stack) in
    if List.length s >= max_stack_depth then fail Stack_overflow else machine_state |-- stack := x :: s

  let pop : Word.t M.t =
    let$ s = !(machine_state |-- stack) in
    match s with
    | [] -> fail Stack_underflow
    | hd :: tl ->
        let$ () = machine_state |-- stack := tl in
        return hd

  module GasCosts = struct
    (* Bring Word into scope so the operators are all available to users *)
    include Word

    let jumpdest = ~$1
    let base = ~$2
    let very_low = ~$3
    let low = ~$5
    let mid = ~$8
    let high = ~$10

    let base_exp_cost = ~$10
    let exp_cost_per_byte = ~$50

    let base_keccak256_cost = ~$30
    let keccak256_cost_per_word = ~$6

    let word_copy_cost = ~$3

    let block_hash_cost = ~$20

    let memory_cost active_memory_words =
      Word.(((active_memory_words ** 2) / ~$512) + (~$3 * active_memory_words))

    let cold_account_access_cost = Word.of_uint64 Traits.cold_costs.Traits.cold_account_cost
    let warm_access_cost = ~$100

    let cold_sload_cost = ~$2_100

    let sset_cost = ~$20_000
    let sreset_cost = ~$2_900
  end

  let finish_execution : bool M.t = return false
  let update_pc_and_continue (f : Word.t -> Word.t) : bool M.t =
    update_field (machine_state |-- pc) f >> return true
  let increase_pc_and_continue : bool M.t = update_pc_and_continue Word.(( + ) one)

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
    let$ () = spend GasCosts.very_low in

    (* Operation *)
    let$ () = push Word.(x + y) in

    (* PC *)
    increase_pc_and_continue

  let mul =
    (* Stack *)
    let$ x = pop in
    let$ y = pop in

    (* Gas *)
    let$ () = spend GasCosts.low in

    (* Operation *)
    let$ () = push Word.(x * y) in

    (* PC *)
    increase_pc_and_continue

  let sub =
    (* Stack *)
    let$ x = pop in
    let$ y = pop in

    (* Gas *)
    let$ () = spend GasCosts.very_low in

    (* Operation *)
    let$ () = push Word.(x - y) in

    (* PC *)
    increase_pc_and_continue

  let udiv =
    (* Stack *)
    let$ dividend = pop in
    let$ divisor = pop in

    (* Gas *)
    let$ () = spend GasCosts.low in

    (* Operation **)
    let$ () = push Word.(if divisor = zero then zero else dividend / divisor) in

    (* PC *)
    increase_pc_and_continue

  let sdiv =
    (* Stack *)
    let$ dividend = pop in
    let$ divisor = pop in

    (* Gas *)
    let$ () = spend GasCosts.low in

    (* Operation *)
    let$ () = push Word.(if divisor = zero then zero else div_signed dividend divisor) in

    (* PC *)
    increase_pc_and_continue

  let umod =
    (* Stack *)
    let$ x = pop in
    let$ y = pop in

    (* Gas *)
    let$ () = spend GasCosts.low in

    (* Operation *)
    let$ () = push Word.(if y = zero then zero else modulo x y) in

    (* PC *)
    increase_pc_and_continue

  let smod =
    (* Stack *)
    let$ x = pop in
    let$ y = pop in

    (* Gas *)
    let$ () = spend GasCosts.low in

    (* Operation *)
    let$ () = push Word.(if y = zero then zero else modulo_signed x y) in

    (* PC *)
    increase_pc_and_continue

  let addmod =
    (* Stack *)
    let$ x = pop in
    let$ y = pop in
    let$ m = pop in

    (* Gas *)
    let$ () = spend GasCosts.mid in

    (* Operation *)
    let$ () = push Word.(if m = zero then zero else addmod x y m) in

    (* PC *)
    increase_pc_and_continue

  let mulmod =
    (* Stack *)
    let$ x = pop in
    let$ y = pop in
    let$ m = pop in

    (* Gas *)
    let$ () = spend GasCosts.mid in

    (* Operation *)
    let$ () = push Word.(if m = zero then zero else mulmod x y m) in

    (* PC *)
    increase_pc_and_continue

  let exp =
    (* Stack *)
    let$ base = pop in
    let$ exponent = pop in

    (* Gas *)
    let exponent_bytes = Word.(of_int (byte_width exponent)) in
    let$ () = spend GasCosts.(base_exp_cost + (exp_cost_per_byte * exponent_bytes)) in

    (* Operation *)
    let$ () = push Word.(exp base exponent) in

    (* PC *)
    increase_pc_and_continue

  let signextend =
    (* Stack *)
    let$ byte_index = pop in
    let$ x = pop in

    (* Gas *)
    let$ () = spend GasCosts.low in

    (* Operation *)
    let$ () = push Word.(sign_extend byte_index x) in

    (* PC *)
    increase_pc_and_continue

  let lt =
    (* Stack *)
    let$ x = pop in
    let$ y = pop in

    (* Gas *)
    let$ () = spend GasCosts.very_low in

    (* Operation *)
    let$ () = push Word.(of_bool (x < y)) in

    (* PC *)
    increase_pc_and_continue

  let gt =
    (* Stack *)
    let$ x = pop in
    let$ y = pop in

    (* Gas *)
    let$ () = spend GasCosts.very_low in

    (* Operation *)
    let$ () = push Word.(of_bool (x > y)) in

    (* PC *)
    increase_pc_and_continue

  let slt =
    (* Stack *)
    let$ x = pop in
    let$ y = pop in

    (* Gas *)
    let$ () = spend GasCosts.very_low in

    (* Operation *)
    let$ () = push (Word.of_bool (Word.signed_compare x y = -1)) in

    (* PC *)
    increase_pc_and_continue

  let sgt =
    (* Stack *)
    let$ x = pop in
    let$ y = pop in

    (* Gas *)
    let$ () = spend GasCosts.very_low in

    (* Operation *)
    let$ () = push (Word.of_bool (Word.signed_compare x y = 1)) in

    (* PC *)
    increase_pc_and_continue

  let eq =
    (* Stack *)
    let$ x = pop in
    let$ y = pop in

    (* Gas *)
    let$ () = spend GasCosts.very_low in

    (* Operation *)
    let$ () = push Word.(of_bool (x = y)) in

    (* PC *)
    increase_pc_and_continue

  let is_zero =
    (* Stack *)
    let$ x = pop in

    (* Gas *)
    let$ () = spend GasCosts.very_low in

    (* Operation *)
    let$ () = push Word.(of_bool (x = zero)) in

    (* PC *)
    increase_pc_and_continue

  let bitwise_and =
    (* Stack *)
    let$ x = pop in
    let$ y = pop in

    (* Gas *)
    let$ () = spend GasCosts.very_low in

    (* Operation *)
    let$ () = push Word.(logand x y) in

    (* PC *)
    increase_pc_and_continue

  let bitwise_or =
    (* Stack *)
    let$ x = pop in
    let$ y = pop in

    (* Gas *)
    let$ () = spend GasCosts.very_low in

    (* Operation *)
    let$ () = push Word.(logor x y) in

    (* PC *)
    increase_pc_and_continue

  let bitwise_xor =
    (* Stack *)
    let$ x = pop in
    let$ y = pop in

    (* Gas *)
    let$ () = spend GasCosts.very_low in

    (* Operation *)
    let$ () = push Word.(logxor x y) in

    (* PC *)
    increase_pc_and_continue

  let bitwise_not =
    (* Stack *)
    let$ x = pop in

    (* Gas *)
    let$ () = spend GasCosts.very_low in

    (* Operation *)
    let$ () = push Word.(lognot x) in

    (* PC *)
    increase_pc_and_continue

  let byte =
    (* Stack *)
    let$ byte_index = pop in
    let$ x = pop in

    (* Gas *)
    let$ () = spend GasCosts.very_low in

    (* Operation *)
    let$ () = push Word.(if byte_index >= ~$32 then zero else of_byte (byte (to_int byte_index) x)) in

    (* PC *)
    increase_pc_and_continue

  let logical_shift_opcode_impl shift_fn =
    (* Stack *)
    let$ shift_amount = pop in
    let$ value = pop in

    (* Gas *)
    let$ () = spend GasCosts.very_low in

    (* Operation *)
    let shifted =
      Word.(
        match to_int_opt shift_amount with
        | None -> Word.zero
        | Some s when Stdlib.(s >= 256) -> Word.zero
        | Some s -> shift_fn value s )
    in
    let$ () = push shifted in

    (* PC *)
    increase_pc_and_continue

  let shl = since Ethereum.Revision.Constantinople (logical_shift_opcode_impl Word.shift_left)
  let shr = since Ethereum.Revision.Constantinople (logical_shift_opcode_impl Word.shift_right)

  let sar =
    since Ethereum.Revision.Constantinople
      ((* Stack *)
       let$ shift_amount = pop in
       let$ value = pop in

       (* Gas *)
       let$ () = spend GasCosts.very_low in

       (* Operation *)
       let full_shift = Word.(if is_negative value then ~$(-1) else zero) in
       let shifted =
         Word.(
           match to_int_opt shift_amount with
           | None -> full_shift
           | Some s when Stdlib.(s >= 256) -> full_shift
           | Some s -> shift_right_arith value s )
       in
       let$ () = push shifted in

       (* PC *)
       increase_pc_and_continue )

  let extend_memory_to (new_address : Word.t) : Word.t M.t =
    let open Word in
    let$ current_memory_words = !(machine_state |-- active_memory_words) in
    let new_memory_words = (new_address + ~$31) / ~$32 in
    if current_memory_words >= new_memory_words then return zero
    else
      let$ () = machine_state |-- active_memory_words := new_memory_words in
      return (GasCosts.memory_cost new_memory_words - GasCosts.memory_cost current_memory_words)

  let keccak =
    (* Stack *)
    let$ start_index = pop in
    let$ size = pop in

    (* Gas *)
    let num_hashed_words = Word.((size + ~$31) / ~$32) in
    let$ memory_extension_gas = extend_memory_to Word.(start_index + size) in
    let$ () =
      spend
        GasCosts.(base_keccak256_cost + (keccak256_cost_per_word * num_hashed_words) + memory_extension_gas)
    in

    (* Operation *)
    let$ bytes = Memory.read_block_at start_index size <$> !(machine_state |-- memory) in
    let$ () = push (Crypto.keccak_256 bytes) in

    (* PC *)
    increase_pc_and_continue

  let fetch_environment_variable_opcode_impl (field : Context.t -> Word.t) =
    (* Stack *)
    (* Gas *)
    let$ () = spend GasCosts.base in

    (* Operation *)
    let$ ctx = get in
    let$ () = push (field ctx) in

    (* PC *)
    increase_pc_and_continue

  let address =
    fetch_environment_variable_opcode_impl (fun ctx -> Address.to_word ctx.execution_environment.address)
  let origin =
    fetch_environment_variable_opcode_impl (fun ctx -> Address.to_word ctx.execution_environment.origin)
  let caller =
    fetch_environment_variable_opcode_impl (fun ctx -> Address.to_word ctx.execution_environment.sender)
  let callvalue = fetch_environment_variable_opcode_impl (execution_environment |-- value).get

  let balance =
    (* Stack *)
    let$ address = Address.of_word_masking <$> pop in

    (* Gas *)
    let$ access = access_account address in
    let$ () =
      spend GasCosts.(match access with `Cold -> cold_account_access_cost | `Warm -> warm_access_cost)
    in

    (* Operation *)
    let$ balance = get_balance address in
    let$ () = push balance in

    (* PC *)
    increase_pc_and_continue

  let calldataload =
    (* Stack *)
    let$ i = pop in

    (* Gas *)
    let$ () = spend GasCosts.very_low in

    (* Operation *)
    let$ data = !(execution_environment |-- data) in
    let$ () =
      push
        ( match Word.to_int_opt i with
        | None -> Word.zero (* Index exceeds max theoretical data size *)
        | Some i -> Word.of_bytes_be (Bytes.sub_with_zero_padding data i 32) )
    in

    (* PC *)
    increase_pc_and_continue

  let calldatasize =
    (* Stack *)
    (* Gas *)
    let$ () = spend GasCosts.base in

    (* Operation *)
    let$ data = !(execution_environment |-- data) in
    let$ () = push Word.(of_int (Bytes.length data)) in

    (* PC *)
    increase_pc_and_continue

  let codesize =
    (* Stack *)
    (* Gas *)
    let$ () = spend GasCosts.base in

    (* Operation *)
    let$ size = Bytes.length <$> !(execution_environment |-- bytes) in
    let$ () = push (Word.of_int size) in

    (* PC *)
    increase_pc_and_continue

  let copy_input_data_opcode_impl data_location =
    (* Stack *)
    let$ dst_start = pop in
    let$ src_start = pop in
    let$ size = pop in

    (* Gas *)
    let n_words = Word.((size + ~$31) / ~$32) in
    let$ memory_extension_gas = extend_memory_to Word.(dst_start + size) in
    let$ () = spend GasCosts.(very_low + (n_words * word_copy_cost) + memory_extension_gas) in

    (* Operation *)
    let$ data = !data_location in
    let block =
      match (Word.to_int_opt src_start, Word.to_int_opt size) with
      | Some src_start, Some size -> Bytes.sub_with_zero_padding data src_start size
      | _, Some size -> Bytes.init size (fun _ -> '\x00')
      | _, None -> raise Internal_error
    in
    let$ () = update_field (machine_state |-- memory) (Memory.write_block_at dst_start block) in

    (* PC *)
    increase_pc_and_continue

  let calldatacopy = copy_input_data_opcode_impl (execution_environment |-- data)

  let codecopy = copy_input_data_opcode_impl (execution_environment |-- bytes)

  let gasprice = fetch_environment_variable_opcode_impl (execution_environment |-- price).get

  let extcodesize =
    (* Stack *)
    let$ address = Address.of_word_masking <$> pop in

    (* Gas *)
    let$ access = access_account address in
    let$ () =
      spend GasCosts.(match access with `Cold -> cold_account_access_cost | `Warm -> warm_access_cost)
    in

    (* Operation *)
    let$ size = get_code_size address in
    let$ () = push size in

    (* PC *)
    increase_pc_and_continue

  let extcodecopy =
    (* Stack *)
    let$ address = Address.of_word_masking <$> pop in
    let$ dst_start = pop in
    let$ src_start = pop in
    let$ size = pop in

    (* Gas *)
    let$ access = access_account address in
    let access_gas =
      GasCosts.(match access with `Cold -> cold_account_access_cost | `Warm -> warm_access_cost)
    in
    let n_words = Word.((size + ~$31) / ~$32) in
    let$ memory_extension_gas = extend_memory_to Word.(dst_start + size) in
    let$ () = spend GasCosts.(very_low + (n_words * word_copy_cost) + memory_extension_gas + access_gas) in

    (* Operation *)
    let$ data = copy_code address in
    let block =
      match (Word.to_int_opt src_start, Word.to_int_opt size) with
      | Some src_start, Some size -> Bytes.sub_with_zero_padding data src_start size
      | _, Some size -> Bytes.init size (fun _ -> '\x00')
      | _, None -> raise Internal_error
    in
    let$ () = update_field (machine_state |-- memory) (Memory.write_block_at dst_start block) in

    (* PC *)
    increase_pc_and_continue

  let extcodehash =
    (* Stack *)
    let$ address = Address.of_word_masking <$> pop in

    (* Gas *)
    let$ access = access_account address in
    let access_gas =
      GasCosts.(match access with `Cold -> cold_account_access_cost | `Warm -> warm_access_cost)
    in
    let$ () = spend access_gas in

    (* Operation *)
    let$ hash = get_code_hash address in
    let$ () = push hash in

    (* PC *)
    increase_pc_and_continue

  let returndatasize =
    fetch_environment_variable_opcode_impl (fun ctx ->
        Word.of_int (Bytes.length ctx.machine_state.output_buffer) )

  let returndatacopy =
    (* Stack *)
    let$ dst_start = pop in
    let$ src_start = pop in
    let$ size = pop in

    (* Gas *)
    let n_words = Word.((size + ~$31) / ~$32) in
    let$ memory_extension_gas = extend_memory_to Word.(dst_start + size) in
    let$ () = spend GasCosts.(very_low + (n_words * word_copy_cost) + memory_extension_gas) in

    (* Operation *)
    let$ data = !(machine_state |-- output_buffer) in
    (* Unlike similar opcodes, returndatacopy fails on out-of-bounds memory access *)
    (* YP (158) *)
    let$ src_start, size =
      match (Word.to_int_opt src_start, Word.to_int_opt size) with
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
    let$ () = spend GasCosts.block_hash_cost in

    (* Operation *)
    let$ current_block_num = !(execution_environment |-- header |-- number) in
    let$ hash =
      if Word.(current_block_num <= block_num || current_block_num - ~$256 > block_num) then return Word.zero
      else get_block_hash block_num
    in
    let$ () = push hash in

    (* PC *)
    increase_pc_and_continue

  let coinbase =
    fetch_environment_variable_opcode_impl (fun ctx ->
        Address.to_word ctx.execution_environment.header.coinbase )

  let timestamp = fetch_environment_variable_opcode_impl (execution_environment |-- header |-- timestamp).get

  let number = fetch_environment_variable_opcode_impl (execution_environment |-- header |-- number).get

  let prevrandao =
    fetch_environment_variable_opcode_impl (execution_environment |-- header |-- prev_randao).get

  let gaslimit = fetch_environment_variable_opcode_impl (execution_environment |-- header |-- gas_limit).get

  (*
   * The yellow paper gets the chain ID directly as the ambient variable Beta, as opposed to fetching it
   * from a specific field in the execution environment. The executable specs, on the other hand, does get
   * it from an environment field
   *)
  let chainid = fetch_environment_variable_opcode_impl (fun _ -> Word.of_int Traits.chain_id)

  let selfbalance =
    (* Stack *)
    (* Gas *)
    let$ () = spend GasCosts.low in

    (* Operation *)
    let$ self = !(execution_environment |-- ExecutionEnvironment.address) in
    let$ balance = get_balance self in
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
       let$ () = spend GasCosts.very_low in

       (* Operation *)
       let$ hashes = !(execution_environment |-- blob_versioned_hashes) in
       let hash =
         match Word.to_int_opt index with
         | None -> Word.zero
         | Some i -> Option.value ~default:Word.zero (List.nth_opt hashes i)
       in
       let$ () = push hash in

       (* PC *)
       increase_pc_and_continue )

  (* EIP-7516 *)
  let blobbasefee =
    since Chain.Ethereum.Revision.Cancun
      ((* Stack *)
       (* Gas *)
       let$ () = spend GasCosts.base in

       (* Operation *)
       let$ fee = !(execution_environment |-- blob_base_fee) in
       let$ () = push fee in

       (* PC *)
       increase_pc_and_continue )

  let pop_ =
    (* Stack *)
    let$ _ = pop in

    (* Gas *)
    let$ () = spend GasCosts.base in

    (* Operation *)
    (* PC *)
    increase_pc_and_continue

  let push_ i : opcode_impl =
    assert (i >= 0) ;
    assert (i <= 32) ;
    (* Stack *)
    (* Gas *)
    let$ () = spend (if i = 0 then GasCosts.base else GasCosts.very_low) in

    (* Operation *)
    let$ here = Word.to_int <$> !(machine_state |-- pc) in
    let$ code = !(execution_environment |-- bytes) in
    let$ () = push (Word.of_bytes_be (Bytes.sub_with_zero_padding code (here + 1) i)) in

    (* PC *)
    update_pc_and_continue (fun pc -> Word.(pc + one + ~$i))

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
    let$ () = spend GasCosts.very_low in

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
    let$ () = spend GasCosts.very_low in

    (* Operation *)
    let$ () = push nth in

    (* PC *)
    increase_pc_and_continue

  (* MEMORY *)
  let mload =
    (* Stack *)
    let$ pos = pop in

    (* Gas *)
    let$ memory_extension_gas = extend_memory_to Word.(pos + ~$31) in
    let$ () = spend GasCosts.(very_low + memory_extension_gas) in

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
    let$ memory_extension_gas = extend_memory_to Word.(pos + ~$31) in
    let$ () = spend GasCosts.(very_low + memory_extension_gas) in

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
    let$ () = spend GasCosts.(very_low + memory_extension_gas) in

    (* Operation *)
    let$ () = update_field (machine_state |-- memory) (Memory.write_byte_at pos Word.(byte 0 value)) in

    (* PC *)
    increase_pc_and_continue

  let sload =
    (* Stack *)
    let$ key = pop in

    (* Gas *)
    let$ self = !(execution_environment |-- ExecutionEnvironment.address) in
    let$ access = access_storage self key in
    let$ () = spend GasCosts.(match access with `Cold -> cold_sload_cost | `Warm -> warm_access_cost) in

    (* Operation *)
    let$ value = get_storage self key in
    let$ () = push value in

    (* PC *)
    increase_pc_and_continue

  let sstore =
    (* Stack *)
    let$ key = pop in
    let$ value' = pop in

    (* Gas *)
    let$ self = !(execution_environment |-- ExecutionEnvironment.address) in
    let$ access = access_storage self key in
    let$ value = get_storage self key in
    let$ value0 = !(initial_storage |-- Word.Map.at key |-- Lens.get_or_default value) in
    (*
     * If the storage slot had already been written to, then initial_storage contained an entry for it and so
     * this code does not change its value. If it had not been written to, then we store the value we get from
     * storage, before the first update
     *)
    let$ () = initial_storage |-- Word.Map.at key := Some value0 in
    let access_gas = GasCosts.(match access with `Warm -> zero | `Cold -> cold_sload_cost) in
    let update_gas =
      GasCosts.(
        if value = value' || value0 <> value then warm_access_cost
        else if value <> value' && value0 = value && value0 == Word.zero then sset_cost
        else if not (value <> value' && value0 = value && value0 <> Word.zero) then raise Internal_error
        else sreset_cost )
    in
    let$ () = spend GasCosts.(access_gas + update_gas) in

    (* Operation *)
    let$ () = set_storage self key value in

    (* PC *)
    increase_pc_and_continue

  let jump =
    (* Stack *)
    let$ new_pc = pop in

    (* Gas *)
    let$ () = spend GasCosts.mid in

    (* Operation *)
    let$ () = check_jump_destination new_pc in

    (* PC *)
    update_pc_and_continue (fun _ -> new_pc)

  let jumpi =
    (* Stack *)
    let$ new_pc = pop in
    let$ condition = pop in

    (* Gas *)
    let$ () = spend GasCosts.high in

    (* Operation *)
    let$ () = check_jump_destination new_pc in

    (* PC *)
    if Word.is_zero condition then increase_pc_and_continue else update_pc_and_continue (fun _ -> new_pc)

  let pc_ = fetch_environment_variable_opcode_impl (machine_state |-- pc).get

  let msize =
    fetch_environment_variable_opcode_impl (fun ctx -> Word.(~$8 * ctx.machine_state.active_memory_words))

  let gas =
    (* Stack *)
    (* Gas *)
    let$ () = spend GasCosts.very_low in

    (* Operation *)
    let$ current_gas = !(machine_state |-- gas) in
    let$ () = push current_gas in

    (* PC *)
    increase_pc_and_continue

  let jumpdest =
    (* Stack *)
    (* Gas *)
    let$ () = spend GasCosts.jumpdest in

    (* Operation *)
    (* PC *)
    increase_pc_and_continue

  let tload =
    (* Stack *)
    let$ key = pop in

    (* Gas *)
    let$ () = spend GasCosts.warm_access_cost in

    (* Operation *)
    let$ value = get_transient_storage key in
    let$ () = push value in

    (* PC *)
    increase_pc_and_continue

  let tstore =
    (* Stack *)
    let$ key = pop in
    let$ value = pop in

    (* Gas *)
    let$ () = spend GasCosts.warm_access_cost in

    (* Operation *)
    let$ can_write = !(execution_environment |-- write_permission) in
    let$ () = when_ (not can_write) (fail Static_mode_violation) in
    let$ () = set_transient_storage key value in

    (* PC *)
    increase_pc_and_continue

  let mcopy =
    (* Stack *)
    let$ dst_start = pop in
    let$ src_start = pop in
    let$ size = pop in

    (* Gas *)
    let n_words = Word.((size + ~$31) / ~$32) in
    let copy_cost = GasCosts.(n_words * word_copy_cost) in
    let$ memory_expansion_cost = extend_memory_to Word.(max src_start dst_start + size) in
    let$ () = spend GasCosts.(very_low + copy_cost + memory_expansion_cost) in

    (* Operation *)
    let$ block = Memory.read_block_at src_start size <$> !(machine_state |-- memory) in
    let$ () = update_field (machine_state |-- memory) (Memory.write_block_at dst_start block) in

    (* PC *)
    increase_pc_and_continue

  let log _i = todo ()

  let create _s = todo ()
  let call _s = todo ()
  let callcode _s = todo ()
  let return_ =
    (* Stack *)
    let$ pos = pop in
    let$ size = pop in

    (* Gas *)
    let$ () =
      (* We do not spend gas when copying a zero-size return value *)
      when_
        Word.(size > zero)
        (let$ memory_extension_gas = extend_memory_to Word.(pos + size - one) in
         spend GasCosts.(zero + memory_extension_gas) )
    in

    (* Operation *)
    let$ result = Memory.read_block_at pos size <$> !(machine_state |-- memory) in
    let$ () = machine_state |-- output_buffer := result in

    (* PC *)
    finish_execution

  let delegatecall _s = todo ()
  let create2 _s = todo ()
  let staticcall _s = todo ()

  let revert =
    (* Stack *)
    let$ pos = pop in
    let$ size = pop in

    (* Gas *)
    let$ () =
      (* TODO: this is a copy of identical code in `return_`, maybe abstract over it *)
      (* We do not spend gas when copying a zero-size return value *)
      when_
        Word.(size > zero)
        (let$ memory_extension_gas = extend_memory_to Word.(pos + size - one) in
         spend GasCosts.(zero + memory_extension_gas) )
    in

    (* Operation *)
    let$ result = Memory.read_block_at pos size <$> !(machine_state |-- memory) in
    let$ () = machine_state |-- output_buffer := result in

    (* PC *)
    fail Revert

  let selfdestruct _s = todo ()

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
      | Gas -> gas
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
    List.iter (fun elt -> Format.printf "%s\n" (Word.to_string elt)) stack ;
    Format.printf "<bottom>\n"

  let trace_memory ms =
    (* Write one word at a time *)
    let rec loop pos =
      if Word.(pos < ms.active_memory_words) then (
        Format.printf "%s: 0x%s\n" (Word.to_string pos)
          (Bytes.to_hex_string (Memory.read_block_at pos Word.(~$32) ms.memory)) ;
        loop Word.(pos + ~$32) )
    in
    loop Word.zero

  let trace_state =
    let$ ms = !machine_state in
    Format.printf "PC: %s\n" (Word.to_string ms.pc) ;
    Format.printf "Gas: %s\n" (Word.to_string ms.gas) ;
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
      match Word.to_int_opt pc with
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
      let$ tx_context = Host.get_tx_context in
      let ctx = Context.make tx_context msg in
      let$ res, ctx = run ~trace msg.code ctx in
      return
        ( match res with
        | Ok () ->
            Evmc.Result.
              { status_code = Success
              ; gas_left = Word.to_uint64 ctx.machine_state.gas
              ; gas_refund = 0L
              ; output_data = ctx.machine_state.output_buffer
              ; create_address = None }
        | Error err ->
            if err = Success then raise Internal_error ;
            Format.printf "Error: %s\n" (StatusCode.to_string err) ;
            exit (-1) ) )
end
