open Monad_lib
open Monad_lib.Chain.Ethereum
open Monad_lib.Numeric
open Monad_lib.Byte_string

(* Generators and printers for our types. *)
module QCheck2 = struct
  include QCheck2
  module Print = struct
    include Print
    let u256 x = Format.sprintf "%s (%s)" (U256.to_string x) (U256.to_hex_string x)
    let i256 x = Format.sprintf "%s (%s)" (I256.to_string x) (I256.to_hex_string x)
    let z : Z.t t =
     fun x ->
      (if Z.(x < zero) then Format.sprintf "%s (-%s)" (Z.to_string x) else Format.sprintf "%s")
        (Bytes.to_hex_string (Z.to_bits x))
    let rlp : Rlp.t t = Rlp.to_string
    let byte_string = Bytes.to_hex_string
  end

  module Gen = struct
    include Gen
    let uint8 = char_range '\x00' '\xff'
    let u256 : U256.t t =
      (* Uniformly distributed random strings are very unlikely to be negative.
         Bool shrinks towards false so this generator will shrink towards positive numbers. *)
      let* negative = bool in
      let* bytes_be =
        if negative then (
          (* Always generate 32 bytes, force MSB to be 1. Note that bytes will shrink towards 0xff *)
          let* bytes = bytes_size ~gen:(char_range ~origin:'\xff' '\x00' '\xff') (return 32) in
          Stdlib.Bytes.(
            set bytes 0 (Char.chr (Int.logor (Char.code (get bytes 0)) 0x80)) ;
            return (to_string bytes) ) )
        else string_size ~gen:uint8 (int_bound 32)
      in
      return U256.(of_bytes_be_exn bytes_be)

    let i256 : I256.t t =
      let* num = u256 in
      return (U256.as_signed num)

    let z : Z.t t =
      let* negative = bool in
      let* bytes_le = string_size ~gen:uint8 nat in
      let abs = Z.of_bits bytes_le in
      return (if negative then Z.neg abs else abs)

    let rec depth = function Rlp.Bytes _ -> 0 | Rlp.List ls -> 1 + List.(fold_left max 0 (map depth ls))
    let string ~nonempty : Bytes.t t =
      let size = if nonempty then ( + ) 1 <$> small_nat else small_nat in
      string_size size

    let rlp ~nonempty : Rlp.t t =
      fix
        (fun self depth ->
          let bytes_case = (fun bs -> Rlp.Bytes bs) <$> string ~nonempty in
          if depth > 2 then bytes_case
          else
            frequency
              [(3 + (2 * depth), bytes_case); (1, (fun l -> Rlp.List l) <$> small_list (self (depth + 1)))] )
        0
  end
end

let check_prop ~name ?print ?(count = 10000) generator property =
  QCheck_alcotest.to_alcotest (QCheck2.Test.make ?print ~name ~count generator property)

let u256 =
  ( module struct
    include U256
    let pp = Fmt.of_to_string U256.to_string
  end : Alcotest.TESTABLE
    with type t = U256.t )

let b32 =
  ( module struct
    include B32
    let pp = Fmt.of_to_string B32.to_hex_string
  end : Alcotest.TESTABLE
    with type t = B32.t )

let rlp =
  ( module struct
    include Rlp
    let pp = Fmt.of_to_string Rlp.to_string
  end : Alcotest.TESTABLE
    with type t = Rlp.t )

let status_code =
  ( module struct
    include Evmc.Result.StatusCode
    let pp = Fmt.of_to_string (fun s -> Evmc.Result.StatusCode.to_string s)
    let equal = Stdlib.( = )
  end : Alcotest.TESTABLE
    with type t = Evmc.Result.StatusCode.t )

let account =
  ( module struct
    include Chain.Ethereum.Account
    let pp = Fmt.of_to_string (fun acc -> Yojson.Safe.pretty_to_string (Account.to_yojson acc))
  end : Alcotest.TESTABLE
    with type t = Chain.Ethereum.Account.t )

let expect_result_status (status : Evmc.Result.StatusCode.t) (result : Evmc.Result.t) =
  Alcotest.check' status_code ~msg:"Result status code is correct" ~expected:status ~actual:result.status_code

let expect_ok (result : ('a, string) result) : 'a =
  match result with Ok value -> value | Error err -> Alcotest.fail err

module Params = struct
  let chain_id = Chain.Monad.Testnet.chain_id
  let revision = `Eight
end

let test_message
    ?(initial_state : Host.TransactionState.t = Host.TransactionState.empty)
    ?(initial_stack : U256.t list = [])
    ?(initial_memory : Bytes.t = Bytes.empty)
    ?(expect_output_stack : U256.t list option)
    ?(check_result : Evmc.Result.t -> unit = expect_result_status Evmc.Result.StatusCode.Success)
    (msg : Evmc.Message.t) =
  let module Check =
    Vm.Instrument
      (functor
         (Base_internals : Vm.INTERNALS)
         (P : Chain.Monad.PARAMS)
         (Host : Evmc.HOST)
         ->
         struct
           module Base_internals = Base_internals (P) (Host)
           module Executor (Env : Vm.ExecutionEnvironment.INSTANCE) = struct
             module Base = Base_internals.Executor (Env)
             open Vm.MachineState (P)
             let run execute_opcode (state : _ Vm.MachineState(P).t) =
               (* The stack/memory injection and final stack check only apply to the top-level frame,
                  not to nested frames entered through CALL/CREATE. *)
               if Env.execution_environment.depth > 0 then Base.run execute_opcode state
               else
                 let memory =
                   state.memory
                   |> Memory.extend_to ~start:U256.zero
                        ~size_bytes:(U256.of_int (Bytes.length initial_memory))
                   |> Option.get
                   |> Memory.write_block_at U256.zero initial_memory
                 in
                 let state =
                   {state with stack = initial_stack; stack_depth = List.length initial_stack; memory}
                 in
                 let result, state = Base.run execute_opcode state in
                 ( match (result, expect_output_stack) with
                 | Ok _, Some expected_stack ->
                     Alcotest.check' (Alcotest.list u256) ~msg:"Stack after execution" ~actual:state.stack
                       ~expected:expected_stack
                 | _ -> () ) ;
                 (result, state)
             let execute_opcode = Base.execute_opcode
           end
         end) in
  let module Evm = Host.Instantiate (Params) (Check (Vm.Make) (Params)) in
  let result, state = Evm.Vm.execute msg msg.code initial_state in
  check_result result ; (result, state)

let bytecode_to_call_message code =
  let max_memory_usage =
    let module Constants = Vm.Constants (Params) in
    Constants.max_memory_usage
  in
  Evmc.(
    Message.
      { kind = CallKind.Call
      ; delegated = false
      ; static = false
      ; depth = 0l
      ; gas = 100_000_000L
      ; recipient = Address.zero
      ; sender = Address.zero
      ; input_data = Bytes.empty
      ; value = U256.of_int 1000
      ; create2_salt = B32.zeros
      ; code_address = Address.zero
      ; code
      ; memory_capacity = Uint.to_uint32 max_memory_usage } )

let test_bytecode_pure bc ~input_stack ~output_stack =
  let msg = bytecode_to_call_message bc in
  ignore (test_message ~initial_stack:input_stack ~expect_output_stack:output_stack msg)

let opcode_test_name opcode inputs output =
  let inputs = List.map U256.to_hex_string inputs |> String.concat ", " in
  Format.sprintf "%s(%s) -> %s" (Opcode.to_string opcode) inputs (U256.to_hex_string output)

let test_case_opcode_1 opcode x_0 y =
  let test_name = opcode_test_name opcode [x_0] y in
  let bc = Bytes.make 1 (Opcode.to_byte opcode) in
  Alcotest.test_case test_name `Quick (fun () -> test_bytecode_pure bc ~input_stack:[x_0] ~output_stack:[y])

let test_case_opcode_2 opcode x_0 x_1 y =
  let test_name = opcode_test_name opcode [x_0; x_1] y in
  let bc = Bytes.make 1 (Opcode.to_byte opcode) in
  Alcotest.test_case test_name `Quick (fun () ->
      test_bytecode_pure bc ~input_stack:[x_0; x_1] ~output_stack:[y] )

let test_case_opcode_3 opcode x_0 x_1 x_2 y =
  let test_name = opcode_test_name opcode [x_0; x_1; x_2] y in
  let bc = Bytes.make 1 (Opcode.to_byte opcode) in
  Alcotest.test_case test_name `Quick (fun () ->
      test_bytecode_pure bc ~input_stack:[x_0; x_1; x_2] ~output_stack:[y] )

let test_cases_opcode_1 opcode cases =
  (Opcode.to_string opcode, List.map (fun (x_0, y) -> test_case_opcode_1 opcode x_0 y) cases)
let test_cases_opcode_2 opcode cases =
  (Opcode.to_string opcode, List.map (fun ((x_0, x_1), y) -> test_case_opcode_2 opcode x_0 x_1 y) cases)
let test_cases_opcode_3 opcode cases =
  ( Opcode.to_string opcode
  , List.map (fun ((x_0, x_1, x_2), y) -> test_case_opcode_3 opcode x_0 x_1 x_2 y) cases )

let ( $/ ) path file = Filename.concat path file

let rec traverse_folder (path : string) : (string * string) Seq.t =
  Sys.readdir path
  |> Array.to_seq
  |> Seq.concat_map (fun entry ->
      let file = path $/ entry in
      if Sys.is_directory file then traverse_folder file else Seq.singleton (path, entry) )
