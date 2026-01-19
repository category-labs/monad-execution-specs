open Monad_lib
open Chain.Ethereum
open Monad_lib.Numeric

module Revision = struct
  let rev = Chain.Monad.Revision.Four
end

module Params = struct
  let trace = false
end

module Evm = struct
  module Evm0 = Evmc.Instantiate (Evmc.DummyHost.M) (Evmc.DummyHost.Make) (Vm.Make (Params))

  (* Unfold one level of recursion to get access to the full signature of Vm *)
  module Vm = Vm.Make (Params) (Evm0.Host)
  module Host = Evm0.Host
end

(* U256.t generator *)
module QCheck2 = struct
  include QCheck2
  module Print = struct
    include Print
    let u256 x = Format.sprintf "%s (%s)" (U256.to_string x) (U256.to_short_hex_string x)
    let i256 x = Format.sprintf "%s (%s)" (I256.to_string x) (I256.to_short_hex_string x)
    let z : Z.t t =
     fun x ->
      (if Z.(x < zero) then Format.sprintf "%s (-%s)" (Z.to_string x) else Format.sprintf "%s")
        (Bytes.to_hex_string (Z.to_bits x))
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
      return (U256.of_bytes_be bytes_be)

    let i256 : I256.t t =
      let* num = u256 in
      return (U256.as_signed num)

    let z : Z.t t =
      let* negative = bool in
      let* bytes_le = string_size ~gen:uint8 nat in
      let abs = Z.of_bits bytes_le in
      return (if negative then Z.neg abs else abs)
  end
end

let check_prop ~name ?print ?(count = 10000) generator property =
  QCheck_alcotest.to_alcotest (QCheck2.Test.make ?print ~name ~count generator property)

let u256 =
  ( module struct
    include U256
    let pp = Fmt.of_to_string (fun w -> U256.to_short_hex_string w)
  end : Alcotest.TESTABLE
    with type t = U256.t )

let status_code =
  ( module struct
    include Evmc.Result.StatusCode
    let pp = Fmt.of_to_string (fun s -> Evmc.Result.StatusCode.to_string s)
    let equal = Stdlib.( = )
  end : Alcotest.TESTABLE
    with type t = Evmc.Result.StatusCode.t )

let expect_result_status (status : Evmc.Result.StatusCode.t) (result : Evmc.Result.t) =
  Alcotest.check' status_code ~msg:"Result status code is correct" ~expected:status ~actual:result.status_code

let test_message
    ?(prepare_env : unit Evm.Host.t = Evm.Host.return ())
    ?(prepare_vm : unit Evm.Vm.M.t = Evm.Vm.M.return ())
    ?(check_vm_state : unit Evm.Vm.M.t option)
    ?(check_env_state : unit Evm.Host.t = Evm.Host.return ())
    ?(check_result : Evmc.Result.t -> unit = expect_result_status Evmc.Result.StatusCode.Success)
    (msg : Evmc.Message.t) =
  (* This is partially duplicated from vm.ml as it needs to inject assssertion-checking.
     With better VM instrumentation we can remove the duplucation *)
  let action =
    let open Evmc.DummyHost in
    let open Evm.Host in
    let$ () = prepare_env in
    let$ tx_context = get_tx_context in
    let ctx = Vm.Context.make tx_context msg msg.code in
    let$ res, ctx =
      Evm.Vm.M.(
        let$ () = prepare_vm in
        let$ () = Evm.Vm.run msg.code in
        match check_vm_state with None -> return () | Some check -> check )
        ctx
    in
    let$ () = check_env_state in
    return
      ( match res with
      | Ok () ->
          Evmc.Result.
            { status_code = Success
            ; gas_left = Uint.to_uint64 ctx.machine_state.gas
            ; gas_refund = 0L
            ; output_data = ctx.machine_state.output_buffer
            ; create_address = Address.zero }
      | Error err -> (
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
        | _ ->
            Evmc.Result.
              { status_code = err
              ; gas_left = 0L
              ; gas_refund = 0L
              ; output_data = Bytes.empty
              ; create_address = Address.zero } ) )
  in
  let result, state = action Evmc.DummyHost.State.empty in
  (* If the caller specified a VM postcondition but execution finished with an early abort,
     the postcondition did not get checked and so the test preemptively fails *)
  if Option.is_some check_vm_state then expect_result_status Evmc.Result.StatusCode.Success result ;
  check_result result ;
  (result, state)

let bytecode_to_call_message code =
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
      ; create2_salt = U256.zero
      ; code_address = Address.zero
      ; code } )

let expect_stack expected_stack =
  let open Lens.Infix in
  let open Evm.Vm.M in
  let$ stack = !(Vm.Context.machine_state |-- Vm.MachineState.stack) in
  Alcotest.check' Alcotest.int ~msg:"Stack after execution has correct size"
    ~expected:(List.length expected_stack) ~actual:(List.length stack) ;
  return
    (List.iteri
       (fun i (expected, actual) ->
         Alcotest.check' u256 ~msg:(Format.sprintf "Output %d is correct" i) ~expected ~actual )
       (List.combine expected_stack stack) )

let test_bytecode_pure bc ~input_stack ~output_stack =
  let open Lens.Infix in
  let open Evm.Vm.M in
  let msg = bytecode_to_call_message bc in
  ignore
    (test_message
       ~prepare_vm:(Vm.Context.machine_state |-- Vm.MachineState.stack := input_stack)
       ~check_vm_state:(expect_stack output_stack) msg )

let opcode_test_name opcode inputs output =
  let inputs = List.map U256.to_short_hex_string inputs |> String.concat ", " in
  Format.sprintf "%s(%s) -> %s" (Opcode.to_string opcode) inputs (U256.to_short_hex_string output)

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
