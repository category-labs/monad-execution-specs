open Monad_lib
open Utils
open Chain.Ethereum

module Revision = struct
  let rev = Chain.Monad.Revision.Four
end
module EvmcHost = Evmc.Dummy (Revision)
module Vm = Vm.Make (Revision) (EvmcHost)

let test_program ~(pre : unit Vm.M.t) ~(post : (unit Vm.M.t, Evmc.Result.StatusCode.t) result)
    (program : Opcode.t list) : unit =
  let code = program |> List.to_seq |> Seq.map Opcode.to_byte |> Bytes.of_seq in
  let msg =
    Evmc.(
      Message.
        { kind = CallKind.Call
        ; flags = []
        ; depth = 0l
        ; gas = 100000L
        ; recipient = Address.zero
        ; sender = Address.zero
        ; input_data = Bytes.empty
        ; value = Word.of_int 1000
        ; create2_salt = Word.zero
        ; code_address = Address.zero
        ; code } )
  in
  let action =
    EvmcHost.(
      let$ tx_context = EvmcHost.get_tx_context in
      let ctx = Vm.Context.make tx_context msg in
      Vm.M.(
        let$ () = pre in
        let$ () = Vm.run code in
        match post with Ok postcondition -> postcondition | Error _ -> return () )
        ctx )
  in
  let (result, _ctx), _state = action EvmcHost.State.empty in
  match (post, result) with
  | Ok _, Ok _ -> ()
  | Error expected, Error actual when expected = actual -> ()
  | Error expected, Error actual ->
      Alcotest.fail
        (Format.sprintf "Expected error code %s, but got %s"
           (Evmc.Result.StatusCode.to_string expected)
           (Evmc.Result.StatusCode.to_string actual) )
  | Ok _, Error actual ->
      Alcotest.fail
        (Format.sprintf "Expected success, but got error code %s" (Evmc.Result.StatusCode.to_string actual))
  | Error expected, Ok _ ->
      Alcotest.fail
        (Format.sprintf "Expected error code %s, but got success"
           (Evmc.Result.StatusCode.to_string expected) )

let word =
  ( module struct
    include Word
    let pp = Fmt.of_to_string (fun w -> Bytes.to_hex_string (Word.to_bytes32_be w))
  end : Alcotest.TESTABLE
    with type t = Word.t )

let test_program_pure ~(push : Word.t list) ~(pop : Word.t list) program =
  let open Vm.M in
  test_program program
    ~pre:(List.iterM push ~f:Vm.push)
    ~post:
      (Ok
         (List.iterM pop ~f:(fun expected ->
              let$ actual = Vm.pop in
              return (Alcotest.(check' word) ~msg:"Output" ~expected ~actual) ) ) )

let tests_pure program (tests : (string list * string list) list) =
  let parse (push, pop) = (List.map Word.of_string push, List.map Word.of_string pop) in
  List.map
    (fun (push, pop) ->
      Alcotest.test_case "" `Quick (fun () -> test_program_pure ~push ~pop program) )
    (List.map parse tests)
