(* Utilities for building bytecode *)

open Monad_lib
open Monad_lib.Utils
open Monad_lib.Opcode
open Monad_lib.Numeric

let to_bytecode (opcodes : Opcode.t list) : Bytes.t =
  List.to_seq opcodes |> Seq.map Opcode.to_byte |> Bytes.of_seq

let push (w : U256.t) = Opcode.to_bytes (Push 32) ^ U256.to_bytes_be w

type stack_value = Lit of U256.t | Pop

let opt_1 opcode x = match x with Pop -> to_bytes opcode | Lit lit -> push lit ^ to_bytes opcode
let opt_2 opcode x y =
  match (x, y) with
  | Lit lit_x, Lit lit_y -> push lit_y ^ push lit_x ^ to_bytes opcode
  | Lit lit_x, Pop -> push lit_x ^ to_bytes opcode
  | Pop, Lit lit_y -> push lit_y ^ to_bytes (Swap 1) ^ to_bytes opcode
  | Pop, Pop -> to_bytes opcode

let mload key = opt_1 Mload key
let sload key = opt_1 Sload key
let tload key = opt_1 Tload key

let mstore key value = opt_2 Mstore key value
let sstore key value = opt_2 Sstore key value
let tstore key value = opt_2 Tstore key value

let keccak = opt_2 Keccak
