(** Higher-level utilities for building bytecode for tests. *)

open Monad_lib
open Monad_lib.Opcode
open Monad_lib.Numeric
open Monad_lib.Byte_string

let to_bytecode (opcodes : Opcode.t list) : Bytes.t =
  List.to_seq opcodes |> Seq.map Opcode.to_byte |> Bytes.of_seq

let push (w : U256.t) =
  let significant_bytes = U256.significant_bytes w in
  Opcode.to_bytes (Push significant_bytes)
  ^ Bytes.sub (U256.to_repr_bytes w) (32 - significant_bytes) significant_bytes

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
