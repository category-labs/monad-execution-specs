open Monad_lib.Utils
open Monad_lib.Opcode
module Word = Monad_lib.Word

let (=>) = (@)

let push (w : Word.t) =
  Word.to_bytes32_be w
  |> Bytes.to_seq
  |> Seq.map (fun b -> Undefined b)
  |> List.of_seq
  |> fun bytes -> Push 32 :: bytes

type stack_value = Lit of Word.t | Pop

let opt_1 opcode x = match x with Pop -> [opcode] | Lit lit -> push lit @ [opcode]
let opt_2 opcode x y  =
  match (x, y) with
  | Lit lit_x, Lit lit_y -> push lit_y @ push lit_x @ [opcode]
  | Lit lit_x, Pop -> push lit_x @ [opcode]
  | Pop, Lit lit_y -> push lit_y @ [Swap 1; opcode]
  | Pop, Pop -> [opcode]

let sload key = opt_1 Sload key
let tload key = opt_1 Tload key

let sstore key value = opt_2 Sstore key value
let tstore key value = opt_2 Tstore key value
