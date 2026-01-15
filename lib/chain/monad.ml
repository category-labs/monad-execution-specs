(** Definitions for Monad-specific types. *)
open Numeric

module Revision = struct
  type t = Zero | One | Two | Three | Four | Five | Six | Seven | Eight | Next

  let to_string = function
    | Zero -> "MONAD_ZERO"
    | One -> "MONAD_ONE"
    | Two -> "MONAD_TWO"
    | Three -> "MONAD_THREE"
    | Four -> "MONAD_FOUR"
    | Five -> "MONAD_FIVE"
    | Six -> "MONAD_SIX"
    | Seven -> "MONAD_SEVEN"
    | Eight -> "MONAD_EIGHT"
    | Next -> "MONAD_NEXT"

  let of_string = function
    | "MONAD_ZERO" -> Some Zero
    | "MONAD_ONE" -> Some One
    | "MONAD_TWO" -> Some Two
    | "MONAD_THREE" -> Some Three
    | "MONAD_FOUR" -> Some Four
    | "MONAD_FIVE" -> Some Five
    | "MONAD_SIX" -> Some Six
    | "MONAD_SEVEN" -> Some Seven
    | "MONAD_EIGHT" -> Some Eight
    | "MONAD_NEXT" -> Some Next
    | _ -> None
end

let wei_per_mon = U256.(~$1_000_000_000_000_000_000)

module type PARAMS = sig
  val chain_id : Uint.t (* β *)
end

module Devnet : PARAMS = struct
  let chain_id = Uint.(~$20_143)
end

module Testnet : PARAMS = struct
  let chain_id = Uint.(~$10_143)
end

module Mainnet : PARAMS = struct
  let chain_id = Uint.(~$143)
end
