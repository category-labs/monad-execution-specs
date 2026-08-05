(** Definitions for Monad-specific types. *)
open Numeric

open Byte_string

module Revision = struct
  type t = [`Zero | `One | `Two | `Three | `Four | `Five | `Six | `Seven | `Eight | `Nine | `Next]
  let all_revisions : t list = [`Zero; `One; `Two; `Three; `Four; `Five; `Six; `Seven; `Eight; `Nine; `Next]

  let to_string : t -> string = function
    | `Zero -> "MONAD_ZERO"
    | `One -> "MONAD_ONE"
    | `Two -> "MONAD_TWO"
    | `Three -> "MONAD_THREE"
    | `Four -> "MONAD_FOUR"
    | `Five -> "MONAD_FIVE"
    | `Six -> "MONAD_SIX"
    | `Seven -> "MONAD_SEVEN"
    | `Eight -> "MONAD_EIGHT"
    | `Nine -> "MONAD_NINE"
    | `Next -> "MONAD_NEXT"
  let to_yojson (rev : t) : Yojson.Safe.t = `String (to_string rev)

  let of_string = function
    | "MONAD_ZERO" -> Some `Zero
    | "MONAD_ONE" -> Some `One
    | "MONAD_TWO" -> Some `Two
    | "MONAD_THREE" -> Some `Three
    | "MONAD_FOUR" -> Some `Four
    | "MONAD_FIVE" -> Some `Five
    | "MONAD_SIX" -> Some `Six
    | "MONAD_SEVEN" -> Some `Seven
    | "MONAD_EIGHT" -> Some `Eight
    | "MONAD_NINE" -> Some `Nine
    | "MONAD_NEXT" -> Some `Next
    | _ -> None
  let of_yojson (json : Yojson.Safe.t) : (t, string) result =
    match json with
    | `String str -> ( match of_string str with Some rev -> Ok rev | None -> Error "Revision.t" )
    | _ -> Error "Revision.t"

  (* The monad revisions supported by the current version of the spec. *)
  type active = [`Eight | `Nine]
  let is_active (rev : t) : active option = match rev with #active as rev -> Some rev | _ -> None
  let all_active_revisions : active list = List.filter_map is_active all_revisions
end

module type PARAMS = sig
  val chain_id : Uint.t (* β *)
  val revision : Revision.active
end

module Devnet = struct
  let chain_id = Uint.(~$20_143)

  let timestamp_to_revision (_timestamp : U256.t) : Revision.t = `Next
end

module Testnet = struct
  let chain_id = Uint.(~$10_143)

  let timestamp_to_revision (timestamp : U256.t) : Revision.t =
    if U256.(timestamp >= ~$1773153000) then (* 2026-03-10T14:30:00.000Z *)
      `Nine
    else if U256.(timestamp >= ~$1763562600) then (* 2025-11-19T14:30:00.000Z *)
      `Eight
    else if U256.(timestamp >= ~$1762353000) then (* 2025-11-05T14:30:00.000Z *)
      `Seven
    else if U256.(timestamp >= ~$1761917400) then (* 2025-10-31T13:30:00.000Z *)
      `Six
    else if U256.(timestamp >= ~$1761658200) then (* 2025-10-28T13:30:00.000Z *)
      `Five
    else if U256.(timestamp >= ~$1760448600) then (* 2025-10-14T13:30:00.000Z *)
      `Four
    else if U256.(timestamp >= ~$1755005400) then (* 2025-08-12T13:30:00.000Z *)
      `Three
    else if U256.(timestamp >= ~$1741978800) then (* 2025-03-14T19:00:00.000Z *)
      `Two
    else if U256.(timestamp >= ~$1739559600) then (* 2025-02-14T19:00:00.000Z *)
      `One
    else `Zero
end

module Mainnet = struct
  let chain_id = Uint.(~$143)

  let timestamp_to_revision (timestamp : U256.t) : Revision.t =
    if U256.(timestamp >= ~$1773930600) then (* 2026-03-19T14:30:00.000Z *)
      `Nine
    else if U256.(timestamp >= ~$1763649000) then (* 2025-11-20T14:30:00.000Z *)
      `Eight
    else if U256.(timestamp >= ~$1762525800) then (* 2025-11-07T14:30:00.000Z *)
      `Seven
    else if U256.(timestamp >= ~$1762266600) then (* 2025-11-04T14:30:00.000Z *)
      `Six
    else if U256.(timestamp >= ~$1755091800) then (* 2025-08-13T13:30:00.000Z *)
      `Three
    else `Two
end

let wei_per_mon = U256.(~$1_000_000_000_000_000_000)
let mon_to_wei mon = U256.(mon * wei_per_mon)

let system_sender = B20.of_hex_string "0x6f49a8F621353f12378d0046E7d7e4b9B249DC9e"
