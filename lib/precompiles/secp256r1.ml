(** EIP-7951: precompile for secp256r1 curve support. *)

open Byte_string
open Numeric
open Chain.Ethereum

open Utils
open Ec.Secp256r1

let f_p =
  Precompile.(
    let$ x = U256.to_uint <$> u256 in
    Option.or_fail (F_p.of_uint_opt x) )

let f_q_nz =
  Precompile.(
    let$ x = U256.to_uint <$> u256 in
    let$ () = ensure Uint.(x <> zero) in
    Option.or_fail (F_q.of_uint_opt x) )

let point_g1 =
  Precompile.(
    (* YP (260) *)
    let$ x = f_p in
    (* YP (261) *)
    let$ y = f_p in
    (* YP (258), YP (259) *)
    Option.or_fail G_1.(of_coords x y) )

let address = Address.of_hex_string "0x0100"
let verify (msg : Evmc.Message.t) : Evmc.Result.t =
  Precompile.(
    run msg
      (let$ () = spend_gas Gas.(of_int 6_900) in

       let$ h = U256.to_integer <$> u256 in

       let$ r = U256.to_uint <$> u256 in
       let$ s = U256.to_uint <$> u256 in

       let$ q_x = U256.to_uint <$> u256 in
       let$ q_y = U256.to_uint <$> u256 in

       Option.(
         (* If input length validation fails here, the contract does not revert but instead returns the empty
            byte string, as per EIP-7951. *)
         let$ () = ensure (Bytes.length msg.input_data = 160) in

         let$ r = F_q.of_uint_opt r in
         let$ s = F_q.of_uint_opt s in
         let$ () = ensure (F_q.(r <> zero) && F_q.(s <> zero)) in

         let$ q =
           let$ q_x = F_p.of_uint_opt q_x in
           let$ q_y = F_p.of_uint_opt q_y in
           G_1.of_coords q_x q_y
         in
         let$ () = ensure G_1.(q <> zero) in

         let s_inv = (F_q.(one / s) :> Integer.t) in
         let u_1 = Integer.as_unsigned_exn (F_q.(reduce Integer.(h * s_inv)) :> Integer.t) in
         let u_2 = Integer.as_unsigned_exn (F_q.(reduce Integer.((r :> Integer.t) * s_inv)) :> Integer.t) in
         let r' = G_1.((u_1 * generator) + (u_2 * q)) in
         let$ () = ensure (not G_1.(r' = zero)) in
         let x, _ = G_1.coords r' in
         let$ () = ensure F_q.(reduce (x :> Integer.t) = r) in
         return U256.(to_repr_bytes one) )
       |> Option.value ~default:Bytes.empty
       |> return ) )
