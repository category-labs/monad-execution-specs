(** EIP-2537: precompiles for BLS12-381 curve operations. *)

open Byte_string
open Numeric
open Chain.Ethereum

open Utils

open Ec.Bls12_381
open Ec_precompile_utils (struct
  include Ec.Bls12_381
  module C1_coord_repr = B64

  (* See EIP-2537, under "Field elements encoding". *)
  let complex_encoding = `Real_first
end)

(* Constants for gas cost calculation. *)
let g1_add_cost = Gas.of_int 375
let g1_mul_cost = Gas.of_int 12_000
let g2_add_cost = Gas.of_int 600
let g2_mul_cost = Gas.of_int 22_500
let multiplier = Gas.of_int 1_000

module IntMap = Map.Make (Int)

let g1_discount =
  let open Gas in
  let max_discount = ~$519 in
  let discount_table =
    IntMap.of_list
      [ (1, ~$1000)
      ; (2, ~$949)
      ; (3, ~$848)
      ; (4, ~$797)
      ; (5, ~$764)
      ; (6, ~$750)
      ; (7, ~$738)
      ; (8, ~$728)
      ; (9, ~$719)
      ; (10, ~$712)
      ; (11, ~$705)
      ; (12, ~$698)
      ; (13, ~$692)
      ; (14, ~$687)
      ; (15, ~$682)
      ; (16, ~$677)
      ; (17, ~$673)
      ; (18, ~$669)
      ; (19, ~$665)
      ; (20, ~$661)
      ; (21, ~$658)
      ; (22, ~$654)
      ; (23, ~$651)
      ; (24, ~$648)
      ; (25, ~$645)
      ; (26, ~$642)
      ; (27, ~$640)
      ; (28, ~$637)
      ; (29, ~$635)
      ; (30, ~$632)
      ; (31, ~$630)
      ; (32, ~$627)
      ; (33, ~$625)
      ; (34, ~$623)
      ; (35, ~$621)
      ; (36, ~$619)
      ; (37, ~$617)
      ; (38, ~$615)
      ; (39, ~$613)
      ; (40, ~$611)
      ; (41, ~$609)
      ; (42, ~$608)
      ; (43, ~$606)
      ; (44, ~$604)
      ; (45, ~$603)
      ; (46, ~$601)
      ; (47, ~$599)
      ; (48, ~$598)
      ; (49, ~$596)
      ; (50, ~$595)
      ; (51, ~$593)
      ; (52, ~$592)
      ; (53, ~$591)
      ; (54, ~$589)
      ; (55, ~$588)
      ; (56, ~$586)
      ; (57, ~$585)
      ; (58, ~$584)
      ; (59, ~$582)
      ; (60, ~$581)
      ; (61, ~$580)
      ; (62, ~$579)
      ; (63, ~$577)
      ; (64, ~$576)
      ; (65, ~$575)
      ; (66, ~$574)
      ; (67, ~$573)
      ; (68, ~$572)
      ; (69, ~$570)
      ; (70, ~$569)
      ; (71, ~$568)
      ; (72, ~$567)
      ; (73, ~$566)
      ; (74, ~$565)
      ; (75, ~$564)
      ; (76, ~$563)
      ; (77, ~$562)
      ; (78, ~$561)
      ; (79, ~$560)
      ; (80, ~$559)
      ; (81, ~$558)
      ; (82, ~$557)
      ; (83, ~$556)
      ; (84, ~$555)
      ; (85, ~$554)
      ; (86, ~$553)
      ; (87, ~$552)
      ; (88, ~$551)
      ; (89, ~$550)
      ; (90, ~$549)
      ; (91, ~$548)
      ; (92, ~$547)
      ; (93, ~$547)
      ; (94, ~$546)
      ; (95, ~$545)
      ; (96, ~$544)
      ; (97, ~$543)
      ; (98, ~$542)
      ; (99, ~$541)
      ; (100, ~$540)
      ; (101, ~$540)
      ; (102, ~$539)
      ; (103, ~$538)
      ; (104, ~$537)
      ; (105, ~$536)
      ; (106, ~$536)
      ; (107, ~$535)
      ; (108, ~$534)
      ; (109, ~$533)
      ; (110, ~$532)
      ; (111, ~$532)
      ; (112, ~$531)
      ; (113, ~$530)
      ; (114, ~$529)
      ; (115, ~$528)
      ; (116, ~$528)
      ; (117, ~$527)
      ; (118, ~$526)
      ; (119, ~$525)
      ; (120, ~$525)
      ; (121, ~$524)
      ; (122, ~$523)
      ; (123, ~$522)
      ; (124, ~$522)
      ; (125, ~$521)
      ; (126, ~$520)
      ; (127, ~$520)
      ; (128, ~$519) ]
  in
  fun k -> IntMap.find_opt k discount_table |> Option.value ~default:max_discount

let g2_discount =
  let open Gas in
  let max_discount = ~$524 in
  let discount_table =
    IntMap.of_list
      [ (1, ~$1000)
      ; (2, ~$1000)
      ; (3, ~$923)
      ; (4, ~$884)
      ; (5, ~$855)
      ; (6, ~$832)
      ; (7, ~$812)
      ; (8, ~$796)
      ; (9, ~$782)
      ; (10, ~$770)
      ; (11, ~$759)
      ; (12, ~$749)
      ; (13, ~$740)
      ; (14, ~$732)
      ; (15, ~$724)
      ; (16, ~$717)
      ; (17, ~$711)
      ; (18, ~$704)
      ; (19, ~$699)
      ; (20, ~$693)
      ; (21, ~$688)
      ; (22, ~$683)
      ; (23, ~$679)
      ; (24, ~$674)
      ; (25, ~$670)
      ; (26, ~$666)
      ; (27, ~$663)
      ; (28, ~$659)
      ; (29, ~$655)
      ; (30, ~$652)
      ; (31, ~$649)
      ; (32, ~$646)
      ; (33, ~$643)
      ; (34, ~$640)
      ; (35, ~$637)
      ; (36, ~$634)
      ; (37, ~$632)
      ; (38, ~$629)
      ; (39, ~$627)
      ; (40, ~$624)
      ; (41, ~$622)
      ; (42, ~$620)
      ; (43, ~$618)
      ; (44, ~$615)
      ; (45, ~$613)
      ; (46, ~$611)
      ; (47, ~$609)
      ; (48, ~$607)
      ; (49, ~$606)
      ; (50, ~$604)
      ; (51, ~$602)
      ; (52, ~$600)
      ; (53, ~$598)
      ; (54, ~$597)
      ; (55, ~$595)
      ; (56, ~$593)
      ; (57, ~$592)
      ; (58, ~$590)
      ; (59, ~$589)
      ; (60, ~$587)
      ; (61, ~$586)
      ; (62, ~$584)
      ; (63, ~$583)
      ; (64, ~$582)
      ; (65, ~$580)
      ; (66, ~$579)
      ; (67, ~$578)
      ; (68, ~$576)
      ; (69, ~$575)
      ; (70, ~$574)
      ; (71, ~$573)
      ; (72, ~$571)
      ; (73, ~$570)
      ; (74, ~$569)
      ; (75, ~$568)
      ; (76, ~$567)
      ; (77, ~$566)
      ; (78, ~$565)
      ; (79, ~$563)
      ; (80, ~$562)
      ; (81, ~$561)
      ; (82, ~$560)
      ; (83, ~$559)
      ; (84, ~$558)
      ; (85, ~$557)
      ; (86, ~$556)
      ; (87, ~$555)
      ; (88, ~$554)
      ; (89, ~$553)
      ; (90, ~$552)
      ; (91, ~$552)
      ; (92, ~$551)
      ; (93, ~$550)
      ; (94, ~$549)
      ; (95, ~$548)
      ; (96, ~$547)
      ; (97, ~$546)
      ; (98, ~$545)
      ; (99, ~$545)
      ; (100, ~$544)
      ; (101, ~$543)
      ; (102, ~$542)
      ; (103, ~$541)
      ; (104, ~$541)
      ; (105, ~$540)
      ; (106, ~$539)
      ; (107, ~$538)
      ; (108, ~$537)
      ; (109, ~$537)
      ; (110, ~$536)
      ; (111, ~$535)
      ; (112, ~$535)
      ; (113, ~$534)
      ; (114, ~$533)
      ; (115, ~$532)
      ; (116, ~$532)
      ; (117, ~$531)
      ; (118, ~$530)
      ; (119, ~$530)
      ; (120, ~$529)
      ; (121, ~$528)
      ; (122, ~$528)
      ; (123, ~$527)
      ; (124, ~$526)
      ; (125, ~$526)
      ; (126, ~$525)
      ; (127, ~$524)
      ; (128, ~$524) ]
  in
  fun k -> IntMap.find_opt k discount_table |> Option.value ~default:max_discount

let g1_add_address = Address.of_hex_string "0x0b"
let g1_add (msg : Evmc.Message.t) : precompile_result =
  Precompile.(
    run msg
      (let$ () = ensure (Bytes.length msg.input_data = 256) in

       let$ () = spend_gas g1_add_cost in

       (* g1_add does not check that its inputs are in G1. *)
       let$ p_0 = point_c1 in
       let$ p_1 = point_c1 in

       return (delta_1_inv C_1.(p_0 + p_1)) ) )

let g1_msm_address = Address.of_hex_string "0x0c"
let g1_msm (msg : Evmc.Message.t) : precompile_result =
  Precompile.(
    run msg
      (let$ () = ensure (Bytes.length msg.input_data mod 160 = 0) in
       let k = Bytes.length msg.input_data / 160 in
       let$ () = ensure (k > 0) in

       let$ () = spend_gas Gas.(~$k * g1_mul_cost * g1_discount k / multiplier) in

       let$ points = list k (pair point_g1 u256) in

       (* TODO: this can be done faster with Pippenger's algorithm. *)
       let sum = List.fold_left (fun acc (pt, s) -> G_1.(acc + (U256.to_uint s * pt))) G_1.zero points in
       return (delta_1_inv (sum :> C_1.t)) ) )

let g2_add_address = Address.of_hex_string "0x0d"
let g2_add (msg : Evmc.Message.t) : precompile_result =
  Precompile.(
    run msg
      (let$ () = ensure (Bytes.length msg.input_data = 512) in

       let$ () = spend_gas g2_add_cost in

       (* g2_add does not check that its inputs are in G2. *)
       let$ p_0 = point_c2 in
       let$ p_1 = point_c2 in

       return (delta_2_inv C_2.(p_0 + p_1)) ) )

let g2_msm_address = Address.of_hex_string "0x0e"
let g2_msm (msg : Evmc.Message.t) : precompile_result =
  Precompile.(
    run msg
      (let$ () = ensure (Bytes.length msg.input_data mod 288 = 0) in
       let k = Bytes.length msg.input_data / 288 in
       let$ () = ensure (k > 0) in

       let$ () = spend_gas Gas.(~$k * g2_mul_cost * g2_discount k / multiplier) in

       let$ points = list k (pair point_g2 u256) in

       (* TODO: this can be done faster with Pippenger's algorithm. *)
       let sum = List.fold_left (fun acc (pt, s) -> G_2.(acc + (U256.to_uint s * pt))) G_2.zero points in
       return (delta_2_inv (sum :> C_2.t)) ) )

let pairing_check_address = Address.of_hex_string "0x0f"
let pairing_check (msg : Evmc.Message.t) : precompile_result =
  Precompile.(
    run msg
      (let$ () = ensure (Bytes.length msg.input_data mod 384 = 0) in
       let k = Bytes.length msg.input_data / 384 in
       let$ () = ensure (k > 0) in

       let$ () = spend_gas Gas.((~$k * ~$32_600) + ~$37_700) in

       let$ points = list k (pair point_g1 point_g2) in

       return
         (if Ec.Bls12_381.pairing_check points then U256.(to_repr_bytes one) else U256.(to_repr_bytes zero))
      ) )

let map_fp_to_g1_address = Address.of_hex_string "0x10"
let map_fp_to_g1 (msg : Evmc.Message.t) : precompile_result =
  Precompile.(
    run msg
      (let$ () = ensure (Bytes.length msg.input_data = 64) in

       let$ () = spend_gas Gas.(of_int 5_500) in

       let$ fp_elem = f_p in
       return (delta_1_inv (Ec.Bls12_381.map_fp_to_g1 fp_elem :> C_1.t)) ) )

let map_fp2_to_g2_address = Address.of_hex_string "0x11"
let map_fp2_to_g2 (msg : Evmc.Message.t) : precompile_result =
  Precompile.(
    run msg
      (let$ () = ensure (Bytes.length msg.input_data = 128) in

       let$ () = spend_gas Gas.(of_int 23_800) in

       let$ fp2_elem = f_p2 in
       return (delta_2_inv (Ec.Bls12_381.map_fp2_to_g2 fp2_elem :> C_2.t)) ) )
