open Numeric
open Algebra

type curve_family = BN | BLS12

(* Generic Miller-loop-based pairing for curves of the form y² = x³ + b over a degree-12 extension field F12. *)
module Make
    (F12 : FIELD)
    (Params : sig
      (* Curve parameters. *)
      val a : F12.t
      val b : F12.t

      val field_characteristic : Uint.t
      val curve_order : Uint.t

      val ate_loop_count : Uint.t

      (* Some curves (bn128) need an extra adjustment step after the Miller loop. See Vercauteren 2009 for the
         algebra or py_ecc for a concrete implementation. *)
      val curve_family : curve_family
    end) =
struct
  module C_12 = Curve.Make (F12) (Params)

  let ( ** ) (f : F12.t) (n : Uint.t) : F12.t =
    let rec loop n f acc =
      if Uint.(n = zero) then acc
      else
        let n, r = Uint.div_rem n Uint.(~$2) in
        let acc = if Uint.(r = one) then F12.(acc * f) else acc in
        loop n F12.(f * f) acc
    in
    loop n f F12.one

  (* Evaluate the line through P1 and P2 at point T (all non-infinity). *)
  let linefunc ((x1, y1) : F12.t * F12.t) ((x2, y2) : F12.t * F12.t) ((xt, yt) : F12.t * F12.t) : F12.t =
    let open F12 in
    if x1 <> x2 then
      let m = (y2 - y1) / (x2 - x1) in
      (m * (xt - x1)) - (yt - y1)
    else if y1 = y2 then
      let m = ((~$3 * x1 * x1) + Params.a) / (~$2 * y1) in
      (m * (xt - x1)) - (yt - y1)
    else xt - x1

  let c12_add ((x1, y1) : F12.t * F12.t) ((x2, y2) : F12.t * F12.t) : F12.t * F12.t =
    match C_12.(Point (x1, y1) + Point (x2, y2)) with
    | C_12.Infinity -> failwith "Pairing.c12_add: unexpected infinity"
    | C_12.Point (x, y) -> (x, y)

  (* Frobenius map. frob x = xᵖ where p is the field characteristic. *)
  let frob x = x ** Params.field_characteristic

  let post_loop_adjustment =
    match Params.curve_family with
    | BN ->
        fun ~q:(qx, qy) ~r ~p f ->
          (* See Vercauteren 2009 §IV *)
          let ((q1x, q1y) as q1) = (frob qx, frob qy) in
          let nq2 = (frob q1x, F12.(zero - frob q1y)) in
          let f = F12.(f * linefunc r q1 p) in
          let r = c12_add r q1 in
          let f = F12.(f * linefunc r nq2 p) in
          f
    | BLS12 ->
        fun ~q:_ ~r:_ ~p:_ f ->
          (* The BLS12 family of curves requires no adjustment, see e.g. "Implementing Pairings at the 192-bit
             Security Level" §4. *)
          f

  let post_loop_exponent = Uint.(((Params.field_characteristic ** 12) - ~$1) / Params.curve_order)

  (* Miller loop implementation, modelled after py_ecc. *)
  let miller_loop (q : C_12.t) (p : C_12.t) : F12.t =
    match (q, p) with
    | C_12.Infinity, _ | _, C_12.Infinity -> F12.one
    | C_12.Point (qx, qy), C_12.Point (px, py) ->
        let qp = (qx, qy) in
        let pp = (px, py) in
        let rec loop i r f =
          if i < 0 then (r, f)
          else
            let f = F12.(f * f * linefunc r r pp) in
            let r = c12_add r r in
            let r, f =
              if Uint.testbit Params.ate_loop_count i then (c12_add r qp, F12.(f * linefunc r qp pp))
              else (r, f)
            in
            loop (i - 1) r f
        in
        let log_ate_loop_count = Uint.significant_bits Params.ate_loop_count - 2 in
        let r, f = loop log_ate_loop_count qp F12.one in
        let f = post_loop_adjustment ~q:qp ~p:pp ~r f in
        f ** post_loop_exponent

  let pairing_check (pairs : (C_12.t * C_12.t) list) : bool =
    let result = List.fold_left (fun acc (q, p) -> F12.(acc * miller_loop q p)) F12.one pairs in
    F12.(result = one)
end
