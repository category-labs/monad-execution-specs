open Numeric
open Algebra

(* Generic Miller-loop-based pairing for curves of the form y² = x³ + b over
   a degree-12 extension field F12.

   PARAMS captures everything curve-specific:
   - The extension field F12 and the curve coefficient b12 (a12 is usually zero).
   - The Ate loop count and its bit-length (log_ate_loop_count).
   - frob12: the Frobenius endomorphism x -> x^p on F12. For BN128 this is
     x -> x^field_modulus; for BLS12-381 it is the identity (set
     apply_post_loop to false instead of passing the identity).
   - apply_post_loop: whether to perform Frobenius correction steps after the
     main Miller loop. True for BN128 (D-type twist), false for BLS12-381.
   - final_exp_exp: the exponent (p^12 - 1) / r for the final exponentiation.
*)
module Make
    (F12 : FIELD)
    (Params : sig
      val a12 : F12.t
      val b12 : F12.t
      val ate_loop_count : Uint.t
      val frob12 : F12.t -> F12.t
      val apply_post_loop : bool
      val final_exp_exp : Uint.t
    end) =
struct
  module C12 = Curve.Make (F12) (struct
    let a = Params.a12
    let b = Params.b12
  end)

  let f12_pow (f : F12.t) (n : Uint.t) : F12.t =
    let rec loop n f acc =
      if Uint.(n = zero) then acc
      else
        let n, rem = Uint.div_rem n Uint.(~$2) in
        let acc = if Uint.(rem = one) then F12.(acc * f) else acc in
        loop n F12.(f * f) acc
    in
    loop n f F12.one

  (* Evaluate the line through P1 and P2 at point T (all non-infinity). *)
  let linefunc
      ((x1, y1) : F12.t * F12.t)
      ((x2, y2) : F12.t * F12.t)
      ((xt, yt) : F12.t * F12.t)
      : F12.t =
    let open F12 in
    if x1 <> x2 then
      let m = (y2 - y1) / (x2 - x1) in
      (m * (xt - x1)) - (yt - y1)
    else if y1 = y2 then
      let m = ((~@"3" * x1 * x1) + Params.a12) / (~@"2" * y1) in
      (m * (xt - x1)) - (yt - y1)
    else
      xt - x1

  let c12_add ((x1, y1) : F12.t * F12.t) ((x2, y2) : F12.t * F12.t) : F12.t * F12.t =
    match C12.(Point (x1, y1) + Point (x2, y2)) with
    | C12.Infinity -> failwith "Pairing.c12_add: unexpected infinity"
    | C12.Point (x, y) -> (x, y)

  let post_loop ~q:(qx, qy) ~r ~p f =
    if not Params.apply_post_loop then f
    else
      let q1x = Params.frob12 qx in
      let q1y = Params.frob12 qy in
      let nq2x = Params.frob12 q1x in
      let nq2y = F12.(zero - Params.frob12 q1y) in
      let f = F12.(f * linefunc r (q1x, q1y) p) in
      let r = c12_add r (q1x, q1y) in
      let f = F12.(f * linefunc r (nq2x, nq2y) p) in
      ignore r ;
      f

  let miller_loop (q : C12.t) (p : C12.t) : F12.t =
    match (q, p) with
    | C12.Infinity, _ | _, C12.Infinity -> F12.one
    | C12.Point (qx, qy), C12.Point (px, py) ->
        let qp = (qx, qy) in
        let pp = (px, py) in
        let rec loop i r f =
          if i < 0 then (r, f)
          else
            let f = F12.(f * f * linefunc r r pp) in
            let r = c12_add r r in
            let r, f =
              if Uint.testbit Params.ate_loop_count i then
                (c12_add r qp, F12.(f * linefunc r qp pp))
              else
                (r, f)
            in
            loop (i - 1) r f
        in
        let log_ate_loop_count = Uint.significant_bits Params.ate_loop_count - 2 in
        let r, f = loop log_ate_loop_count qp F12.one in
        let f = post_loop ~q:qp ~r ~p:pp f in
        f12_pow f Params.final_exp_exp

  let pairing_check (pairs : (C12.t * C12.t) list) : bool =
    let result =
      List.fold_left (fun acc (q, p) -> F12.(acc * miller_loop q p)) F12.one pairs
    in
    F12.(result = one)
end
