open Numeric
open Algebra

module Make
    (F : FIELD)
    (P : sig
      (* y^2 = x^3 + ax + b *)
      val a : F.t
      val b : F.t
    end) =
struct
  type t = Point of F.t * F.t | Infinity

  let of_coords (x : F.t) (y : F.t) =
    if F.(x = zero) && F.(y = zero) then Some Infinity
    else if F.(y * y = (x * x * x) + (P.a * x) + P.b) then Some (Point (x, y))
    else None

  let three = F.(~@"3")
  let two = F.(~@"2")

  let ( + ) (p_1 : t) (p_2 : t) =
    match (p_1, p_2) with
    | Infinity, _ -> p_2
    | _, Infinity -> p_1
    | Point (x_1, y_1), Point (x_2, y_2) when F.(x_1 <> x_2) ->
        (* YP (250), case x_1 <> x_2 *)
        let lambda = F.((y_2 - y_1) / (x_2 - x_1)) in
        let x = F.((lambda * lambda) - x_1 - x_2) in
        let y = F.((lambda * (x_1 - x)) - y_1) in
        assert (Option.is_some (of_coords x y)) ;
        Point (x, y)
    | Point (_, y_1), Point (_, y_2) when F.(y_1 <> y_2) ->
        (* YP (250), case x_1 = x_2 *)
        Infinity
    | Point (x_1, y_1), Point (_, _) when F.(y_1 <> zero) ->
        (* YP (251), case y_1 = y_2 <> zero *)
        let lambda = F.(((three * x_1 * x_1) + P.a) / (two * y_1)) in
        let x = F.((lambda * lambda) - x_1 - x_1) in
        let y = F.((lambda * (x_1 - x)) - y_1) in
        assert (Option.is_some (of_coords x y)) ;
        Point (x, y)
    | _ ->
        (* YP (251), case y_1 = y_2 = zero *)
        Infinity

  (* YP (252) *)
  let ( * ) (n : Uint.t) (p : t) =
    let rec loop n p acc =
      if Uint.(n = zero) then acc
      else
        let n, rem = Uint.(div_rem n ~$2) in
        let acc = if Uint.(rem = one) then acc + p else acc in
        loop n (p + p) acc
    in
    loop n p Infinity
end
