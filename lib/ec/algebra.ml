open Numeric

module type FIELD = sig
  type t

  val ( = ) : t -> t -> bool
  val ( <> ) : t -> t -> bool

  val zero : t
  val one : t

  (* Read the input as an unsigned integer and embed it in the field. This can be derived, but all our instances
     can provide more efficient implementations. *)
  val ( ~@ ) : String.t -> t

  val ( + ) : t -> t -> t
  val ( - ) : t -> t -> t
  val ( * ) : t -> t -> t
  val ( / ) : t -> t -> t
end

module type EUCLIDEAN_DOMAIN = sig
  type t

  val ( = ) : t -> t -> bool
  val ( <> ) : t -> t -> bool

  val zero : t
  val one : t
  val ( ~@ ) : String.t -> t

  val ( + ) : t -> t -> t
  val ( - ) : t -> t -> t
  val ( * ) : t -> t -> t
  val div_rem : t -> t -> t * t
end

module Quotient_field
    (D : EUCLIDEAN_DOMAIN)
    (Mod : sig
      (* modulus must be an irreducible element in D, but there is no general way to assert this. *)
      val modulus : D.t
    end) : sig
  include FIELD with type t = private D.t
  val reduce : D.t -> t
end = struct
  module Impl : sig
    type impl = D.t
    type t = private impl
    val reduce : impl -> t
  end = struct
    type impl = D.t
    type t = impl
    let reduce (x : impl) =
      let _quot, rem = D.div_rem x Mod.modulus in
      rem
  end
  include Impl

  let ( = ) (u : t) (v : t) = D.((u :> t) = (v :> t))
  let ( <> ) (u : t) (v : t) = D.((u :> t) <> (v :> t))

  let zero = reduce D.zero
  let one = reduce D.one
  let ( ~@ ) str = reduce D.(~@str)

  let lift_2 f (u : t) (v : t) = reduce (f (u :> D.t) (v :> D.t))

  let ( + ) = lift_2 D.( + )
  let ( - ) = lift_2 D.( - )
  let ( * ) = lift_2 D.( * )

  (* Compute the Bezout coefficients of two elements in the underlying domain, using the extended Euclidean
     algorithm.
     This does more work than necessary as we are only interested in one coefficient.
   *)
  let bezout_coeffs (u : D.t) (v : D.t) =
    let open D in
    let rec loop (r : D.t) (a, b) (r' : D.t) (a', b') =
      if r' = zero then (a, b, r)
      else
        let quotient, remainder = div_rem r r' in
        let r, r' = (r', remainder) in
        let a, a' = (a', a - (quotient * a')) in
        let b, b' = (b', b - (quotient * b')) in
        loop r (a, b) r' (a', b')
    in
    loop u (one, zero) v (zero, one)

  let ( / ) (u : t) (v : t) =
    let inv_v, _inv_mod, gcd = bezout_coeffs (v :> D.t) Mod.modulus in
    let inv_v, rem = D.(div_rem inv_v gcd) in
    assert (D.(rem = zero)) ;
    reduce D.((u :> t) * inv_v)
end

(* Prime fields over a prime modulus. We do not check primality. We also require modulus mod 4 = 3 to implement
   sqrt. *)
module Prime_field (Mod : sig
  val modulus : Integer.t
end) =
struct
  include Mod
  include Quotient_field (Integer) (Mod)

  (* Returns None if the input is not already reduced. Useful for precompile input validation. *)
  let of_uint_opt (i : Uint.t) =
    let i = Uint.as_signed i in
    if Integer.(i >= Mod.modulus) then None else Some (reduce i)

  (* When modulo mod 4 = 3, we can efficiently compute square roots. *)
  let sqrt_opt =
    if Integer.(modulo modulus ~$4 = ~$3) then
      let sqrt_exp = Integer.((modulus + one) / ~$4) in
      Some
        (fun (x : t) : t option ->
          (* Check x really is a square. *)
          if Stdlib.(Integer.(legendre (x :> Integer.t) modulus) = 1) then
            Some (reduce (Integer.pow_mod (x :> Integer.t) sqrt_exp modulus))
          else None )
    else None
end

(* Polynomial ring over a field. *)
module Polynomial_ring (F : FIELD) = struct
  module Impl : sig
    type impl = F.t Iarray.t
    type t = private impl
    val trim : F.t Iarray.t -> t
  end = struct
    (* A polynomial is represented by an array of its non-zero coefficients. To ensure unique representations,
       we require no trailing zeros. *)
    type impl = F.t Iarray.t
    type t = impl

    let trim (coeffs : F.t Iarray.t) =
      let rec loop i = if i >= 0 && F.(Iarray.get coeffs i = zero) then loop (i - 1) else i in
      (* Here, the zero polynomial is given degree -1. *)
      let degree = loop (Iarray.length coeffs - 1) in
      if degree = Iarray.length coeffs - 1 then coeffs
      else Iarray.init (degree + 1) (fun i -> Iarray.get coeffs i)
  end

  include Impl

  let length (p : t) = Iarray.length (p :> impl)

  (* By convention, zero is a -1-degree polynomial. *)
  let degree (p : t) = Stdlib.(length p - 1)
  let init length p_i = trim (Iarray.init length p_i)

  let ( .$() ) (p : t) i = if i < length p then Iarray.get (p :> F.t Iarray.t) i else F.zero

  let ( <> ) (p_1 : t) (p_2 : t) =
    length p_1 <> length p_2 || Iarray.exists2 F.( <> ) (p_1 :> F.t Iarray.t) (p_2 :> F.t Iarray.t)
  let ( = ) p_1 p_2 = not (p_1 <> p_2)

  let zero = trim (Iarray.init 0 (fun _ -> F.zero))
  let one = trim (Iarray.init 1 (fun _ -> F.one))
  let ( ~@ ) i = trim (Iarray.init 1 (fun _ -> F.(~@i)))
  let monomial_x = trim (Iarray.init 2 (fun i -> if Stdlib.(i = 1) then F.one else F.zero))

  let ( + ) (p_1 : t) (p_2 : t) = init (max (length p_1) (length p_2)) (fun i -> F.(p_1.$(i) + p_2.$(i)))

  let ( - ) (p_1 : t) (p_2 : t) = init (max (length p_1) (length p_2)) (fun i -> F.(p_1.$(i) - p_2.$(i)))

  let ( * ) (p_1 : t) (p_2 : t) =
    let len_1 = length p_1 in
    let len_2 = length p_2 in
    if Stdlib.(len_1 = 0 || len_2 = 0) then zero
    else
      init
        Stdlib.(len_1 + len_2 - 1)
        (fun i ->
          let rec loop j acc =
            let k = Stdlib.(i - j) in
            if j < 0 || k >= len_2 then acc else loop Stdlib.(j - 1) F.(acc + (p_1.$(j) * p_2.$(k)))
          in
          loop Stdlib.(min i (len_1 - 1)) F.zero )

  let const (a : F.t) = trim (Iarray.init 1 (fun _ -> a))

  (* Computes the monomial ax^n. *)
  let monomial a n = init Stdlib.(n + 1) (fun i -> if Stdlib.(i = n) then a else F.zero)

  let div_rem u v =
    let n = degree v in
    let rec loop u quot_acc =
      let m = degree u in
      if m < n then (quot_acc, u)
      else
        let u_m = u.$(degree u) in
        let v_n = v.$(degree v) in
        let q = monomial F.(u_m / v_n) Stdlib.(m - n) in
        loop (u - (q * v)) (quot_acc + q)
    in
    loop u zero
end

module Polynomial (F : FIELD) = struct
  module Poly = Polynomial_ring (F)
  module type SIG = sig
    val modulus : Poly.t
  end
end

(* Polynomial field extensions over a field. *)
module Polynomial_extension
    (F : FIELD)
    (Mod : sig
      val modulus : Polynomial_ring(F).t
    end) =
struct
  module Underlying_ring = Polynomial_ring (F)

  include Quotient_field (Underlying_ring) (Mod)

  let monomial_x : t = reduce Underlying_ring.monomial_x

  let const (p : F.t) = reduce (Underlying_ring.const p)

  let ( .$() ) (p : t) (i : int) : F.t = Underlying_ring.((p :> t).$(i))
end
