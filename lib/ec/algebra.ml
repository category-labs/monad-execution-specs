(** Algebraic structures used in elliptic curve cryptography. This includes:
    - Prime fields over the integers.
    - General quotient fields over Euclidean domains.
    - Polynomial rings over arbitrary fields, and polynomial extensions over them.
    - Complex extensions over arbitrary fields.

    Functor types are as follows (ignoring modulus arguments):
    [Quotient_field : EUCLIDEAN_DOMAIN -> FIELD] using the extended Euclidean algorithm for division.
    [Polynomial_ring : FIELD -> EUCLIDEAN_DOMAIN] implementing naive polynomial division.
    [Polynomial_extension : FIELD -> FIELD] is the composition [Quotient_field ∘ Polynomial_ring].
    [Complex_extension : FIELD -> FIELD] using rectangular coordinates to represent elements.
*)

open Numeric

(** The module type of fields, given in terms of binary operations [+], [-], [*], [/]. Unary multiplicative
    inversion [inv] is also provided as part of the signature although it can be derived from [/]. *)
module type FIELD = sig
  (* TODO: all our fields are finite. We could consider adding the field order and characteristic here so we can
     e.g. include the Frobenius automorphisms for polynomial extensions. *)
  type t

  val ( = ) : t -> t -> bool
  val ( <> ) : t -> t -> bool

  val zero : t
  val one : t

  val ( ~$ ) : int -> t
  (** Embed an integer in the field. Note that this can be derived, but all our instances can provide more direct
      implementations than a naive algorithm. *)

  val ( ~@ ) : String.t -> t
  (** Read the input as an unsigned integer and embed it in the field. The input can be arbitrarily long, and is
      not constrained to fit in a machine integer. *)

  val ( + ) : t -> t -> t
  val ( - ) : t -> t -> t
  val ( * ) : t -> t -> t
  val ( / ) : t -> t -> t
  val inv : t -> t
end

(** The module type of Euclidean domains.
    Remember that an Euclidean domain is a ring equipped with a degree function [degree : t ∖ {0} → ℕ ]
    satisfying:
    - Whenever [a, b ∈ t] and [b ≠ 0], there exist [q, r ∈ t] satisfying [a = q × b + r] and either [r = 0] or
    [f(r) < f(b)].
    The choice of degree function is unimportant, but its existence guarantees termination of the Euclidean
    algorithm, which is used to construct quotient fields over the domain. *)
module type EUCLIDEAN_DOMAIN = sig
  type t

  val ( = ) : t -> t -> bool
  val ( <> ) : t -> t -> bool

  val zero : t
  val one : t
  val ( ~@ ) : String.t -> t
  val ( ~$ ) : int -> t

  (* The degree function is never used in the code, but is provided here so that the Euclidean domain condition
     can be stated. *)
  val degree : t -> int

  val ( + ) : t -> t -> t
  val ( - ) : t -> t -> t
  val ( * ) : t -> t -> t
  val div_rem : t -> t -> t * t
end

(** The functor [Quotient_field] constructs a field by quotienting the Euclidean domain [D] by the element
    [Mod.modulus], which is assumed to be irreducible. Field division is implemented via the extended
    Euclidean algorithm. *)
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
  let ( ~$ ) x = reduce D.(~$x)

  let lift_2 f (u : t) (v : t) = reduce (f (u :> impl) (v :> impl))

  let ( + ) = lift_2 D.( + )
  let ( - ) = lift_2 D.( - )
  let ( * ) = lift_2 D.( * )

  (* Compute the Bezout coefficients of two elements in the underlying domain, using the extended Euclidean
     algorithm. The returned GCD is a unit in the underlying field, but is not guaranteed to be 1. *)
  let bezout_coeffs (u : impl) (v : impl) =
    let open D in
    let rec loop (r : impl) a (r' : impl) a' =
      if r' = zero then (a, r)
      else
        let quotient, remainder = div_rem r r' in
        let r, r' = (r', remainder) in
        let a, a' = (a', a - (quotient * a')) in
        loop r a r' a'
    in
    loop u one v zero

  let inv (u : t) : t =
    if u = zero then raise Division_by_zero ;
    let inv_u, gcd = bezout_coeffs (u :> impl) Mod.modulus in
    let inv_u, rem = D.(div_rem inv_u gcd) in
    assert (D.(rem = zero)) ;
    reduce inv_u

  let ( / ) (u : t) (v : t) =
    (* Inline inv to save a reduction. *)
    if v = zero then raise Division_by_zero ;
    let inv_v, gcd = bezout_coeffs (v :> impl) Mod.modulus in
    let inv_v, rem = D.(div_rem inv_v gcd) in
    assert (D.(rem = zero)) ;
    reduce D.((u :> t) * inv_v)
end

(** The functor [Prime_field] constructs the prime field of integers modulo [Mod.modulus]. As with the
    [Quotient_field] functor, primality of [Mod.modulus] is not checked.
    Conditionally, if [Mod.modulus mod 4 = 3], an efficient implementation of modular square root is also
    provided. *)
module Prime_field (Mod : sig
  val modulus : Integer.t
end) =
struct
  include Mod
  module Impl : sig
    type impl = Integer.t
    type t = private impl
    val reduce : impl -> t
    val ( + ) : t -> t -> t
    val ( - ) : t -> t -> t
  end = struct
    type impl = Integer.t
    type t = impl
    let reduce (x : impl) = Integer.modulo x Mod.modulus

    let ( + ) (u : t) (v : t) : t =
      let s = Integer.(u + v) in
      if Integer.(s >= Mod.modulus) then Integer.(s - Mod.modulus) else s
    let ( - ) (u : t) (v : t) : t =
      let s = Integer.(u - v) in
      if Integer.(s < zero) then Integer.(s + Mod.modulus) else s
  end
  include Impl

  let ( = ) (u : t) (v : t) = Integer.((u :> t) = (v :> t))
  let ( <> ) (u : t) (v : t) = Integer.((u :> t) <> (v :> t))

  let zero = reduce Integer.zero
  let one = reduce Integer.one
  let ( ~@ ) str = reduce Integer.(~@str)
  let ( ~$ ) x = reduce Integer.(~$x)

  let ( * ) (u : t) (v : t) = reduce Integer.((u :> t) * (v :> t))

  (* Faster inversion via Zarith. *)
  let inv (u : t) = reduce (Integer.of_z_exn (Z.invert Integer.(to_z (u :> t)) Integer.(to_z modulus)))

  let ( / ) (u : t) (v : t) =
    (* Inline inv to save a reduction. *)
    let inv_v = Integer.of_z_exn (Z.invert Integer.(to_z (v :> t)) Integer.(to_z modulus)) in
    reduce Integer.((u :> t) * inv_v)

  (** [of_uint_opt i] returns the input [i] as an element of this prime field if it is already reduced, or
      None otherwise. Useful for precompile input validation. *)
  let of_uint_opt (i : Uint.t) =
    let i = Uint.as_signed i in
    if Integer.(i >= Mod.modulus) then None else Some (reduce i)

  (** When [Mod.modulus mod 4 = 3], [sqrt_opt] efficiently computes square roots, when they exist. *)
  let sqrt_opt =
    if Integer.(modulo modulus ~$4 = ~$3) then
      let sqrt_exp = Integer.((modulus + one) / ~$4) in
      Some
        (fun (x : t) : t option ->
          if x = zero then Some zero
          else if
            (* Check x really is a square. *)
            Stdlib.(Integer.(legendre (x :> t) modulus) = 1)
          then Some (reduce (Integer.(exp_mod (x :> t)) sqrt_exp ~modulo:modulus))
          else None )
    else None
end

(** The functor [Polynomial_ring] constructs the Euclidean domain of polynomials over an underlying field. *)
module Polynomial_ring (F : FIELD) = struct
  module Impl : sig
    type impl = F.t Iarray.t
    type t = private impl
    val of_coeffs : impl -> t
  end = struct
    (* A polynomial is represented by an array of its non-zero coefficients. To ensure unique representations,
       we require no trailing zeros. *)
    type impl = F.t Iarray.t
    type t = impl

    let of_coeffs (coeffs : impl) =
      let rec loop i = if i >= 0 && F.(Iarray.get coeffs i = zero) then loop (i - 1) else i in
      (* Here, the zero polynomial is given degree -1. *)
      let degree = loop (Iarray.length coeffs - 1) in
      if degree = Iarray.length coeffs - 1 then coeffs
      else Iarray.init (degree + 1) (fun i -> Iarray.get coeffs i)
  end

  include Impl

  (** Number of coefficients in the polynomial [p]. *)
  let length (p : t) = Iarray.length (p :> impl)

  (** Degree of the polynomial [p]. By convention, zero is a -1-degree polynomial. *)
  let degree (p : t) = Stdlib.(length p - 1)

  let init length p_i = of_coeffs (Iarray.init length p_i)

  (** [p.$(i)] returns the i-th coefficient of the polynomial [p], or zero if [i >= length p]. *)
  let ( .$() ) (p : t) i = if i < length p then Iarray.get (p :> impl) i else F.zero

  let ( <> ) (p_1 : t) (p_2 : t) =
    length p_1 <> length p_2 || Iarray.exists2 F.( <> ) (p_1 :> impl) (p_2 :> impl)
  let ( = ) p_1 p_2 = not (p_1 <> p_2)

  let zero = init 0 (fun _ -> F.zero)
  let one = init 1 (fun _ -> F.one)
  let ( ~@ ) i = init 1 (fun _ -> F.(~@i))
  let ( ~$ ) i = init 1 (fun _ -> F.(~$i))

  (** [monomial_x] represents the degree-1 monomial x. *)
  let monomial_x = init 2 (fun i -> if Stdlib.(i = 1) then F.one else F.zero)

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

  let const (a : F.t) = init 1 (fun _ -> a)

  (** [monomial a n] computes the monomial ax^n. *)
  let monomial a n = init Stdlib.(n + 1) (fun i -> if Stdlib.(i = n) then a else F.zero)

  let div_rem u v =
    let n = degree v in
    let v_n_inv = F.(inv v.$(degree v)) in
    let rec loop u quot_acc =
      let m = degree u in
      if m < n then (quot_acc, u)
      else
        let u_m = u.$(degree u) in
        let q = monomial F.(u_m * v_n_inv) Stdlib.(m - n) in
        loop (u - (q * v)) (quot_acc + q)
    in
    loop u zero

  (** [eval p x] evaluates [p] at point [x] efficiently via Horner's rule. *)
  let eval (p : t) (x : F.t) = Iarray.fold_right (fun coeff acc -> F.(coeff + (x * acc))) (p :> impl) F.zero
end

(** For a field of scalars [F], the functor [Polynomial_extension(F)(Mod)] constructs the field of polynomials
    over [F] by quotienting [Polynomial_ring(F)] over the element [Mod.modulus], which is assumed to be
    irreducible.

    Modular reduction is done via the Euclidean method implemented in [Quotient_field]. This could be
    specialized to perform reduction via iterated multiplication and subtraction, but it's hard to do
    functionally. Avoid until it proves a bottleneck. *)
module Polynomial_extension
    (F : FIELD)
    (Mod : sig
      val modulus : Polynomial_ring(F).t
    end) =
struct
  include Mod
  module Underlying_ring = Polynomial_ring (F)
  include Quotient_field (Underlying_ring) (Mod)

  let monomial_x : t = reduce Underlying_ring.monomial_x

  let const (p : F.t) = reduce (Underlying_ring.const p)

  let ( .$() ) (p : t) (i : int) : F.t = Underlying_ring.((p :> t).$(i))

  (** Degree of this extension over [F]. Elements have at most this many coefficients. *)
  let extension_degree = Underlying_ring.degree Mod.modulus

  (** Given a function [f : t -> t] which is assumed to be an automorphism, [automorphism f] constructs a
      potentially more efficient implementation by precomputing the table f(1), f(x), f(x²), ... ahead of time.
      For a polynomial aₙxⁿ + ... + a₀x⁰, [automorphism f] computes aₙf(xⁿ) + ... + a₀f(x⁰) from the
      precomputed terms f(xᵏ). *)
  let automorphism (f : t -> t) : t -> t =
    let f_x = f monomial_x in
    let powers = Seq.iterate (fun f_x_i -> f_x * f_x_i) one |> Seq.take extension_degree |> Iarray.of_seq in
    fun p ->
      (* Do the entire computation in the underlying ring, then reduce. *)
      Underlying_ring.(
        let p = (p :> t) in
        let powers = (powers :> t iarray) in
        let rec loop (i : int) (acc : t) =
          if Stdlib.(i > degree p) then acc
          else loop Stdlib.(i + 1) (acc + (Iarray.get powers i * const p.$(i)))
        in
        loop 0 zero )
      |> reduce

  (** Power function, used for computing Frobenius automorphisms. *)
  let ( ** ) (p : t) (n : Uint.t) =
    let rec loop n p acc =
      if Uint.(n = zero) then acc
      else
        let n, r = Uint.div_rem n Uint.(~$2) in
        let acc = if Uint.(r = one) then acc * p else acc in
        loop n (p * p) acc
    in
    loop n p one
end

(** The functor [Complex_extension] defines the complex extension of a field [F]. This is mathematically
    equivalent to forming a polynomial extension over the polynomial x² + 1, but more efficient. *)
module Complex_extension (F : FIELD) = struct
  type t = {re : F.t; im : F.t}

  let ( = ) (x : t) (y : t) = F.(x.re = y.re) && F.(x.im = y.im)
  let ( <> ) (x : t) (y : t) = F.(x.re <> y.re) || F.(x.im <> y.im)

  let zero = {re = F.zero; im = F.zero}
  let one = {re = F.one; im = F.zero}
  let i = {re = F.zero; im = F.one}

  let ( ~@ ) str = {re = F.(~@str); im = F.zero}
  let ( ~$ ) x = {re = F.(~$x); im = F.zero}

  let real x = {re = x; im = F.zero}
  let imaginary x = {re = F.zero; im = x}

  let conjugate {re; im} = {re; im = F.(zero - im)}
  let norm {re; im} = F.((re * re) + (im * im))

  let ( + ) x y = {re = F.(x.re + y.re); im = F.(x.im + y.im)}
  let ( - ) x y = {re = F.(x.re - y.re); im = F.(x.im - y.im)}
  let ( * ) x y =
    (* This could use Karatsuba multiplication, but in practice it has no impact. *)
    {re = F.((x.re * y.re) - (x.im * y.im)); im = F.((x.re * y.im) + (x.im * y.re))}

  let inv x =
    let x' = conjugate x in
    let nx_inv = F.inv (norm x) in
    {re = F.(x'.re * nx_inv); im = F.(x'.im * nx_inv)}

  let ( / ) x y = x * inv y

  (** When the underlying field provides a square root function, [sqrt_opt] computes square roots in the complex
      extension. Note that unlike in the real case, the complex extension of a prime field does not in general
      have all the square roots. *)
  let sqrt_opt (sqrt_opt : F.t -> F.t option) =
    let two = F.(one + one) in
    fun (v : t) : t option ->
      Option.(
        let {re = a; im = b} = v in
        if F.(b = zero) then
          (* b = 0, return sqrt(a) (which may be imaginary). *)
          match sqrt_opt a with
          | Some y -> return (real y)
          | None ->
              (* Root must be imaginary. *)
              let$ w = sqrt_opt F.(zero - a) in
              return (imaginary w)
        else
          let$ r = sqrt_opt F.((a * a) + (b * b)) in
          let$ c =
            match sqrt_opt F.((a + r) / two) with Some c -> return c | None -> sqrt_opt F.((a - r) / two)
          in
          (* Since b ≠ 0, r cannot be equal to ± a (otherwise we would have a² = r² = a² + b²), therefore
             the division below is always safe. *)
          let d = F.(b / (two * c)) in
          return {re = c; im = d} )
end
