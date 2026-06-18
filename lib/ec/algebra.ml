open Numeric

(* TODO: all our fields are finite. We could consider adding the field order and characteristic here so we can
   e.g. include the Frobenius automorphisms for polynomial extensions. *)
module type FIELD = sig
  type t

  val ( = ) : t -> t -> bool
  val ( <> ) : t -> t -> bool

  val zero : t
  val one : t

  (* Read the input as an unsigned integer and embed it in the field. This can be derived, but all our instances
     can provide more efficient implementations. *)
  val ( ~@ ) : String.t -> t
  val ( ~$ ) : int -> t

  val ( + ) : t -> t -> t
  val ( - ) : t -> t -> t
  val ( * ) : t -> t -> t
  val ( / ) : t -> t -> t
  val inv : t -> t
end

module type EUCLIDEAN_DOMAIN = sig
  type t

  val ( = ) : t -> t -> bool
  val ( <> ) : t -> t -> bool

  val zero : t
  val one : t
  val ( ~@ ) : String.t -> t
  val ( ~$ ) : int -> t

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
  let ( ~$ ) x = reduce D.(~$x)

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

  let inv (u : t) : t =
    let inv_u, _inv_mod, gcd = bezout_coeffs (u :> D.t) Mod.modulus in
    let inv_u, rem = D.(div_rem inv_u gcd) in
    assert (D.(rem = zero)) ;
    reduce inv_u

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
  module Impl : sig
    type impl = Integer.t
    type t = private impl
    val reduce : impl -> t
    val ( + ) : t -> t -> t
    val ( - ) : t -> t -> t
  end = struct
    type impl = Integer.t
    type t = impl
    let reduce (x : impl) = Integer.remainder x Mod.modulus

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
    let inv_v = Integer.of_z_exn (Z.invert Integer.(to_z (v :> t)) Integer.(to_z modulus)) in
    reduce Integer.((u :> t) * inv_v)

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
  let ( ~$ ) i = trim (Iarray.init 1 (fun _ -> F.(~$i)))
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

  (* Point evaluation via Horner's rule. *)
  let eval (p : t) (x : F.t) =
    Iarray.fold_right (fun coeff acc -> F.(coeff + (x * acc))) (p :> F.t Iarray.t) F.zero
end

(* Polynomial field extensions over a field of scalars. This could be specialized to perform reduction via
   multiplication and addition, but performance improvements are limited to the pairing check
   precompiles. TODO: double-check that this is true. *)
module Polynomial_extension_slow
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

  (* Degree of this extension over F. Elements have exactly this many coefficients. *)
  let extension_degree = Underlying_ring.degree Mod.modulus

  (* Apply an automorphism f given its action on the basis element x. This is made more efficient by
     precomputing the table f(1), f(x), f(x²), ... ahead of time. *)
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

  (* Power function, used for computing Frobenius automorphisms. *)
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

(* Polynomial field extensions over a field, but fast. *)
module Polynomial_extension_fast
    (F : FIELD)
    (Mod : sig
      val modulus : Polynomial_ring(F).t
    end) =
struct
  include Mod
  module Underlying_ring = Polynomial_ring (F)
  module Impl : sig
    type impl = Underlying_ring.t
    type t = private impl
    val reduce : impl -> t
    val ( + ) : t -> t -> t
    val ( - ) : t -> t -> t
  end = struct
    type impl = Underlying_ring.t
    type t = impl
    let reduce (x : impl) = snd (Underlying_ring.div_rem x Mod.modulus)

    let ( + ) (u : t) (v : t) : t = Underlying_ring.(u + v)
    let ( - ) (u : t) (v : t) : t = Underlying_ring.(u - v)
  end
  include Impl

  let ( = ) (u : t) (v : t) = Underlying_ring.((u :> t) = (v :> t))
  let ( <> ) (u : t) (v : t) = Underlying_ring.((u :> t) <> (v :> t))

  let zero = reduce Underlying_ring.zero
  let one = reduce Underlying_ring.one
  let ( ~@ ) str = reduce Underlying_ring.(~@str)
  let ( ~$ ) x = reduce Underlying_ring.(~$x)

  let extension_degree = Underlying_ring.degree modulus

  let modulus_coefficients =
    let open Underlying_ring in
    let beta = modulus.$(extension_degree) in
    Iarray.to_seqi (modulus :> F.t iarray)
    |> Seq.take extension_degree
    |> Seq.filter_map (fun (i, alpha_i) ->
        if F.(alpha_i = zero) then None
        else
          let w = F.(alpha_i / beta) in
          Some (i, w) )
    |> List.of_seq

  let ( * ) (u : t) (v : t) =
    let u = (u :> F.t Iarray.t) in
    let v = (v :> F.t Iarray.t) in
    (* Try to avoid as many multiplications as possible. *)
    let u, v =
      let lu, lv = (Iarray.length u, Iarray.length v) in
      let count_muls (arr : F.t iarray) (n : int) =
        let rec loop (i : int) (acc : int) =
          if i >= Iarray.length arr then acc
          else loop Stdlib.(i + 1) (if F.(Iarray.get arr i = zero) then acc else Stdlib.(acc + n))
        in
        loop 0 0
      in
      let u_muls = count_muls u lv in
      let v_muls = count_muls v lu in
      if u_muls > v_muls then (v, u) else (u, v)
    in

    let l = Stdlib.(Iarray.length (u :> F.t iarray) + Iarray.length (v :> F.t iarray) - 1) in
    let arr = Array.make l F.zero in

    for i = 0 to Stdlib.(Iarray.length u - 1) do
      let u_i = Iarray.get u i in
      if F.(u_i <> zero) then
        for j = 0 to Stdlib.(Iarray.length v - 1) do
          let v_j = Iarray.get v j in
          let k = Stdlib.(i + j) in
          arr.(k) <- F.(arr.(k) + (u_i * v_j))
        done
    done ;

    for i = Stdlib.(l - 1) downto extension_degree do
      (* Sparse reduction. *)
      List.iter
        (fun (j, w_j) ->
          let k = Stdlib.(i - extension_degree + j) in
          arr.(k) <- F.(arr.(k) - (arr.(i) * w_j)) )
        modulus_coefficients
    done ;

    (* hehe *)
    let prod_len =
      let rec loop i =
        if Stdlib.(i < 0) then 0 else if F.(arr.(i) <> zero) then Stdlib.(i + 1) else loop Stdlib.(i - 1)
      in
      loop Stdlib.(min l extension_degree - 1)
    in
    Obj.magic (Iarray.init prod_len (fun i -> arr.(i)))
  (*
    reduce Underlying_ring.(trim (Iarray.of_array arr))
     *)

  (* Compute the Bezout coefficients of two elements in the underlying domain, using the extended Euclidean
     algorithm.
     This does more work than necessary as we are only interested in one coefficient.
   *)
  let bezout_coeffs (u : Underlying_ring.t) (v : Underlying_ring.t) =
    let open Underlying_ring in
    let rec loop (r : t) (a, b) (r' : t) (a', b') =
      if r' = zero then (a, b, r)
      else
        let quotient, remainder = div_rem r r' in
        let r, r' = (r', remainder) in
        let a, a' = (a', a - (quotient * a')) in
        let b, b' = (b', b - (quotient * b')) in
        loop r (a, b) r' (a', b')
    in
    loop u (one, zero) v (zero, one)

  let inv (u : t) : t =
    let inv_u, _inv_mod, gcd = bezout_coeffs (u :> Underlying_ring.t) Mod.modulus in
    let inv_u, rem = Underlying_ring.(div_rem inv_u gcd) in
    assert (Underlying_ring.(rem = zero)) ;
    reduce inv_u

  let ( / ) (u : t) (v : t) =
    let inv_v, _inv_mod, gcd = bezout_coeffs (v :> Underlying_ring.t) Mod.modulus in
    let inv_v, rem = Underlying_ring.(div_rem inv_v gcd) in
    assert (Underlying_ring.(rem = zero)) ;
    reduce Underlying_ring.((u :> t) * inv_v)

  let monomial_x : t = reduce Underlying_ring.monomial_x

  let const (p : F.t) = reduce (Underlying_ring.const p)

  let ( .$() ) (p : t) (i : int) : F.t = Underlying_ring.((p :> t).$(i))

  (* Degree of this extension over F. Elements have exactly this many coefficients. *)
  let extension_degree = Underlying_ring.degree Mod.modulus

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

  (* Power function, used for computing Frobenius automorphisms. *)
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

module Polynomial_extension
    (F : FIELD)
    (Mod : sig
      val modulus : Polynomial_ring(F).t
    end) =
  Polynomial_extension_fast (F) (Mod)

(* Complex field extensions over a field. Equivalent to a polynomial extension, but more efficient. *)
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
    (* This could use Karatsuba multiplication, but in practice it has no impact. TODO: double-check. *)
    {re = F.((x.re * y.re) - (x.im * y.im)); im = F.((x.re * y.im) + (x.im * y.re))}

  let inv x =
    let x' = conjugate x in
    let nx_inv = F.inv (norm x) in
    {re = F.(x'.re * nx_inv); im = F.(x'.im * nx_inv)}

  let ( / ) x y = x * inv y

  (* When the underlying field supports efficient square roots, then so does its complex extension. *)
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
          let d = F.(b / (two * c)) in
          return {re = c; im = d} )
end
