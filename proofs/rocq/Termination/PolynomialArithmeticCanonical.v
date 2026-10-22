(** Generated polynomial constructors preserve the trimmed-list invariant.
    These facts use the checked [of_coeffs] normalizer and make no field-law
    assumption about addition, subtraction, or multiplication. *)

From Stdlib Require Import ZArith.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import MonadVM.Ec.Algebra.
Require Import MonadExecutionSpecs.Termination.PolynomialDegree.
Require Import MonadExecutionSpecs.Termination.PolynomialOfCoeffs.

Local Open Scope Z_scope.

Section ArithmeticCanonical.
  Context {F_t : Set}
    {F : @MonadVM.Ec.Algebra.Polynomial_ring.FArgs F_t}.
  Context `{Uarray :
    RocqOfOCaml.Basics.Unreachable (RocqOfOCaml.OCamlIarray.t F_t)}.
  Context `{Ufield : RocqOfOCaml.Basics.Unreachable F_t}.

  Let canonical :=
    @MonadExecutionSpecs.Termination.PolynomialDegree.canonical_polynomial
      F_t F Ufield.

  Lemma generated_init_canonical_all (count : Z) (coefficient : Z -> F_t) :
    canonical
      (@MonadVM.Ec.Algebra.Polynomial_ring.init F_t F
        Uarray Uarray Ufield count coefficient).
  Proof.
    unfold MonadVM.Ec.Algebra.Polynomial_ring.init.
    apply generated_of_coeffs_canonical_all.
  Qed.

  Lemma generated_plus_canonical_all (left right : list F_t) :
    canonical
      (@MonadVM.Ec.Algebra.Polynomial_ring.op_plus F_t F
        Uarray Uarray Ufield left right).
  Proof.
    unfold MonadVM.Ec.Algebra.Polynomial_ring.op_plus.
    apply generated_init_canonical_all.
  Qed.

  Lemma generated_minus_canonical_all (left right : list F_t) :
    canonical
      (@MonadVM.Ec.Algebra.Polynomial_ring.op_minus F_t F
        Uarray Uarray Ufield left right).
  Proof.
    unfold MonadVM.Ec.Algebra.Polynomial_ring.op_minus.
    apply generated_init_canonical_all.
  Qed.

  Lemma generated_star_canonical_all (left right : list F_t) :
    canonical
      (@MonadVM.Ec.Algebra.Polynomial_ring.op_star F_t F
        Uarray Uarray Ufield left right).
  Proof.
    unfold MonadVM.Ec.Algebra.Polynomial_ring.op_star.
    cbn -[Fix Fix_F].
    destruct
      (orb
        (equiv_decb
          (@MonadVM.Ec.Algebra.Polynomial_ring.length F_t F left) 0)
        (equiv_decb
          (@MonadVM.Ec.Algebra.Polynomial_ring.length F_t F right) 0)).
    - unfold MonadVM.Ec.Algebra.Polynomial_ring.zero.
      apply generated_of_coeffs_canonical_all.
    - apply generated_init_canonical_all.
  Qed.
End ArithmeticCanonical.
