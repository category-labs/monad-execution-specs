(** Representation facts for the generated polynomial ring. These support
    future proofs that the algebraic recursion guards are unreachable for
    lawful field instances. *)

From Stdlib Require Import ZArith Lia.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import MonadVM.Ec.Algebra.
Require Import MonadExecutionSpecs.Termination.Ec.

Local Open Scope Z_scope.

Section PolynomialDegree.
  Context {F_t : Set}
    {F : @MonadVM.Ec.Algebra.Polynomial_ring.FArgs F_t}.
  Context `{Uarray :
    RocqOfOCaml.Basics.Unreachable (RocqOfOCaml.OCamlIarray.t F_t)}.
  Context `{Ufield : RocqOfOCaml.Basics.Unreachable F_t}.
  Context `{Ubool : RocqOfOCaml.Basics.Unreachable bool}.

  Lemma generated_polynomial_degree_lower_bound
      (polynomial : @MonadVM.Ec.Algebra.Polynomial_ring.t F_t F) :
    -1 <= @MonadVM.Ec.Algebra.Polynomial_ring.degree F_t F polynomial.
  Proof.
    unfold MonadVM.Ec.Algebra.Polynomial_ring.degree,
      MonadVM.Ec.Algebra.Polynomial_ring.length,
      RocqOfOCaml.OCamlIarray.length.
    lia.
  Qed.

  Lemma generated_polynomial_zero_is_empty :
    @MonadVM.Ec.Algebra.Polynomial_ring.zero F_t F
      Uarray Uarray Ufield = nil.
  Proof.
    reflexivity.
  Qed.

  Lemma generated_polynomial_zero_degree :
    @MonadVM.Ec.Algebra.Polynomial_ring.degree F_t F
      (@MonadVM.Ec.Algebra.Polynomial_ring.zero F_t F
        Uarray Uarray Ufield) = -1.
  Proof.
    rewrite generated_polynomial_zero_is_empty.
    reflexivity.
  Qed.

  Lemma generated_polynomial_eq_zero_sound
      (polynomial : @MonadVM.Ec.Algebra.Polynomial_ring.t F_t F) :
    @MonadVM.Ec.Algebra.Polynomial_ring.op_eq F_t F Ubool
      polynomial
      (@MonadVM.Ec.Algebra.Polynomial_ring.zero F_t F
        Uarray Uarray Ufield) = true ->
    polynomial =
      @MonadVM.Ec.Algebra.Polynomial_ring.zero F_t F
        Uarray Uarray Ufield.
  Proof.
    rewrite generated_polynomial_zero_is_empty.
    destruct polynomial as [|head tail]; [reflexivity|].
    unfold MonadVM.Ec.Algebra.Polynomial_ring.op_eq,
      MonadVM.Ec.Algebra.Polynomial_ring.op_ltgt,
      MonadVM.Ec.Algebra.Polynomial_ring.length,
      RocqOfOCaml.OCamlIarray.length.
    cbn. discriminate.
  Qed.

  Lemma generated_polynomial_nonzero_degree
      (polynomial : @MonadVM.Ec.Algebra.Polynomial_ring.t F_t F) :
    @MonadVM.Ec.Algebra.Polynomial_ring.op_eq F_t F Ubool
      polynomial
      (@MonadVM.Ec.Algebra.Polynomial_ring.zero F_t F
        Uarray Uarray Ufield) = false ->
    0 <= @MonadVM.Ec.Algebra.Polynomial_ring.degree F_t F polynomial.
  Proof.
    rewrite generated_polynomial_zero_is_empty.
    destruct polynomial as [|head tail].
    - unfold MonadVM.Ec.Algebra.Polynomial_ring.op_eq,
        MonadVM.Ec.Algebra.Polynomial_ring.op_ltgt,
        MonadVM.Ec.Algebra.Polynomial_ring.length,
        RocqOfOCaml.OCamlIarray.length.
      cbn. discriminate.
    - intro Hunused.
      change (0 <= Z.of_nat (S (Datatypes.length tail)) - 1).
      rewrite Nat2Z.inj_succ.
      lia.
  Qed.

  (** The generated carrier is an unrestricted list. A singleton is therefore
      classified as nonzero by length alone, even when its coefficient is the
      field zero. Native [Polynomial_ring.t] only exposes trimmed values. *)
  Lemma generated_singleton_unequal_zero (coefficient : F_t) :
    @MonadVM.Ec.Algebra.Polynomial_ring.op_eq F_t F Ubool
      (coefficient :: nil)
      (@MonadVM.Ec.Algebra.Polynomial_ring.zero F_t F
        Uarray Uarray Ufield) = false.
  Proof.
    rewrite generated_polynomial_zero_is_empty.
    unfold MonadVM.Ec.Algebra.Polynomial_ring.op_eq,
      MonadVM.Ec.Algebra.Polynomial_ring.op_ltgt,
      MonadVM.Ec.Algebra.Polynomial_ring.length,
      RocqOfOCaml.OCamlIarray.length.
    reflexivity.
  Qed.

  Lemma generated_singleton_degree (coefficient : F_t) :
    @MonadVM.Ec.Algebra.Polynomial_ring.degree F_t F
      (coefficient :: nil) = 0.
  Proof. reflexivity. Qed.

  Let Polynomial := @MonadVM.Ec.Algebra.Polynomial_ring.t F_t F.
  Let polynomial_zero :=
    @MonadVM.Ec.Algebra.Polynomial_ring.zero F_t F
      Uarray Uarray Ufield.
  Let polynomial_equal :=
    @MonadVM.Ec.Algebra.Polynomial_ring.op_eq F_t F Ubool.
  Let polynomial_degree :=
    @MonadVM.Ec.Algebra.Polynomial_ring.degree F_t F.
  Let field := @MonadVM.Ec.Algebra.Polynomial_ring.F F_t F.
  Let field_zero := field.(MonadVM.Ec.Algebra.FIELD.zero).
  Let field_equal := field.(MonadVM.Ec.Algebra.FIELD.op_eq).
  Let leading_coefficient (polynomial : Polynomial) :=
    @MonadVM.Ec.Algebra.Polynomial_ring.op_pointdollarlparenrparen
      F_t F Ufield polynomial (polynomial_degree polynomial).

  (** This is the source-level invariant hidden by the native private type.
      It must be proved for outputs of [of_coeffs] and then preserved by the
      arithmetic operations before applying field cancellation laws. *)
  Definition canonical_polynomial (polynomial : Polynomial) : Prop :=
    polynomial = nil \/
      field_equal (leading_coefficient polynomial) field_zero = false.

  Lemma canonical_polynomial_zero :
    canonical_polynomial polynomial_zero.
  Proof.
    left. apply generated_polynomial_zero_is_empty.
  Qed.

  Lemma canonical_polynomial_singleton (coefficient : F_t) :
    canonical_polynomial (coefficient :: nil) <->
      field_equal coefficient field_zero = false.
  Proof.
    unfold canonical_polynomial, leading_coefficient,
      polynomial_degree.
    simpl.
    split.
    - intros [Hnil | Hnonzero]; [discriminate | exact Hnonzero].
    - intro Hnonzero. right. exact Hnonzero.
  Qed.

  Lemma padded_zero_not_canonical :
    field_equal field_zero field_zero = true ->
    ~ canonical_polynomial (field_zero :: nil).
  Proof.
    intros Hreflexive Hcanonical.
    apply canonical_polynomial_singleton in Hcanonical.
    rewrite Hreflexive in Hcanonical. discriminate.
  Qed.

  Lemma generated_of_coeffs_singleton (coefficient : F_t) :
    @MonadVM.Ec.Algebra.Polynomial_ring.of_coeffs F_t F Ufield Uarray
      (coefficient :: nil) =
    if field_equal coefficient field_zero
    then nil else coefficient :: nil.
  Proof.
    destruct (field_equal coefficient field_zero) eqn:Hzero;
      cbn; unfold MonadVM.Ec.Algebra.Polynomial_ring.Impl.of_coeffs;
      cbn; unfold field_equal, field_zero, field in Hzero;
      rewrite Hzero; vm_compute; reflexivity.
  Qed.

  Lemma generated_of_coeffs_singleton_canonical (coefficient : F_t) :
    canonical_polynomial
      (@MonadVM.Ec.Algebra.Polynomial_ring.of_coeffs F_t F Ufield Uarray
        (coefficient :: nil)).
  Proof.
    rewrite generated_of_coeffs_singleton.
    destruct (field_equal coefficient field_zero) eqn:Hzero.
    - left. reflexivity.
    - apply canonical_polynomial_singleton. exact Hzero.
  Qed.

  Lemma generated_polynomial_euclidean_laws
      (div_rem : Polynomial -> Polynomial -> Polynomial * Polynomial) :
    (forall x y quotient remainder,
      polynomial_equal y polynomial_zero = false ->
      div_rem x y = (quotient, remainder) ->
      polynomial_equal remainder polynomial_zero = true \/
        polynomial_degree remainder < polynomial_degree y) ->
    @MonadExecutionSpecs.Termination.Ec.euclidean_degree_laws
      Polynomial polynomial_equal polynomial_zero polynomial_degree div_rem.
  Proof.
    intro Hremainder.
    constructor.
    - apply generated_polynomial_zero_degree.
    - intros x Hzero.
      apply generated_polynomial_eq_zero_sound. exact Hzero.
    - intros x Hnonzero.
      apply generated_polynomial_nonzero_degree. exact Hnonzero.
    - exact Hremainder.
  Qed.
End PolynomialDegree.
