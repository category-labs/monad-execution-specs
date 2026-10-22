(** Length bounds for generated polynomial arithmetic. These do not assume
    field laws: normalization can only shorten the raw coefficient array. *)

From Stdlib Require Import ZArith Bool Lia.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import MonadVM.Ec.Algebra.
Require Import MonadExecutionSpecs.Termination.PolynomialOfCoeffs.

Local Open Scope Z_scope.

Section ArithmeticBounds.
  Context {F_t : Set}
    {F : @MonadVM.Ec.Algebra.Polynomial_ring.FArgs F_t}.
  Context `{Uarray :
    RocqOfOCaml.Basics.Unreachable (RocqOfOCaml.OCamlIarray.t F_t)}.
  Context `{Ufield : RocqOfOCaml.Basics.Unreachable F_t}.

  Let length := @MonadVM.Ec.Algebra.Polynomial_ring.length F_t F.
  Let degree := @MonadVM.Ec.Algebra.Polynomial_ring.degree F_t F.

  Lemma generated_polynomial_init_length_le
      (count : Z) (coefficient : Z -> F_t) :
    0 <= count ->
    length
      (@MonadVM.Ec.Algebra.Polynomial_ring.init F_t F
        Uarray Uarray Ufield count coefficient) <= count.
  Proof.
    intro Hcount.
    unfold MonadVM.Ec.Algebra.Polynomial_ring.init.
    eapply Z.le_trans.
    - apply generated_of_coeffs_length_le.
    - destruct (Z.eq_dec count 0) as [Hzero | Hnonzero].
      + change (count = 0) in Hzero.
        subst count. reflexivity.
      + change (count <> 0) in Hnonzero.
        replace count with ((count - 1) + 1) by lia.
        rewrite generated_init_length by lia.
        lia.
  Qed.

  Lemma generated_polynomial_product_length_le
      (left right : list F_t) :
    0 < length left ->
    0 < length right ->
    length
      (@MonadVM.Ec.Algebra.Polynomial_ring.op_star F_t F
        Uarray Uarray Ufield left right) <=
      length left + length right - 1.
  Proof.
    intros Hleft Hright.
    unfold MonadVM.Ec.Algebra.Polynomial_ring.op_star.
    cbn -[Fix Fix_F].
    destruct
      (orb
        (equiv_decb (length left) 0)
        (equiv_decb (length right) 0)) eqn:Hzero.
    - apply Bool.orb_true_iff in Hzero.
      destruct Hzero as [Hzero | Hzero].
      + change ((if Z.eq_dec (length left) 0 then true else false) = true)
          in Hzero.
        destruct (Z.eq_dec (length left) 0) as [Heq | Hneq].
        * change (length left = 0) in Heq. lia.
        * discriminate.
      + change ((if Z.eq_dec (length right) 0 then true else false) = true)
          in Hzero.
        destruct (Z.eq_dec (length right) 0) as [Heq | Hneq].
        * change (length right = 0) in Heq. lia.
        * discriminate.
    - unfold length in Hzero.
      rewrite Hzero.
      apply generated_polynomial_init_length_le.
      lia.
  Qed.

  Lemma generated_polynomial_product_length_le_right_positive
      (left right : list F_t) :
    0 < length right ->
    length
      (@MonadVM.Ec.Algebra.Polynomial_ring.op_star F_t F
        Uarray Uarray Ufield left right) <=
      length left + length right - 1.
  Proof.
    intro Hright.
    destruct left as [|head tail].
    - change (0 <= length right - 1).
      lia.
    - apply generated_polynomial_product_length_le.
      + unfold length, MonadVM.Ec.Algebra.Polynomial_ring.length,
          RocqOfOCaml.OCamlIarray.length.
        simpl. lia.
      + exact Hright.
  Qed.

  Lemma generated_monomial_length_le
      (coefficient : F_t) (power : Z) :
    0 <= power ->
    length
      (@MonadVM.Ec.Algebra.Polynomial_ring.monomial F_t F
        Uarray Uarray Ufield coefficient power) <= power + 1.
  Proof.
    intro Hpower.
    unfold MonadVM.Ec.Algebra.Polynomial_ring.monomial.
    apply generated_polynomial_init_length_le.
    lia.
  Qed.

  (** The product subtracted in a division step cannot extend beyond the
      dividend's final coefficient, even if the monomial normalizes to zero. *)
  Lemma generated_division_product_length_le
      (divisor : list F_t) (coefficient : F_t) (m : Z) :
    let n := degree divisor in
    0 <= n ->
    n <= m ->
    length
      (@MonadVM.Ec.Algebra.Polynomial_ring.op_star F_t F
        Uarray Uarray Ufield
        (@MonadVM.Ec.Algebra.Polynomial_ring.monomial F_t F
          Uarray Uarray Ufield coefficient (m - n)) divisor) <= m + 1.
  Proof.
    cbn beta zeta.
    intros Hn Hm.
    pose proof
      (generated_monomial_length_le coefficient
        (m - degree divisor) ltac:(lia)) as Hmonomial.
    pose proof
      (generated_polynomial_product_length_le_right_positive
        (@MonadVM.Ec.Algebra.Polynomial_ring.monomial F_t F
          Uarray Uarray Ufield coefficient (m - degree divisor))
        divisor) as Hproduct.
    assert (Hdivisor : 0 < length divisor).
    { unfold degree, MonadVM.Ec.Algebra.Polynomial_ring.degree in Hn.
      change
        (0 < @MonadVM.Ec.Algebra.Polynomial_ring.length F_t F divisor).
      assert (Hpositive_int : forall x : Z, 0 <= x - 1 -> 0 < x)
        by lia.
      exact (Hpositive_int _ Hn). }
    specialize (Hproduct Hdivisor).
    unfold degree, MonadVM.Ec.Algebra.Polynomial_ring.degree in Hn.
    assert (Hdegree_length :
      degree divisor = length divisor - 1) by reflexivity.
    lia.
  Qed.

  Corollary generated_division_product_degree_le
      (divisor : list F_t) (coefficient : F_t) (m : Z) :
    let n := degree divisor in
    0 <= n ->
    n <= m ->
    degree
      (@MonadVM.Ec.Algebra.Polynomial_ring.op_star F_t F
        Uarray Uarray Ufield
        (@MonadVM.Ec.Algebra.Polynomial_ring.monomial F_t F
          Uarray Uarray Ufield coefficient (m - n)) divisor) <= m.
  Proof.
    cbn beta zeta.
    intros Hn Hm.
    pose proof
      (generated_division_product_length_le divisor coefficient m Hn Hm)
      as Hlength.
    unfold degree, MonadVM.Ec.Algebra.Polynomial_ring.degree.
    change
      (length
        (@MonadVM.Ec.Algebra.Polynomial_ring.op_star F_t F
          Uarray Uarray Ufield
          (@MonadVM.Ec.Algebra.Polynomial_ring.monomial F_t F
            Uarray Uarray Ufield coefficient (m - degree divisor))
          divisor) - 1 <= m).
    lia.
  Qed.

  (** The remaining premise is field-specific leading-term cancellation.
      The array-length and normalization parts hold for any field record. *)
  Theorem generated_division_step_degree_drops_if_lead_zero
      (dividend divisor : list F_t) (coefficient : F_t) :
    let m := degree dividend in
    let n := degree divisor in
    let product :=
      @MonadVM.Ec.Algebra.Polynomial_ring.op_star F_t F
        Uarray Uarray Ufield
        (@MonadVM.Ec.Algebra.Polynomial_ring.monomial F_t F
          Uarray Uarray Ufield coefficient (m - n)) divisor in
    0 <= n ->
    n <= m ->
    (@MonadVM.Ec.Algebra.Polynomial_ring.F F_t F).(MonadVM.Ec.Algebra.FIELD.op_eq)
      ((@MonadVM.Ec.Algebra.Polynomial_ring.F F_t F).(MonadVM.Ec.Algebra.FIELD.op_minus)
        (@MonadVM.Ec.Algebra.Polynomial_ring.op_pointdollarlparenrparen
          F_t F Ufield dividend m)
        (@MonadVM.Ec.Algebra.Polynomial_ring.op_pointdollarlparenrparen
          F_t F Ufield product m))
      (@MonadVM.Ec.Algebra.Polynomial_ring.F F_t F).(MonadVM.Ec.Algebra.FIELD.zero)
      = true ->
    degree
      (@MonadVM.Ec.Algebra.Polynomial_ring.op_minus F_t F
        Uarray Uarray Ufield dividend product) < m.
  Proof.
    cbn beta zeta.
    intros Hn Hm Hcancel.
    apply generated_minus_degree_drops_if_lead_zero.
    - change (0 <= degree dividend). lia.
    - pose proof
        (generated_division_product_length_le divisor coefficient
          (degree dividend) Hn Hm) as Hproduct.
      assert (Hdividend :
        length dividend = degree dividend + 1).
      { change (length dividend = length dividend - 1 + 1).
        lia. }
      rewrite <- Hdividend in Hproduct.
      exact Hproduct.
    - exact Hcancel.
  Qed.

  Corollary generated_polynomial_product_degree_le
      (left right : list F_t) :
    0 < length left ->
    0 < length right ->
    degree
      (@MonadVM.Ec.Algebra.Polynomial_ring.op_star F_t F
        Uarray Uarray Ufield left right) <=
      degree left + degree right.
  Proof.
    intros Hleft Hright.
    pose proof
      (generated_polynomial_product_length_le left right Hleft Hright)
      as Hlength.
    unfold degree, MonadVM.Ec.Algebra.Polynomial_ring.degree.
    change
      (length
        (@MonadVM.Ec.Algebra.Polynomial_ring.op_star F_t F
          Uarray Uarray Ufield left right) - 1 <=
       (length left - 1) + (length right - 1)).
    lia.
  Qed.
End ArithmeticBounds.
