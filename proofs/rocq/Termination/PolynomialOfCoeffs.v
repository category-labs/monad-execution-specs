(** The generated [of_coeffs] loop trims trailing field-zero coefficients.
    Its well-founded [Fix] uses a dependent Boolean guard, so the branch
    congruence below exposes the recursive equation without new axioms. *)

From Stdlib Require Import ZArith Bool Lia List.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import MonadVM.Ec.Algebra.
Require Import MonadExecutionSpecs.Termination.PolynomialDegree.

Local Open Scope Z_scope.

Local Lemma guarded_branch_ext (guard : bool)
    (left right : guard = true -> Z)
    (fallback : guard = false -> Z) :
  (forall proof, left proof = right proof) ->
  (match guard as result return guard = result -> Z with
   | true => left
   | false => fallback
   end eq_refl) =
  (match guard as result return guard = result -> Z with
   | true => right
   | false => fallback
   end eq_refl).
Proof.
  destruct guard; intro Hpointwise; simpl.
  - apply Hpointwise.
  - reflexivity.
Qed.

Local Lemma guarded_branch_true (guard : bool) (yes no : Z) :
  guard = true ->
  (match guard as result return guard = result -> Z with
   | true => fun _ => yes
   | false => fun _ => no
   end eq_refl) = yes.
Proof.
  destruct guard; simpl; congruence.
Qed.

Local Lemma guarded_branch_false (guard : bool) (yes no : Z) :
  guard = false ->
  (match guard as result return guard = result -> Z with
   | true => fun _ => yes
   | false => fun _ => no
   end eq_refl) = no.
Proof.
  destruct guard; simpl; congruence.
Qed.

Local Lemma generated_int_equality_sound (left right : Z) :
  equiv_decb left right = true -> left = right.
Proof.
  intro Hbool.
  change ((if Z.eq_dec left right then true else false) = true) in Hbool.
  destruct (Z.eq_dec left right) as [Heq | Hne].
  - change (left = right) in Heq. exact Heq.
  - discriminate.
Qed.

Local Lemma generated_init_nat_length {A : Set} (count : nat)
    (start : Z) (element : Z -> A) :
  Datatypes.length (RocqOfOCaml.OCamlIarray.init_nat count start element) = count.
Proof.
  revert start.
  induction count; intro start; simpl; [reflexivity |].
  rewrite IHcount. reflexivity.
Qed.

Local Lemma generated_init_nat_nth {A : Set} (count index : nat)
    (start : Z) (element : Z -> A) :
  (index < count)%nat ->
  List.nth_error
    (RocqOfOCaml.OCamlIarray.init_nat count start element)
    index = Some (element (start + Z.of_nat index)).
Proof.
  revert index start.
  induction count as [|count IH]; intros index start Hindex;
    [lia |].
  destruct index as [|index]; simpl.
  - rewrite Z.add_0_r. reflexivity.
  - rewrite IH by lia.
    replace (Z.pos (Pos.of_succ_nat index))
      with (Z.of_nat (S index)) by reflexivity.
    rewrite Nat2Z.inj_succ.
    replace (start + 1 + Z.of_nat index)
      with (start + (Z.of_nat index + 1)) by lia.
    reflexivity.
Qed.

Local Lemma generated_init_last {A : Set}
    `{RocqOfOCaml.Basics.Unreachable (list A)}
    `{RocqOfOCaml.Basics.Unreachable A}
    (degree : Z) (element : Z -> A) :
  0 <= degree ->
  RocqOfOCaml.OCamlIarray.get
    (RocqOfOCaml.OCamlIarray.init (degree + 1) element) degree =
    element degree.
Proof.
  intro Hdegree.
  unfold RocqOfOCaml.OCamlIarray.get,
    RocqOfOCaml.OCamlIarray.init.
  assert (Hcount : (degree + 1 <? 0) = false)
    by (apply Z.ltb_ge; lia).
  assert (Hindex : (degree <? 0) = false)
    by (apply Z.ltb_ge; lia).
  rewrite Hcount, Hindex.
  rewrite generated_init_nat_nth by lia.
  f_equal. rewrite Z2Nat.id by lia. lia.
Qed.

Lemma generated_init_length {A : Set}
    `{RocqOfOCaml.Basics.Unreachable (list A)}
    (degree : Z) (element : Z -> A) :
  0 <= degree ->
  RocqOfOCaml.OCamlIarray.length
    (RocqOfOCaml.OCamlIarray.init (degree + 1) element) =
    degree + 1.
Proof.
  intro Hdegree.
  unfold RocqOfOCaml.OCamlIarray.length,
    RocqOfOCaml.OCamlIarray.init.
  assert (Hcount : (degree + 1 <? 0) = false)
    by (apply Z.ltb_ge; lia).
  rewrite Hcount, generated_init_nat_length.
  rewrite Z2Nat.id by lia. reflexivity.
Qed.

Section OfCoeffs.
  Context {F_t : Set}
    {F : @MonadVM.Ec.Algebra.Polynomial_ring.FArgs F_t}.
  Context `{Uarray :
    RocqOfOCaml.Basics.Unreachable (RocqOfOCaml.OCamlIarray.t F_t)}.
  Context `{Ufield : RocqOfOCaml.Basics.Unreachable F_t}.
  Let field := @MonadVM.Ec.Algebra.Polynomial_ring.F F_t F.
  Let field_zero := field.(MonadVM.Ec.Algebra.FIELD.zero).
  Let field_equal := field.(MonadVM.Ec.Algebra.FIELD.op_eq).
  Let guard (coeffs : list F_t) (i : Z) :=
    andb (Z.geb i 0)
      (field_equal (RocqOfOCaml.OCamlIarray.get coeffs i) field_zero).

  Theorem generated_of_coeffs_facts (coeffs : list F_t) :
    let output :=
      @MonadVM.Ec.Algebra.Polynomial_ring.of_coeffs F_t F Ufield Uarray
        coeffs in
    (output = nil \/
       field_equal
         (RocqOfOCaml.OCamlIarray.get output
           (Z.of_nat (Datatypes.length output) - 1))
         field_zero = false) /\
    RocqOfOCaml.OCamlIarray.length output <=
      RocqOfOCaml.OCamlIarray.length coeffs /\
    (0 < RocqOfOCaml.OCamlIarray.length coeffs ->
      field_equal
        (RocqOfOCaml.OCamlIarray.get coeffs
          (RocqOfOCaml.OCamlIarray.length coeffs - 1))
        field_zero = true ->
      RocqOfOCaml.OCamlIarray.length output <
        RocqOfOCaml.OCamlIarray.length coeffs).
  Proof.
    cbn beta.
    unfold MonadVM.Ec.Algebra.Polynomial_ring.of_coeffs at 1.
    cbn -[Fix Fix_F].
    unfold MonadVM.Ec.Algebra.Polynomial_ring.Impl.of_coeffs at 1.
    lazymatch goal with
    | |- context [@Fix ?A ?R ?wf ?P ?body] =>
        assert (Hext : forall x f g,
          (forall y p, f y p = g y p) -> body x f = body x g)
    end.
    { intros x f g Hfg.
      cbn beta.
      eapply guarded_branch_ext.
      intro Hguard.
      apply Hfg. }
    lazymatch goal with
    | |- context [@Fix ?A ?R ?wf ?P ?body] =>
        pose proof (@Fix_eq A R wf P body Hext) as Hfixeq;
        set (loop := @Fix A R wf P body)
    end.
    assert (Hloop_step : forall i : Z,
      guard coeffs i = true -> loop i = loop (i - 1)).
    { intros i Hguard.
      unfold loop at 1.
      rewrite (Hfixeq i).
      cbn beta.
      apply guarded_branch_true.
      exact Hguard. }
    assert (Hloop_stop : forall i : Z,
      guard coeffs i = false -> loop i = i).
    { intros i Hguard.
      unfold loop at 1.
      rewrite (Hfixeq i).
      cbn beta.
      apply guarded_branch_false.
      exact Hguard. }
    assert (Hloop_sound : forall i : Z,
      -1 <= i ->
      let degree := loop i in
      -1 <= degree <= i /\
      (0 <= degree ->
        field_equal (RocqOfOCaml.OCamlIarray.get coeffs degree)
          field_zero = false)).
    { apply (@well_founded_ind Z
        (ltof Z MonadExecutionSpecs.Termination.IntegerLoops.countdown_rank)
        (well_founded_ltof Z
          MonadExecutionSpecs.Termination.IntegerLoops.countdown_rank)
        (fun i =>
          -1 <= i ->
          let degree := loop i in
          -1 <= degree <= i /\
          (0 <= degree ->
            field_equal (RocqOfOCaml.OCamlIarray.get coeffs degree)
              field_zero = false))).
      intros i IH Hlower.
      destruct (guard coeffs i) eqn:Hguard.
      - rewrite Hloop_step by exact Hguard.
        assert (Hi : 0 <= i).
        { unfold guard in Hguard.
          apply Bool.andb_true_iff in Hguard.
          apply Z.geb_le. exact (proj1 Hguard). }
        assert (Hdecrease :
          ltof Z MonadExecutionSpecs.Termination.IntegerLoops.countdown_rank
            (i - 1) i).
        { unfold ltof.
          apply MonadExecutionSpecs.Termination.IntegerLoops.countdown_decreases.
          exact Hi. }
        pose proof (IH (i - 1) Hdecrease ltac:(lia)) as [Hrange Hnonzero].
        split; [lia | exact Hnonzero].
      - rewrite Hloop_stop by exact Hguard.
        split; [lia |].
        intro Hi.
        unfold guard in Hguard.
        assert (Hge : (i >=? 0) = true) by (apply Z.geb_le; lia).
        rewrite Hge in Hguard.
        exact Hguard. }
    unfold MonadVM.Ec.Algebra.Polynomial_ring.Impl.of_coeffs.
    cbn -[Fix Fix_F].
    fold loop.
    lazymatch goal with
    | |- context [if loop _ ==b _ then _ else _] =>
        set (result :=
          if equiv_decb
            (loop (RocqOfOCaml.OCamlIarray.length coeffs - 1))
            (RocqOfOCaml.OCamlIarray.length coeffs - 1)
          then coeffs
          else RocqOfOCaml.OCamlIarray.init
            (loop (RocqOfOCaml.OCamlIarray.length coeffs - 1) + 1)
            (fun i => RocqOfOCaml.OCamlIarray.get coeffs i))
    end.
    change
      ((result = nil \/
        field_equal
          (RocqOfOCaml.OCamlIarray.get result
            (Z.of_nat (Datatypes.length result) - 1))
          field_zero = false) /\
       RocqOfOCaml.OCamlIarray.length result <=
         RocqOfOCaml.OCamlIarray.length coeffs /\
       (0 < RocqOfOCaml.OCamlIarray.length coeffs ->
         field_equal
           (RocqOfOCaml.OCamlIarray.get coeffs
             (RocqOfOCaml.OCamlIarray.length coeffs - 1))
           field_zero = true ->
         RocqOfOCaml.OCamlIarray.length result <
           RocqOfOCaml.OCamlIarray.length coeffs)).
    set (n := RocqOfOCaml.OCamlIarray.length coeffs).
    set (degree := loop (n - 1)).
    assert (Hstart : -1 <= n - 1).
    { unfold n, RocqOfOCaml.OCamlIarray.length. lia. }
    pose proof (Hloop_sound (n - 1) Hstart) as [Hrange Hnonzero].
    fold degree in Hrange, Hnonzero.
    change
      (let output :=
        if equiv_decb degree (n - 1) then coeffs
        else RocqOfOCaml.OCamlIarray.init (degree + 1)
          (fun i => RocqOfOCaml.OCamlIarray.get coeffs i) in
       (output = nil \/
        field_equal
          (RocqOfOCaml.OCamlIarray.get output
            (Z.of_nat (Datatypes.length output) - 1))
          field_zero = false) /\
       RocqOfOCaml.OCamlIarray.length output <= n /\
       (0 < n ->
         field_equal (RocqOfOCaml.OCamlIarray.get coeffs (n - 1))
           field_zero = true ->
         RocqOfOCaml.OCamlIarray.length output < n)).
    destruct (equiv_decb degree (n - 1)) eqn:Hequal; cbn beta.
    - apply generated_int_equality_sound in Hequal.
      destruct coeffs as [|head tail].
      + split.
        * left. reflexivity.
        * split.
          -- unfold n, RocqOfOCaml.OCamlIarray.length. simpl. lia.
          -- intros Hpositive Hlastzero.
             unfold n, RocqOfOCaml.OCamlIarray.length in Hpositive.
             simpl in Hpositive. lia.
      +
        assert (Hdegree : 0 <= degree).
        { unfold n, RocqOfOCaml.OCamlIarray.length in Hequal.
          cbn [Datatypes.length] in Hequal.
          rewrite Nat2Z.inj_succ in Hequal. lia. }
        pose proof (Hnonzero Hdegree) as Htop.
        rewrite Hequal in Htop.
        split.
        * right. exact Htop.
        * split.
          -- unfold n, RocqOfOCaml.OCamlIarray.length.
             reflexivity.
          -- intros Hpositive Hlastzero.
             rewrite Hlastzero in Htop. discriminate.
    - destruct (Z_le_gt_dec 0 degree) as [Hdegree | Hdegree].
      + assert (Hlength :
          RocqOfOCaml.OCamlIarray.length
            (RocqOfOCaml.OCamlIarray.init (degree + 1)
              (fun i => RocqOfOCaml.OCamlIarray.get coeffs i)) =
          degree + 1).
        { apply generated_init_length. exact Hdegree. }
        split.
        * right.
          change
            (field_equal
              (RocqOfOCaml.OCamlIarray.get
                (RocqOfOCaml.OCamlIarray.init (degree + 1)
                  (fun i => RocqOfOCaml.OCamlIarray.get coeffs i))
                (RocqOfOCaml.OCamlIarray.length
                  (RocqOfOCaml.OCamlIarray.init (degree + 1)
                    (fun i => RocqOfOCaml.OCamlIarray.get coeffs i)) - 1))
              field_zero = false).
          rewrite Hlength.
          replace (degree + 1 - 1) with degree by lia.
          rewrite (generated_init_last degree
            (fun i => RocqOfOCaml.OCamlIarray.get coeffs i))
            by exact Hdegree.
          apply Hnonzero. exact Hdegree.
        * split.
          -- rewrite Hlength. lia.
          -- intros Hpositive Hlastzero.
             rewrite Hlength.
             assert (Hguard : guard coeffs (n - 1) = true).
             { unfold guard. apply Bool.andb_true_iff. split.
               - apply Z.geb_le. lia.
               - exact Hlastzero. }
             assert (Hdrop : degree <= n - 2).
             { unfold degree.
               rewrite Hloop_step by exact Hguard.
               replace (n - 1 - 1) with (n - 2) by lia.
               pose proof (Hloop_sound (n - 2) ltac:(lia))
                 as [[_ Hnext] _].
               exact Hnext. }
             lia.
      +
        assert (Hminus : degree = -1) by lia.
        rewrite Hminus.
        cbn.
        split.
        * left. reflexivity.
        * split; [lia |].
          intros Hpositive Hlastzero. lia.
  Qed.

  (** A nonzero last coefficient makes normalization return its input
      unchanged, independently of the array and field fallback arguments. *)
  Lemma generated_of_coeffs_keeps_nonzero_last (coeffs : list F_t) :
    0 < RocqOfOCaml.OCamlIarray.length coeffs ->
    field_equal
      (RocqOfOCaml.OCamlIarray.get coeffs
        (RocqOfOCaml.OCamlIarray.length coeffs - 1)) field_zero = false ->
    @MonadVM.Ec.Algebra.Polynomial_ring.of_coeffs F_t F Ufield Uarray
      coeffs = coeffs.
  Proof.
    intros Hpositive Hlast.
    unfold MonadVM.Ec.Algebra.Polynomial_ring.of_coeffs at 1.
    cbn -[Fix Fix_F].
    unfold MonadVM.Ec.Algebra.Polynomial_ring.Impl.of_coeffs at 1.
    lazymatch goal with
    | |- context [@Fix ?A ?R ?wf ?P ?body] =>
        assert (Hext : forall x f g,
          (forall y p, f y p = g y p) -> body x f = body x g)
    end.
    { intros x f g Hfg.
      cbn beta.
      eapply guarded_branch_ext.
      intro Hguard.
      apply Hfg. }
    lazymatch goal with
    | |- context [@Fix ?A ?R ?wf ?P ?body] =>
        pose proof (@Fix_eq A R wf P body Hext) as Hfixeq;
        set (loop := @Fix A R wf P body)
    end.
    unfold MonadVM.Ec.Algebra.Polynomial_ring.Impl.of_coeffs.
    cbn -[Fix Fix_F].
    fold loop.
    set (n := RocqOfOCaml.OCamlIarray.length coeffs).
    assert (Hguard :
      andb (Z.geb (n - 1) 0)
        (field_equal (RocqOfOCaml.OCamlIarray.get coeffs (n - 1))
          field_zero) = false).
    { assert (Hge : Z.geb (n - 1) 0 = true)
        by (apply Z.geb_le; unfold n in *; lia).
      rewrite Hge. exact Hlast. }
    assert (Hloop : loop (n - 1) = n - 1).
    { unfold loop at 1.
      rewrite (Hfixeq (n - 1)).
      cbn beta.
      eapply guarded_branch_false.
      exact Hguard. }
    change
      ((if equiv_decb (loop (n - 1)) (n - 1) then coeffs
        else RocqOfOCaml.OCamlIarray.init (loop (n - 1) + 1)
          (fun i => RocqOfOCaml.OCamlIarray.get coeffs i)) = coeffs).
    rewrite Hloop.
    lazymatch goal with
    | |- (if ?condition then _ else _) = _ =>
        destruct condition eqn:Heq; [reflexivity |]
    end.
    change ((if Z.eq_dec (n - 1) (n - 1) then true else false) = false)
      in Heq.
    destruct (Z.eq_dec (n - 1) (n - 1)); congruence.
  Qed.

  Print Assumptions generated_of_coeffs_keeps_nonzero_last.

  Corollary generated_of_coeffs_trailing_nonzero (coeffs : list F_t) :
    let output :=
      @MonadVM.Ec.Algebra.Polynomial_ring.of_coeffs F_t F Ufield Uarray
        coeffs in
    output = nil \/
      field_equal
        (RocqOfOCaml.OCamlIarray.get output
          (Z.of_nat (Datatypes.length output) - 1))
        field_zero = false.
  Proof.
    exact (proj1 (generated_of_coeffs_facts coeffs)).
  Qed.

  Corollary generated_of_coeffs_length_le (coeffs : list F_t) :
    RocqOfOCaml.OCamlIarray.length
      (@MonadVM.Ec.Algebra.Polynomial_ring.of_coeffs F_t F
        Ufield Uarray coeffs) <=
      RocqOfOCaml.OCamlIarray.length coeffs.
  Proof.
    exact (proj1 (proj2 (generated_of_coeffs_facts coeffs))).
  Qed.

  Corollary generated_of_coeffs_drops_last_zero (coeffs : list F_t) :
    0 < RocqOfOCaml.OCamlIarray.length coeffs ->
    field_equal
      (RocqOfOCaml.OCamlIarray.get coeffs
        (RocqOfOCaml.OCamlIarray.length coeffs - 1))
      field_zero = true ->
    RocqOfOCaml.OCamlIarray.length
      (@MonadVM.Ec.Algebra.Polynomial_ring.of_coeffs F_t F
        Ufield Uarray coeffs) <
      RocqOfOCaml.OCamlIarray.length coeffs.
  Proof.
    intros Hpositive Hlastzero.
    exact (proj2 (proj2 (generated_of_coeffs_facts coeffs))
      Hpositive Hlastzero).
  Qed.

  Corollary generated_of_coeffs_degree_drops_last_zero
      (coeffs : list F_t) :
    0 < RocqOfOCaml.OCamlIarray.length coeffs ->
    field_equal
      (RocqOfOCaml.OCamlIarray.get coeffs
        (RocqOfOCaml.OCamlIarray.length coeffs - 1))
      field_zero = true ->
    @MonadVM.Ec.Algebra.Polynomial_ring.degree F_t F
      (@MonadVM.Ec.Algebra.Polynomial_ring.of_coeffs F_t F
        Ufield Uarray coeffs) <
      @MonadVM.Ec.Algebra.Polynomial_ring.degree F_t F coeffs.
  Proof.
    intros Hpositive Hlastzero.
    pose proof (generated_of_coeffs_drops_last_zero coeffs
      Hpositive Hlastzero) as Hlength.
    unfold MonadVM.Ec.Algebra.Polynomial_ring.degree,
      MonadVM.Ec.Algebra.Polynomial_ring.length in *.
    apply (proj1 (Z.sub_lt_mono_r _ _ 1)).
    exact Hlength.
  Qed.

  (** Subtraction can use the normalizer's strict-drop result once the
      subtrahend is no longer than the dividend and the leading coefficient
      of the raw result is zero. The translated integer [max] makes the raw
      result's length provable without changing the source. *)
  Corollary generated_minus_degree_drops_if_lead_zero
      (left right : list F_t) :
    let degree_left :=
      @MonadVM.Ec.Algebra.Polynomial_ring.degree F_t F left in
    0 <= degree_left ->
    @MonadVM.Ec.Algebra.Polynomial_ring.length F_t F right <=
      @MonadVM.Ec.Algebra.Polynomial_ring.length F_t F left ->
    field_equal
      (field.(MonadVM.Ec.Algebra.FIELD.op_minus)
        (@MonadVM.Ec.Algebra.Polynomial_ring.op_pointdollarlparenrparen
          F_t F Ufield left degree_left)
        (@MonadVM.Ec.Algebra.Polynomial_ring.op_pointdollarlparenrparen
          F_t F Ufield right degree_left)) field_zero = true ->
    @MonadVM.Ec.Algebra.Polynomial_ring.degree F_t F
      (@MonadVM.Ec.Algebra.Polynomial_ring.op_minus F_t F
        Uarray Uarray Ufield left right) < degree_left.
  Proof.
    cbn beta zeta.
    intros Hdegree Hrightlength Hlastzero.
    assert (Hmax :
      Z.max
        (@MonadVM.Ec.Algebra.Polynomial_ring.length F_t F left)
        (@MonadVM.Ec.Algebra.Polynomial_ring.length F_t F right) =
      @MonadVM.Ec.Algebra.Polynomial_ring.length F_t F left).
    { apply Z.max_l. exact Hrightlength. }
    unfold MonadVM.Ec.Algebra.Polynomial_ring.op_minus,
      MonadVM.Ec.Algebra.Polynomial_ring.init.
    set (raw :=
      RocqOfOCaml.OCamlIarray.init
        (Z.max
          (@MonadVM.Ec.Algebra.Polynomial_ring.length F_t F left)
          (@MonadVM.Ec.Algebra.Polynomial_ring.length F_t F right))
        (fun i =>
          field.(MonadVM.Ec.Algebra.FIELD.op_minus)
            (@MonadVM.Ec.Algebra.Polynomial_ring.op_pointdollarlparenrparen
              F_t F Ufield left i)
            (@MonadVM.Ec.Algebra.Polynomial_ring.op_pointdollarlparenrparen
              F_t F Ufield right i))).
    assert (Hrawlength :
      RocqOfOCaml.OCamlIarray.length raw =
        @MonadVM.Ec.Algebra.Polynomial_ring.length F_t F left).
    { unfold raw. rewrite Hmax.
      replace (@MonadVM.Ec.Algebra.Polynomial_ring.length F_t F left)
        with ((@MonadVM.Ec.Algebra.Polynomial_ring.degree F_t F left) + 1)
        by (unfold MonadVM.Ec.Algebra.Polynomial_ring.degree; lia).
      apply generated_init_length. exact Hdegree. }
    assert (Hrawlast :
      field_equal
        (RocqOfOCaml.OCamlIarray.get raw
          (@MonadVM.Ec.Algebra.Polynomial_ring.degree F_t F left))
        field_zero = true).
    { unfold raw. rewrite Hmax.
      replace (@MonadVM.Ec.Algebra.Polynomial_ring.length F_t F left)
        with ((@MonadVM.Ec.Algebra.Polynomial_ring.degree F_t F left) + 1)
        by (unfold MonadVM.Ec.Algebra.Polynomial_ring.degree; lia).
      rewrite generated_init_last by exact Hdegree.
      exact Hlastzero. }
    change
      (@MonadVM.Ec.Algebra.Polynomial_ring.degree F_t F
        (@MonadVM.Ec.Algebra.Polynomial_ring.of_coeffs F_t F
          Ufield Uarray raw) <
       @MonadVM.Ec.Algebra.Polynomial_ring.degree F_t F left).
    replace (@MonadVM.Ec.Algebra.Polynomial_ring.degree F_t F left)
      with (@MonadVM.Ec.Algebra.Polynomial_ring.degree F_t F raw).
    2: { unfold MonadVM.Ec.Algebra.Polynomial_ring.degree.
         change
           (@MonadVM.Ec.Algebra.Polynomial_ring.length F_t F raw =
            @MonadVM.Ec.Algebra.Polynomial_ring.length F_t F left)
           in Hrawlength.
         lia. }
    apply generated_of_coeffs_degree_drops_last_zero.
    - rewrite Hrawlength.
      change (0 < RocqOfOCaml.OCamlIarray.length left).
      unfold MonadVM.Ec.Algebra.Polynomial_ring.degree,
        MonadVM.Ec.Algebra.Polynomial_ring.length in Hdegree.
      assert (Hpositive_int : forall x : Z, 0 <= x - 1 -> 0 < x)
        by lia.
      exact (Hpositive_int _ Hdegree).
    - rewrite Hrawlength.
      unfold MonadVM.Ec.Algebra.Polynomial_ring.degree in Hrawlast.
      exact Hrawlast.
  Qed.

  Corollary generated_of_coeffs_canonical_all (coeffs : list F_t) :
    @MonadExecutionSpecs.Termination.PolynomialDegree.canonical_polynomial
      F_t F Ufield
      (@MonadVM.Ec.Algebra.Polynomial_ring.of_coeffs F_t F Ufield Uarray
        coeffs).
  Proof.
    pose proof (generated_of_coeffs_trailing_nonzero coeffs) as Htrimmed.
    set (output :=
      @MonadVM.Ec.Algebra.Polynomial_ring.of_coeffs F_t F Ufield Uarray
        coeffs) in *.
    destruct output as [|head tail].
    - unfold MonadExecutionSpecs.Termination.PolynomialDegree.canonical_polynomial.
      left. reflexivity.
    - destruct Htrimmed as [Hempty | Hlast];
        [discriminate |].
      unfold MonadExecutionSpecs.Termination.PolynomialDegree.canonical_polynomial.
      right.
      change
        (field_equal
          (if Z.ltb (Z.of_nat (S (Datatypes.length tail)) - 1)
              (Z.of_nat (S (Datatypes.length tail)))
           then RocqOfOCaml.OCamlIarray.get (head :: tail)
             (Z.of_nat (S (Datatypes.length tail)) - 1)
           else field_zero)
          field_zero = false).
      assert (Hwithin :
        Z.ltb (Z.of_nat (S (Datatypes.length tail)) - 1)
          (Z.of_nat (S (Datatypes.length tail))) = true).
      { apply Z.ltb_lt. lia. }
      rewrite Hwithin. exact Hlast.
  Qed.
End OfCoeffs.
