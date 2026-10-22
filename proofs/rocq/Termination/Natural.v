(** Ranking facts for loops over the [N]-backed translation of [Uint.t]. *)

From Stdlib Require Import NArith Lia Arith.Wf_nat.

Create HintDb uint_countdown.

Definition n_rank (value : N) : nat := N.to_nat value.

Lemma n_rank_strict (next current : N) :
  (next < current)%N -> (n_rank next < n_rank current)%nat.
Proof.
  unfold n_rank.
  intros Hlt.
  nia.
Qed.

Lemma positive_halving_decreases (value : N) :
  value <> 0%N -> (n_rank (N.div value 2) < n_rank value)%nat.
Proof.
  intros Hnonzero.
  apply n_rank_strict.
  apply N.div_lt; lia.
Qed.

Lemma positive_countdown_decreases (value : N) :
  value <> 0%N -> (n_rank (N.pred value) < n_rank value)%nat.
Proof.
  intros Hnonzero.
  apply n_rank_strict.
  nia.
Qed.

Definition n_increasing_index_rank (limit index : N) : nat :=
  n_rank (limit - index).

Lemma n_increasing_index_positive_step_decreases
    (limit index step : N) :
  (index < limit)%N ->
  step <> 0%N ->
  (n_increasing_index_rank limit (index + step) <
   n_increasing_index_rank limit index)%nat.
Proof.
  intros Hindex Hstep.
  unfold n_increasing_index_rank.
  apply n_rank_strict.
  nia.
Qed.

(** Normalize the [UintN] compatibility operations occurring in generated
    recursive-call arguments. *)
Ltac simplify_uintn :=
  cbn beta iota zeta in *.

Ltac derive_n_boolean_facts :=
  repeat match goal with
  | guard : N.eqb ?left ?right = false |- _ =>
      apply N.eqb_neq in guard
  | guard : N.eqb ?left ?right = true |- _ =>
      apply N.eqb_eq in guard
  | guard : N.ltb ?left ?right = true |- _ =>
      apply N.ltb_lt in guard
  | guard : N.ltb ?left ?right = false |- _ =>
      apply N.ltb_ge in guard
  end.

Ltac expose_generated_measure :=
  unfold ltof;
  match goal with
  | [ measure := _ : _ -> nat |- _ ] => unfold measure
  end;
  repeat match goal with
  | [ equation : ?scrutinee = (?lhs, ?rhs) |- _ ] =>
      let body := (eval cbv delta in scrutinee) in
      change (body = (lhs, rhs)) in equation;
      cbn beta iota zeta in equation;
      inversion equation; subst; clear equation
  end;
  repeat match goal with
  | [ local := _ |- _ ] => unfold local in *
  end;
  subst;
  cbn beta iota zeta in *.

Ltac solve_uint_halving_decrease :=
  expose_generated_measure;
  simplify_uintn;
  derive_n_boolean_facts;
  apply positive_halving_decreases;
  intro Hzero;
  subst;
  cbv delta in *;
  discriminate.

Ltac solve_uint_countdown_decrease :=
  expose_generated_measure;
  eauto with uint_countdown.

Ltac solve_uint_increasing_index_decrease :=
  expose_generated_measure;
  simplify_uintn;
  derive_n_boolean_facts;
  apply n_increasing_index_positive_step_decreases;
  [ match goal with
    | guard : ?test = true |- (?index < ?limit)%N =>
        apply N.ltb_lt;
        change (N.ltb index limit = true) in guard;
        exact guard
    end
  | let Hzero := fresh "Hzero" in
    intro Hzero;
    cbv delta in Hzero;
    discriminate ].
