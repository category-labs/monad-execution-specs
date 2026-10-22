(** Ranking facts and call-site tactics for simple loops over translated
    OCaml [int] values. *)

From Stdlib Require Import ZArith Lia Arith.Wf_nat Strings.Ascii.
From RocqOfOCaml.Termination Require Import Common IncreasingIndex.
Require Import RocqOfOCaml.OCamlChar.

Local Open Scope Z_scope.

Definition countdown_rank (value : Z) : nat := z_rank (value + 1).

Lemma countdown_decreases (value : Z) :
  0 <= value ->
  (countdown_rank (value - 1) < countdown_rank value)%nat.
Proof.
  intros Hvalue.
  unfold countdown_rank.
  apply z_rank_strict; lia.
Qed.

Ltac derive_z_boolean_facts :=
  repeat match goal with
  | guard : andb ?left ?right = true |- _ =>
      apply Bool.andb_true_iff in guard; destruct guard
  | guard : orb ?left ?right = false |- _ =>
      apply Bool.orb_false_iff in guard; destruct guard
  | guard : Z.geb ?left ?right = true |- _ =>
      apply Z.geb_le in guard
  | guard : Z.geb ?left ?right = false |- _ =>
      let fact := fresh "Hlt" in
      assert (fact : left < right) by
        (destruct (Z.geb_spec left right); congruence);
      clear guard
  | guard : Z.gtb ?left ?right = true |- _ =>
      apply Z.gtb_lt in guard
  | guard : Z.gtb ?left ?right = false |- _ =>
      let fact := fresh "Hle" in
      assert (fact : left <= right) by
        (destruct (Z.gtb_spec left right); congruence);
      clear guard
  | guard : Z.ltb ?left ?right = true |- _ =>
      apply Z.ltb_lt in guard
  | guard : Z.ltb ?left ?right = false |- _ =>
      apply Z.ltb_ge in guard
  end.

Ltac expose_generated_measure :=
  subst;
  unfold ltof;
  match goal with
  | [ measure := _ : _ -> nat |- _ ] => unfold measure; cbn beta zeta
  end.

Ltac solve_countdown_decrease :=
  expose_generated_measure;
  derive_z_boolean_facts;
  apply countdown_decreases;
  lia.

Ltac solve_increasing_index_decrease :=
  expose_generated_measure;
  derive_z_boolean_facts;
  repeat match goal with
  | local := _ : ascii |- _ => subst local
  | local := Z.add (Z.sub _ _) _ |- _ => subst local
  end;
  unfold RocqOfOCaml.OCamlChar.code in *;
  cbn in *;
  unfold increasing_index_rank;
  apply z_rank_strict_from_positive;
  lia.
