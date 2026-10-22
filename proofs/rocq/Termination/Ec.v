(** Ranking certificates for arithmetic loops in [Ec.Algebra], [Ec.Curve],
    and [Ec.Pairing]. *)

From Stdlib Require Import ZArith Lia Bool.
From RocqOfOCaml.Termination Require Import Common.
From RocqOfOCaml.Termination Require Import IncreasingIndex.
Require Import MonadExecutionSpecs.Termination.Natural.
Require Import MonadExecutionSpecs.Termination.IntegerLoops.

Local Open Scope Z_scope.

Definition automorphism_rank (degree index : Z) : nat :=
  increasing_index_rank (degree + 1) index.

Lemma automorphism_step_decreases (degree index : Z) :
  index <= degree ->
  (automorphism_rank degree (index + 1) <
   automorphism_rank degree index)%nat.
Proof.
  intros Hindex.
  unfold automorphism_rank.
  apply increasing_index_positive_step_decreases; lia.
Qed.

Ltac solve_automorphism_decrease :=
  expose_generated_measure;
  derive_z_boolean_facts;
  apply automorphism_step_decreases;
  lia.

(** A nonzero divisor or dividend has a nonnegative degree in the intended
    Euclidean domains. The source guards establish exactly the two facts
    required to decrease this rank, even before their algebraic redundancy is
    proved for concrete instances. *)
Definition degree_rank (degree : Z) : nat := z_rank (degree + 1).

Lemma guarded_degree_step_decreases (current next : Z) :
  0 <= current ->
  next < current ->
  (degree_rank next < degree_rank current)%nat.
Proof.
  intros Hcurrent Hnext.
  unfold degree_rank.
  apply z_rank_strict_from_positive; lia.
Qed.

Ltac solve_guarded_degree_decrease :=
  expose_generated_measure;
  derive_z_boolean_facts;
  apply guarded_degree_step_decreases;
  lia.

(** The generic OCaml Euclidean-domain signature has no laws. These are the
    exact semantic premises needed to show that its new recursive guard is
    never taken on the failure branch. Concrete domain instances still have
    to establish this record. *)
Section EuclideanGuard.
  Context {A : Set}.
  Context (op_eq : A -> A -> bool) (zero : A)
    (degree : A -> Z) (div_rem : A -> A -> A * A).

  Record euclidean_degree_laws : Prop := {
    euclidean_zero_degree : degree zero = -1;
    euclidean_eq_zero_sound : forall x, op_eq x zero = true -> x = zero;
    euclidean_nonzero_degree :
      forall x, op_eq x zero = false -> 0 <= degree x;
    euclidean_remainder_progress :
      forall x y quotient remainder,
        op_eq y zero = false ->
        div_rem x y = (quotient, remainder) ->
        op_eq remainder zero = true \/ degree remainder < degree y
  }.

  Lemma euclidean_progress_guard_true
      (laws : euclidean_degree_laws)
      (x y quotient remainder : A) :
    op_eq y zero = false ->
    div_rem x y = (quotient, remainder) ->
    (Z.geb (degree y) 0 && Z.ltb (degree remainder) (degree y)) = true.
  Proof.
    intros Hnonzero Hdivision.
    destruct laws as [Hzero Heq Hdegree Hremainder].
    apply Bool.andb_true_iff; split.
    - apply Z.geb_le. apply Hdegree. exact Hnonzero.
    - apply Z.ltb_lt.
      destruct (Hremainder x y quotient remainder Hnonzero Hdivision)
        as [Hrem_zero | Hless]; auto.
      rewrite (Heq remainder Hrem_zero), Hzero.
      pose proof (Hdegree y Hnonzero) as Hy.
      lia.
  Qed.
End EuclideanGuard.
