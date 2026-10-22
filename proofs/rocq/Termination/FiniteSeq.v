(** Ranking certificate for consumers of the finite project model of
    [Stdlib.Seq].  This theorem intentionally does not apply to arbitrary
    potentially infinite OCaml sequences. *)

From Stdlib Require Import Lia Arith.Wf_nat.
Require Import RocqOfOCaml.OCamlSeq.

Definition finite_seq_rank {A : Set} (values : OCamlSeq.t A) : nat :=
  OCamlSeq.length_nat values.

Lemma uncons_tail_decreases {A : Set}
    (values : OCamlSeq.t A) (head : A) (tail : OCamlSeq.t A) :
  OCamlSeq.uncons values = Some (head, tail) ->
  (finite_seq_rank tail < finite_seq_rank values)%nat.
Proof.
  destruct values; cbn; intros Hview.
  - discriminate.
  - inversion Hview; subst. unfold finite_seq_rank. cbn. lia.
Qed.

Ltac solve_finite_seq_decrease :=
  unfold ltof;
  match goal with
  | [ measure := _ : _ -> nat |- _ ] => unfold measure
  end;
  repeat match goal with
  | [ local := _ |- _ ] => unfold local in *
  end;
  subst;
  cbn beta iota zeta in *;
  eapply uncons_tail_decreases;
  eassumption.
