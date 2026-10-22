(** Ranking certificate for the unsigned repetition count used by
    [Precompiles.Utils.Precompile.list.loop]. *)

From Stdlib Require Import NArith Lia.
Require Import MonadExecutionSpecs.Termination.Natural.
Require Import MonadVM.Support.UintN.

Definition precompile_list_rank (remaining : N) : nat := n_rank remaining.

Lemma precompile_list_step_decreases
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable
      MonadVM.Support.UintN.t}
    (remaining : N) :
  MonadVM.Support.UintN.is_zero remaining = false ->
  (precompile_list_rank
     (MonadVM.Support.UintN.op_minus
       remaining MonadVM.Support.UintN.one) <
   precompile_list_rank remaining)%nat.
Proof.
  intros Hnonzero.
  unfold MonadVM.Support.UintN.is_zero in Hnonzero.
  destruct remaining as [|positive].
  - discriminate.
  - unfold MonadVM.Support.UintN.op_minus,
      MonadVM.Support.UintN.one.
    assert (Hone : N.leb 1 (N.pos positive) = true).
    { apply N.leb_le. lia. }
    rewrite Hone.
    unfold precompile_list_rank.
    apply n_rank_strict.
    nia.
Qed.

#[export] Hint Resolve precompile_list_step_decreases : uint_countdown.
