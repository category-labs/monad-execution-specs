From Stdlib Require Import NArith.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import MonadVM.Gas.
Require Import MonadVM.Chain.Monad.
Require Import MonadVM.Support.Variants.

(** These are exact formulas in the generated N-backed unsigned model.
    The generated [Revision.active] is an alias of the full revision type,
    so the [is_active] premise below is necessary: other constructors can
    reach [memory_cost]'s typed exceptional branch. *)
Lemma generated_memory_cost_eight_formula
    (UG : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t)
    (UF : RocqOfOCaml.Basics.Unreachable (MonadVM.Gas.t -> MonadVM.Gas.t))
    (words : MonadVM.Gas.t) :
  @MonadVM.Gas.memory_cost UG UF MonadVM.Support.Variants.Revision.Eight words =
    (N.div (N.pow words 2) 512 + 3 * words)%N.
Proof. reflexivity. Qed.

Lemma generated_memory_cost_nine_formula
    (UG : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t)
    (UF : RocqOfOCaml.Basics.Unreachable (MonadVM.Gas.t -> MonadVM.Gas.t))
    (words : MonadVM.Gas.t) :
  @MonadVM.Gas.memory_cost UG UF MonadVM.Support.Variants.Revision.Nine words =
    N.div words 2.
Proof. reflexivity. Qed.

Lemma generated_active_memory_cost_independent
    (UG1 UG2 : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t)
    (UF1 UF2 : RocqOfOCaml.Basics.Unreachable (MonadVM.Gas.t -> MonadVM.Gas.t))
    (revision : MonadVM.Chain.Monad.Revision.t)
    (words : MonadVM.Gas.t) :
  MonadVM.Chain.Monad.Revision.is_active revision = Some revision ->
  @MonadVM.Gas.memory_cost UG1 UF1 revision words =
  @MonadVM.Gas.memory_cost UG2 UF2 revision words.
Proof.
  destruct revision; cbn; try discriminate; reflexivity.
Qed.

(** [is_active] is the source boundary that produces an [active] value.
    This statement applies to that returned value rather than requiring
    the caller to establish the equality [Some revision] separately. *)
Lemma generated_checked_revision_memory_cost_independent
    (UG1 UG2 : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t)
    (UF1 UF2 : RocqOfOCaml.Basics.Unreachable (MonadVM.Gas.t -> MonadVM.Gas.t))
    (revision : MonadVM.Chain.Monad.Revision.t)
    (active : MonadVM.Chain.Monad.Revision.active)
    (words : MonadVM.Gas.t) :
  MonadVM.Chain.Monad.Revision.is_active revision = Some active ->
  @MonadVM.Gas.memory_cost UG1 UF1 active words =
  @MonadVM.Gas.memory_cost UG2 UF2 active words.
Proof.
  intros Hactive.
  destruct revision; cbn in Hactive; try discriminate;
    inversion Hactive; subst; reflexivity.
Qed.

Print Assumptions generated_memory_cost_eight_formula.
Print Assumptions generated_memory_cost_nine_formula.
Print Assumptions generated_active_memory_cost_independent.
Print Assumptions generated_checked_revision_memory_cost_independent.
