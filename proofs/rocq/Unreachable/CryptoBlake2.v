(** Bounds lemmas for the list-backed mutable-array model used by
    [MonadVM.Support.CryptoBlake2]. *)

From Stdlib Require Import ZArith Lia List.
Require Import RocqOfOCaml.Basics.
Require Import MonadVM.Support.CryptoBlake2.

Local Open Scope Z_scope.

Lemma set_nat_succeeds {A : Set} (values : list A)
    (index : nat) (value : A) :
  (index < Datatypes.length values)%nat ->
  exists updated,
    CryptoBlake2.set_nat values index value = Some updated /\
    Datatypes.length updated = Datatypes.length values.
Proof.
  revert index.
  induction values as [|head values IH]; intros [|index] Hindex; simpl in *.
  - lia.
  - lia.
  - eexists; split; reflexivity.
  - destruct (IH index) as [updated [Hupdated Hlength]]; [lia |].
    rewrite Hupdated.
    exists (head :: updated).
    simpl; now rewrite Hlength.
Qed.

Lemma set_in_bounds_does_not_use_fallback {A : Set}
    (fallback : Unreachable (list A)) (values : list A)
    (index : Z) (value : A) :
  0 <= index ->
  (Z.to_nat index < Datatypes.length values)%nat ->
  exists updated,
    CryptoBlake2.set_nat values (Z.to_nat index) value = Some updated /\
    @CryptoBlake2.set A fallback values index value = updated.
Proof.
  intros Hnonnegative Hbound.
  destruct (set_nat_succeeds values (Z.to_nat index) value Hbound)
    as [updated [Hset Hlength]].
  exists updated; split; [exact Hset |].
  unfold CryptoBlake2.set.
  destruct (index <? 0) eqn:Hnegative.
  - apply Z.ltb_lt in Hnegative; lia.
  - now rewrite Hset.
Qed.
