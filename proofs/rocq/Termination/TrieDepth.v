(** Prefix-trie insertion and lookup advance through a finite key. *)

From Stdlib Require Import String Ascii ZArith Lia Arith.Wf_nat.
Require Import RocqOfOCaml.OCamlString.
From RocqOfOCaml.Termination Require Import IncreasingIndex.

Local Open Scope Z_scope.

Definition depth_value (depth : option Z) : Z :=
  match depth with Some value => value | None => 0 end.

Definition key_depth_rank (key : string) (depth : option Z) : nat :=
  increasing_index_rank (OCamlString.length key) (depth_value depth).

Lemma key_depth_decreases (key : string) (depth : Z) :
  depth < OCamlString.length key ->
  (key_depth_rank key (Some (depth + 1)%Z) <
   key_depth_rank key (Some depth))%nat.
Proof.
  intros Hdepth.
  unfold key_depth_rank, depth_value.
  apply increasing_index_positive_step_decreases; lia.
Qed.

Ltac solve_key_depth_decrease :=
  repeat match goal with
  | local := _ : option _ |- _ => subst local
  end;
  subst;
  unfold ltof;
  match goal with
  | [ measure := _ : _ -> nat |- _ ] => unfold measure
  end;
  cbn beta iota zeta;
  unfold key_depth_rank, depth_value;
  apply increasing_index_positive_step_decreases;
  [ apply Z.ltb_lt; assumption | lia ].

(** The native key access raises before either guard can fail. An arbitrary
    translated fallback can nevertheless supply a branch index after the key
    is exhausted. Without a guard the index then advances away from its bound. *)
Example exhausted_key_access_can_supply_a_nibble :
  @OCamlString.get
    {| RocqOfOCaml.Basics.unreachable := ascii_of_nat 0 |}
    EmptyString 1 = ascii_of_nat 0.
Proof. reflexivity. Qed.

Example advancing_past_end_does_not_decrease :
  ~ (key_depth_rank EmptyString (Some 2%Z) <
     key_depth_rank EmptyString (Some 1%Z))%nat.
Proof. compute; lia. Qed.
