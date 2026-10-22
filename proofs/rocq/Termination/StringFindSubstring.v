(** Ranking certificate for [String.find_substring.matches_at]. *)

From Stdlib Require Import ZArith Lia.
From RocqOfOCaml.Termination Require Import Common.
Require Import RocqOfOCaml.OCamlString.

Local Open Scope Z_scope.

Lemma ocaml_string_length_nonnegative (value : Strings.String.string) :
  0 <= RocqOfOCaml.OCamlString.length value.
Proof. unfold RocqOfOCaml.OCamlString.length; lia. Qed.

(** There are [substring_length + 1] ranks for each candidate start
    position.  Advancing [j] consumes one rank; rejecting a start position
    and advancing [i] consumes all remaining ranks for that position. *)
Definition matches_at_rank
    (string_length substring_length i j : Z) : nat :=
  z_rank
    (Z.max 0 (string_length - i) * (substring_length + 1) +
     (substring_length - j)).

Lemma matches_at_matching_character_decreases
    (string_length substring_length i j : Z) :
  0 <= substring_length ->
  j < substring_length ->
  i + j < string_length ->
  (matches_at_rank string_length substring_length i (j + 1) <
   matches_at_rank string_length substring_length i j)%nat.
Proof.
  intros Hsubstring Hj_bound Hposition.
  unfold matches_at_rank.
  apply z_rank_strict.
  - assert (0 <= Z.max 0 (string_length - i)) by apply Z.le_max_l.
    nia.
  - nia.
Qed.

Lemma matches_at_next_position_decreases
    (string_length substring_length i j : Z) :
  0 <= substring_length ->
  j < substring_length ->
  i + j < string_length ->
  (matches_at_rank string_length substring_length (i + 1) 0 <
   matches_at_rank string_length substring_length i j)%nat.
Proof.
  intros Hsubstring Hj_bound Hposition.
  unfold matches_at_rank.
  apply z_rank_strict.
  - assert (0 <= Z.max 0 (string_length - (i + 1))) by apply Z.le_max_l.
    nia.
  - destruct (Z_lt_ge_dec i string_length) as [Hi | Hi].
    + rewrite (Z.max_r 0 (string_length - i)) by lia.
      rewrite (Z.max_r 0 (string_length - (i + 1))) by lia.
      nia.
    + rewrite (Z.max_l 0 (string_length - i)) by lia.
      rewrite (Z.max_l 0 (string_length - (i + 1))) by lia.
      nia.
Qed.

Ltac derive_false_integer_ge_facts :=
  repeat match goal with
  | guard : Z.geb ?left ?right = false |- _ =>
      let fact := fresh "Hlt" in
      assert (fact : left < right) by
        (destruct (Z.geb_spec left right); congruence);
      clear guard
  end.

(** This tactic is named in the translation profile.  It is run at each of
    the two recursive call sites after the translator has exposed the local
    [Fix] relation and branch equations. *)
Ltac solve_matches_at_decrease :=
  subst;
  unfold ltof;
  cbn;
  match goal with
  | [ measure := _ : _ -> nat |- _ ] => unfold measure; cbn
  end;
  derive_false_integer_ge_facts;
  first
    [ eapply matches_at_matching_character_decreases
    | eapply matches_at_next_position_decreases ];
  try assumption;
  apply ocaml_string_length_nonnegative.
