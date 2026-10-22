(** Structural bounds for the finite inductive Patricia-trie model.
    Native cyclic OCaml values require a separate representation relation. *)

From Stdlib Require Import List ZArith Lia Arith.Wf_nat.
Require Import RocqOfOCaml.OCamlIarray.
Require Import RocqOfOCaml.Unreachable.ArrayBounds.

Import ListNotations.
Local Open Scope Z_scope.

Ltac solve_patricia_decrease :=
  repeat match goal with
  | local := _ : _ * _ |- _ => subst local
  end;
  repeat match goal with
  | equation : (_, _) = (_, _) |- _ =>
      injection equation; clear equation; intros
  end;
  subst;
  unfold ltof;
  match goal with
  | [ measure := _ : _ -> nat |- _ ] => unfold measure
  end;
  cbn beta iota zeta;
  first
    [ apply Nat.lt_succ_diag_r
    | apply iarray_get_weight_lt;
      repeat match goal with
      | guard : andb _ _ = true |- _ =>
          apply Bool.andb_true_iff in guard; destruct guard
      end;
      [ apply Z.leb_le; assumption | apply Z.ltb_lt; assumption ] ].
