(** The VM dispatch loop recurses only after the explicit gas-progress guard.
    This certificate proves a decrease at that recursive boundary; it does
    not establish that lawful executions always pass the guard. *)

From Stdlib Require Import NArith Arith.Wf_nat.
Require Import MonadExecutionSpecs.Termination.Natural.

Ltac solve_run_decrease :=
  unfold ltof;
  try match goal with
  | [ measure := _ : _ -> nat |- _ ] => unfold measure
  end;
  cbn beta iota zeta;
  apply n_rank_strict;
  apply N.ltb_lt;
  assumption.
