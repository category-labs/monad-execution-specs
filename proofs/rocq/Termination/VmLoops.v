(** Ranking certificates for the increasing-index loops in generated [Vm]. *)

From Stdlib Require Import ZArith NArith Lia Strings.Ascii.
From RocqOfOCaml.Termination Require Import Common IncreasingIndex.
Require Import RocqOfOCaml.OCamlChar.
Require Import MonadExecutionSpecs.Termination.Natural.
Require Import MonadExecutionSpecs.Termination.IntegerLoops.

Local Open Scope Z_scope.

Lemma memory_dump_loop_decreases (active_bytes position : N) :
  (position < active_bytes)%N ->
  (n_increasing_index_rank active_bytes (position + 32)%N <
   n_increasing_index_rank active_bytes position)%nat.
Proof.
  intros Hposition.
  apply n_increasing_index_positive_step_decreases; lia.
Qed.

Lemma jump_destinations_next_byte_decreases
    (byte_length pc : Z) :
  pc < byte_length ->
  (increasing_index_rank byte_length (pc + 1) <
   increasing_index_rank byte_length pc)%nat.
Proof.
  intros Hpc.
  apply increasing_index_positive_step_decreases; lia.
Qed.

Lemma jump_destinations_push_decreases
    (byte_length pc push_bytes : Z) :
  pc < byte_length ->
  0 < push_bytes ->
  (increasing_index_rank byte_length (pc + 1 + push_bytes) <
   increasing_index_rank byte_length pc)%nat.
Proof.
  intros Hpc Hpush.
  replace (pc + 1 + push_bytes) with (pc + (1 + push_bytes)) by lia.
  apply increasing_index_positive_step_decreases; lia.
Qed.

(** The bytecode scanner skips the immediate bytes of PUSH1 through PUSH32
    (opcodes 0x60 through 0x7f). Every other byte advances by one. This also
    covers arbitrary bytes returned by an exceptional string-access fallback.
    Arithmetic here follows the translated mathematical [Z] model of [int]. *)
Definition jump_destinations_next (pc : Z) (opcode : ascii) : Z :=
  match opcode with
  | "`"%char | "a"%char | "b"%char | "c"%char
  | "d"%char | "e"%char | "f"%char | "g"%char
  | "h"%char | "i"%char | "j"%char | "k"%char
  | "l"%char | "m"%char | "n"%char | "o"%char
  | "p"%char | "q"%char | "r"%char | "s"%char
  | "t"%char | "u"%char | "v"%char | "w"%char
  | "x"%char | "y"%char | "z"%char | "{"%char
  | "|"%char | "}"%char | "~"%char | "127"%char =>
      pc + OCamlChar.code opcode - 96 + 2
  | _ => pc + 1
  end.

Lemma jump_destinations_next_advances (pc : Z) (opcode : ascii) :
  pc < jump_destinations_next pc opcode.
Proof.
  destruct opcode as [b0 b1 b2 b3 b4 b5 b6 b7].
  destruct b0, b1, b2, b3, b4, b5, b6, b7;
    cbn [jump_destinations_next];
    repeat match goal with
    | |- context [OCamlChar.code ?character] =>
        let value := eval vm_compute in (OCamlChar.code character) in
        change (OCamlChar.code character) with value
    end;
    lia.
Qed.

Lemma jump_destinations_next_decreases (byte_length pc : Z) (opcode : ascii) :
  pc < byte_length ->
  (increasing_index_rank byte_length (jump_destinations_next pc opcode) <
   increasing_index_rank byte_length pc)%nat.
Proof.
  intros Hpc.
  pose proof (jump_destinations_next_advances pc opcode).
  unfold increasing_index_rank.
  apply z_rank_strict_from_positive; lia.
Qed.

Ltac solve_jump_destinations_decrease :=
  expose_generated_measure;
  derive_z_boolean_facts;
  match goal with
  | |- (increasing_index_rank ?bound ?next <
        increasing_index_rank ?bound ?pc)%nat =>
      match goal with
      | byte := _ : ascii |- _ =>
          let equation := fresh "Hnext" in
          assert (equation : next = jump_destinations_next pc byte) by
            (unfold next;
             generalize byte;
             intros [b0 b1 b2 b3 b4 b5 b6 b7];
             destruct b0, b1, b2, b3, b4, b5, b6, b7; reflexivity);
          rewrite equation
      end
  end;
  apply jump_destinations_next_decreases;
  assumption.
