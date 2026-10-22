From Stdlib Require Import ZArith Lia.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import MonadVM.Numeric.

Open Scope Z_scope.

(** The generated U256 addition used to advance the VM program counter is
    extraction of the low 256 bits of the sum. *)
Lemma generated_u256_increment_eq_extract
    `{U : RocqOfOCaml.Basics.Unreachable Z.t} (pc : Z) :
  MonadVM.Numeric.U256.op_plus
    (_rocq_assumption_0 := U)
    (MonadVM.Numeric.U256.one (_rocq_assumption_0 := U)) pc =
  RocqOfOCaml.OCamlZ.extract (1 + pc) 0 256.
Proof.
  cbn.
  unfold MonadVM.Numeric.Make.Impl.to_z.
  reflexivity.
Qed.

Lemma generated_u256_increment_mod
    `{U : RocqOfOCaml.Basics.Unreachable Z.t} (pc : Z) :
  MonadVM.Numeric.U256.op_plus
    (_rocq_assumption_0 := U)
    (MonadVM.Numeric.U256.one (_rocq_assumption_0 := U)) pc =
  (pc + 1) mod (2 ^ 256).
Proof.
  rewrite generated_u256_increment_eq_extract.
  rewrite (Z.add_comm 1 pc).
  unfold RocqOfOCaml.OCamlZ.extract.
  cbn [Z.ltb Z.leb orb Z.shiftr].
  change (Z.land (pc + 1) (Z.ones 256) =
    (pc + 1) mod (2 ^ 256)).
  apply Z.land_ones.
  lia.
Qed.

Lemma generated_u256_increment_range
    `{U : RocqOfOCaml.Basics.Unreachable Z.t} (pc : Z) :
  (0 <= MonadVM.Numeric.U256.op_plus
    (_rocq_assumption_0 := U)
    (MonadVM.Numeric.U256.one (_rocq_assumption_0 := U)) pc <
    2 ^ 256)%Z.
Proof.
  rewrite generated_u256_increment_mod.
  apply Z.mod_pos_bound.
  vm_compute.
  easy.
Qed.
