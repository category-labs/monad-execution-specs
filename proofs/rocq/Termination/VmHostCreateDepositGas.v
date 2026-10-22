(** Successful generated CREATE code-deposit charging cannot add gas. *)

From Stdlib Require Import ZArith NArith Lia.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import MonadExecutionSpecs.Termination.VmUnsignedGas.
Require Import MonadExecutionSpecs.Termination.VmPrecompileGasBound.
Require MonadVM.Gas.
Require MonadVM.Support.UintN.

Local Open Scope Z_scope.

Section Deposit.
Context `{UGas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
Context `{U64 : RocqOfOCaml.Basics.Unreachable int64}.

Lemma host_create_code_deposit_nonincreasing (raw : Z) (charge : N) :
  valid_int64_repr raw ->
  MonadVM.Gas.op_lt
    (@MonadVM.Gas.of_uint64 UGas raw) charge = false ->
  (RocqOfOCaml.OCamlZ.of_int64_unsigned
    (@MonadVM.Gas.to_uint64 U64
      (@MonadVM.Gas.op_minus UGas
        (@MonadVM.Gas.of_uint64 UGas raw) charge))
    <= RocqOfOCaml.OCamlZ.of_int64_unsigned raw)%Z.
Proof.
  intros Hvalid Hnotless.
  unfold MonadVM.Gas.op_lt, MonadVM.Support.UintN.op_lt
    in Hnotless.
  apply N.ltb_ge in Hnotless.
  unfold MonadVM.Gas.op_minus, MonadVM.Support.UintN.op_minus.
  assert (Hcharge : N.leb charge
    (@MonadVM.Gas.of_uint64 UGas raw) = true).
  { apply N.leb_le. exact Hnotless. }
  rewrite Hcharge.
  apply precompile_numeric_spend_nonincreasing.
  exact Hvalid.
Qed.

Lemma host_create_code_deposit_bounded_by_message
    (returned incoming : Z) (charge : N) :
  valid_int64_repr returned ->
  (RocqOfOCaml.OCamlZ.of_int64_unsigned returned <=
    RocqOfOCaml.OCamlZ.of_int64_unsigned incoming)%Z ->
  MonadVM.Gas.op_lt
    (@MonadVM.Gas.of_uint64 UGas returned) charge = false ->
  (RocqOfOCaml.OCamlZ.of_int64_unsigned
    (@MonadVM.Gas.to_uint64 U64
      (@MonadVM.Gas.op_minus UGas
        (@MonadVM.Gas.of_uint64 UGas returned) charge))
    <= RocqOfOCaml.OCamlZ.of_int64_unsigned incoming)%Z.
Proof.
  intros Hvalid Hbounded Hnotless.
  eapply Z.le_trans.
  - apply host_create_code_deposit_nonincreasing; assumption.
  - exact Hbounded.
Qed.
End Deposit.
