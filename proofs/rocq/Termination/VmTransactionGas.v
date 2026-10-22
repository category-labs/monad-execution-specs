(** The generated transaction gas-limit gate excludes limits above 30 million. *)

From Stdlib Require Import ZArith NArith Lia.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import MonadExecutionSpecs.Termination.VmUnsignedGas.
Require MonadVM.Gas.
Require MonadVM.Result.
Require MonadVM.Execution.
Require MonadVM.Chain.Ethereum.
Require MonadVM.State.
Require MonadVM.Vm.
Require MonadVM.Numeric.
Require MonadVM.Support.UintN.

Local Open Scope N_scope.

Section TransactionGasGate.
Context `{UGas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.

Lemma transaction_gas_limit_value :
  MonadVM.Gas.tx_max_gas_limit = 30_000_000.
Proof. vm_compute. reflexivity. Qed.

Lemma successful_gas_limit_gate
    {Error : Set} (limit : N) (error : Error) :
  MonadVM.Result.when_
    (MonadVM.Gas.op_gt limit MonadVM.Gas.tx_max_gas_limit)
    ((inr error) : MonadVM.Result.t unit Error) = inl tt ->
  limit <= 30_000_000.
Proof.
  intro Hsuccess.
  unfold MonadVM.Result.when_ in Hsuccess.
  cbn in Hsuccess.
  destruct (MonadVM.Gas.op_gt limit MonadVM.Gas.tx_max_gas_limit)
    eqn:Habove.
  - rewrite transaction_gas_limit_value in Habove.
    cbn in Hsuccess.
    rewrite Habove in Hsuccess.
    cbn in Hsuccess.
    discriminate Hsuccess.
  - unfold MonadVM.Gas.op_gt, MonadVM.Support.UintN.op_gt in Habove.
    rewrite transaction_gas_limit_value in Habove.
    apply N.ltb_ge in Habove.
    exact Habove.
Qed.

Lemma successful_gas_limit_gate_bind
    {Error Value : Set} (limit : N) (error : Error)
    (next : unit -> MonadVM.Result.t Value Error) (value : Value) :
  MonadVM.Result.op_letdollar
    (MonadVM.Result.when_
      (MonadVM.Gas.op_gt limit MonadVM.Gas.tx_max_gas_limit)
      ((inr error) : MonadVM.Result.t unit Error))
    next = inl value ->
  limit <= 30_000_000.
Proof.
  intro Hsuccess.
  destruct (MonadVM.Gas.op_gt limit MonadVM.Gas.tx_max_gas_limit)
    eqn:Habove.
  - rewrite transaction_gas_limit_value in Habove.
    cbn in Hsuccess.
    discriminate Hsuccess.
  - unfold MonadVM.Gas.op_gt, MonadVM.Support.UintN.op_gt in Habove.
    rewrite transaction_gas_limit_value in Habove.
    apply N.ltb_ge in Habove.
    exact Habove.
Qed.
End TransactionGasGate.

Lemma result_bind_success_inv {A B Error : Set}
    (first : MonadVM.Result.t A Error)
    (next : A -> MonadVM.Result.t B Error) (value : B) :
  MonadVM.Result.op_letdollar first next = inl value ->
  exists intermediate,
    first = inl intermediate /\ next intermediate = inl value.
Proof.
  destruct first as [intermediate | error]; cbn.
  - intro Hsuccess. exists intermediate. split; auto.
  - discriminate.
Qed.

Section ValidatedTransaction.
Context {F : MonadVM.Execution.Make.FArgs}.

Lemma validated_transaction_gas_cap
    (block_state : MonadVM.State.BlockState.t)
    (tx : MonadVM.Chain.Ethereum.Transaction.t)
    (validation : MonadVM.Execution.Make.transaction_validation) :
  MonadVM.Execution.Make.validate_transaction block_state tx =
    inl validation ->
  (MonadVM.Chain.Ethereum.Transaction.gas_limit tx <= 30_000_000)%N.
Proof.
  intro Hvalidated.
  unfold MonadVM.Execution.Make.validate_transaction in Hvalidated.
  cbn zeta in Hvalidated.
  apply result_bind_success_inv in Hvalidated.
  destruct Hvalidated as [step1 [_ Hvalidated]].
  cbn beta iota zeta in Hvalidated.
  do 5 (apply result_bind_success_inv in Hvalidated;
    destruct Hvalidated as [? [_ Hvalidated]];
    cbn beta iota zeta in Hvalidated).
  destruct (MonadVM.Gas.op_gt
    (MonadVM.Chain.Ethereum.Transaction.gas_limit tx)
    MonadVM.Gas.tx_max_gas_limit) eqn:Habove.
  - cbn in Hvalidated. discriminate Hvalidated.
  - unfold MonadVM.Gas.op_gt, MonadVM.Support.UintN.op_gt in Habove.
    rewrite transaction_gas_limit_value in Habove.
    apply N.ltb_ge in Habove.
    exact Habove.
Qed.
End ValidatedTransaction.

Section ValidatedTransactionInitialGas.
Context {F : MonadVM.Execution.Make.FArgs}.
Context `{U64 : RocqOfOCaml.Basics.Unreachable int64}.
Context `{UGas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.

Lemma validated_transaction_message_initial_gas_cap
    (block_state : MonadVM.State.BlockState.t)
    (tx : MonadVM.Chain.Ethereum.Transaction.t)
    (validation : MonadVM.Execution.Make.transaction_validation) :
  MonadVM.Execution.Make.validate_transaction block_state tx =
    inl validation ->
  let available :=
    (MonadVM.Chain.Ethereum.Transaction.gas_limit tx -
      validation.(MonadVM.Execution.Make.transaction_validation.intrinsic_gas))%N in
  (Z.of_N (MonadVM.Gas.of_uint64
    (_rocq_assumption_0 := UGas)
    (MonadVM.Gas.to_int64
      (_rocq_assumption_0 := U64) available)) <= 30_000_000)%Z.
Proof.
  intro Hvalidated.
  cbn zeta.
  pose proof (validated_transaction_gas_cap
    block_state tx validation Hvalidated) as Hlimit.
  set (available :=
    (MonadVM.Chain.Ethereum.Transaction.gas_limit tx -
      validation.(MonadVM.Execution.Make.transaction_validation.intrinsic_gas))%N).
  assert (Havailable : (Z.of_N available < 2 ^ 63)%Z).
  { unfold available. lia. }
  pose proof (@uintn_signed_roundtrip U64 available Havailable)
    as Hroundtrip.
  unfold MonadVM.Gas.to_int64.
  rewrite initial_gas_matches_unsigned.
  - rewrite Hroundtrip. unfold available. lia.
  - rewrite Hroundtrip. lia.
Qed.
End ValidatedTransactionInitialGas.

Section ValidatedTransactionSignedMessage.
Context {F : MonadVM.Execution.Make.FArgs}.
Context `{U64 : RocqOfOCaml.Basics.Unreachable int64}.

Lemma validated_transaction_message_signed_gas_range
    (block_state : MonadVM.State.BlockState.t)
    (tx : MonadVM.Chain.Ethereum.Transaction.t)
    (validation : MonadVM.Execution.Make.transaction_validation) :
  MonadVM.Execution.Make.validate_transaction block_state tx =
    inl validation ->
  let available :=
    (MonadVM.Chain.Ethereum.Transaction.gas_limit tx -
      validation.(MonadVM.Execution.Make.transaction_validation.intrinsic_gas))%N in
  let raw := MonadVM.Gas.to_int64
    (_rocq_assumption_0 := U64) available in
  (0 <= raw <= 30_000_000)%Z.
Proof.
  intro Hvalidated.
  cbn zeta.
  pose proof (validated_transaction_gas_cap
    block_state tx validation Hvalidated) as Hlimit.
  set (available :=
    (MonadVM.Chain.Ethereum.Transaction.gas_limit tx -
      validation.(MonadVM.Execution.Make.transaction_validation.intrinsic_gas))%N).
  assert (Havailable : (Z.of_N available < 2 ^ 63)%Z).
  { unfold available. lia. }
  unfold MonadVM.Gas.to_int64.
  rewrite (@uintn_to_int64_small_identity U64 available Havailable).
  unfold available.
  lia.
Qed.
End ValidatedTransactionSignedMessage.

Section ValidatedTransactionMachineState.
Context {ExecutionF : MonadVM.Execution.Make.FArgs}.
Context {Host_t : Set} {VmF : @MonadVM.Vm.Make.FArgs Host_t}.
Context `{U : RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}.
Context `{U256 :
  RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
Context `{U64 : RocqOfOCaml.Basics.Unreachable int64}.
Context `{I :
  RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.Integer.t}.
Context `{V : RocqOfOCaml.Basics.Unreachable unit}.

Lemma validated_transaction_root_initial_machine_gas_cap
    (block_state : MonadVM.State.BlockState.t)
    (tx : MonadVM.Chain.Ethereum.Transaction.t)
    (validation : MonadVM.Execution.Make.transaction_validation)
    (host : Host_t) (memory_capacity : MonadVM.Support.UintN.t) :
  MonadVM.Execution.Make.validate_transaction block_state tx =
    inl validation ->
  let available :=
    (MonadVM.Chain.Ethereum.Transaction.gas_limit tx -
      validation.(MonadVM.Execution.Make.transaction_validation.intrinsic_gas))%N in
  let raw := MonadVM.Gas.to_int64
    (_rocq_assumption_0 := U64) available in
  let state := MonadVM.Vm.Make.MachineState.initial host
    (MonadVM.Gas.of_uint64 (_rocq_assumption_0 := U) raw)
    memory_capacity in
  (Z.of_N state.(MonadVM.Vm.Make.MachineState.t.gas) <= 30_000_000)%Z.
Proof.
  intro Hvalidated.
  cbn zeta.
  change (Z.of_N (MonadVM.Gas.of_uint64
    (_rocq_assumption_0 := U)
    (MonadVM.Gas.to_int64 (_rocq_assumption_0 := U64)
      (MonadVM.Chain.Ethereum.Transaction.gas_limit tx -
        validation.(MonadVM.Execution.Make.transaction_validation.intrinsic_gas))%N))
    <= 30_000_000)%Z.
  exact (@validated_transaction_message_initial_gas_cap
    ExecutionF U64 U block_state tx validation Hvalidated).
Qed.
End ValidatedTransactionMachineState.
