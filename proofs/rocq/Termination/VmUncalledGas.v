(** Gas effect of the generated CALL branch that skips a child call. *)

From Stdlib Require Import NArith Lia.
Require Import RocqOfOCaml.RocqOfOCaml.
Require MonadVM.Byte_string.
Require MonadVM.Evmc.
Require MonadVM.Gas.
Require MonadVM.Numeric.
Require MonadVM.Support.UintN.
Require MonadVM.Support.Variants.
Require MonadVM.Vm.
Require Import MonadExecutionSpecs.Termination.VmCallGas.
Require Import MonadExecutionSpecs.Termination.VmChildGasMerge.
Require Import MonadExecutionSpecs.Termination.VmOpcodeProgress.

Local Open Scope N_scope.

Section UncalledGas.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context `{U :
    RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}.

  Let State := @MonadVM.Vm.Make.MachineState.t Host_t F.

  Definition uncalled_refund_action
      (pushed : MonadVM.Numeric.U256.t) (forwarded : N) :
      @MonadVM.Vm.Make.M.t Host_t F unit :=
    MonadVM.Vm.Make.M.op_letdollar
      (MonadVM.Vm.Make.push pushed)
      (fun _ => MonadVM.Vm.Make.M.op_letdollar
        (MonadVM.Vm.Make.M.update_field
          MonadVM.Vm.Make.MachineState.gas
          (fun gas => MonadVM.Support.UintN.op_plus gas forwarded))
        (fun _ => MonadVM.Vm.Make.M.op_coloneq
          MonadVM.Vm.Make.MachineState.output_buffer
          MonadVM.Byte_string.Bytes.empty)).

  Lemma uncalled_refund_gas_exact
      (pushed : MonadVM.Numeric.U256.t) (forwarded : N)
      (state next : State) :
    uncalled_refund_action pushed forwarded state = (inl tt, next) ->
    next.(MonadVM.Vm.Make.MachineState.t.gas) =
      (state.(MonadVM.Vm.Make.MachineState.t.gas) + forwarded)%N.
  Proof.
    intro Hsuccess.
    unfold uncalled_refund_action in Hsuccess.
    destruct (bind_success_decompose _ _ _ _ _ Hsuccess)
      as [after_push [push_result [Hpush Htail]]].
    destruct (bind_success_decompose _ _ _ _ _ Htail)
      as [after_refund [refund_result [Hrefund Hbuffer]]].
    pose proof (push_preserves_gas pushed state) as Hpush_gas.
    rewrite Hpush in Hpush_gas.
    cbn in Hpush_gas.
    assert (Hrefund_gas :
      after_refund.(MonadVM.Vm.Make.MachineState.t.gas) =
      (after_push.(MonadVM.Vm.Make.MachineState.t.gas) + forwarded)%N).
    { pose proof (f_equal snd Hrefund) as Hstate.
      cbn in Hstate.
      subst after_refund.
      reflexivity. }
    pose proof (f_equal snd Hbuffer) as Hbuffer_state.
    cbn in Hbuffer_state.
    subst next.
    cbn.
    lia.
  Qed.

  Lemma spend_uncalled_refund_decreases
      (transfer : bool)
      (access_status : MonadVM.Support.Variants.AccessStatus.t)
      (requested memory access delegation new_account : N)
      (pushed : MonadVM.Numeric.U256.t)
      (initial charged next : State) :
    let before := initial.(MonadVM.Vm.Make.MachineState.t.gas) in
    let transfer_cost := if transfer then MonadVM.Gas.call_value else 0 in
    let extra := access + delegation + transfer_cost + new_account in
    let quote :=
      MonadVM.Gas.call_gas_value transfer requested before memory extra in
    MonadVM.Vm.Make.spend
      (quote.(MonadVM.Gas.call_gas.caller_spent_gas) + memory)
      initial = (inl tt, charged) ->
    uncalled_refund_action pushed
      quote.(MonadVM.Gas.call_gas.callee_available_gas) charged =
      (inl tt, next) ->
    MonadVM.Gas.account_access_cost access_status <= access ->
    next.(MonadVM.Vm.Make.MachineState.t.gas) < before.
  Proof.
    cbn zeta.
    intros Hspend Hrefund Haccess.
    pose proof (spend_success_exact _ _ _ Hspend)
      as [Hspent Hcharged].
    pose proof (uncalled_refund_gas_exact _ _ _ _ Hrefund)
      as Hnext.
    rewrite Hnext, Hcharged.
    eapply call_not_made_decreases; eauto.
  Qed.
End UncalledGas.
