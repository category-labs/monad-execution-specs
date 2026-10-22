(** Exact gas effect of the generated child-call merge. *)

From Stdlib Require Import ZArith NArith Lia.
Require Import RocqOfOCaml.RocqOfOCaml.
Require MonadVM.Evmc.
Require MonadVM.Gas.
Require MonadVM.Numeric.
Require MonadVM.Support.UintN.
Require MonadVM.Support.Variants.
Require MonadVM.Vm.
Require Import MonadExecutionSpecs.Termination.VmCallGas.
Require Import MonadExecutionSpecs.Termination.VmHostGasBound.

Local Open Scope N_scope.

Section ChildGasMerge.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{U :
    RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}.
  Context `{I :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.Integer.t}.
  Context `{V : RocqOfOCaml.Basics.Unreachable unit}.

  Let State := @MonadVM.Vm.Make.MachineState.t Host_t F.

  Lemma merge_child_gas_exact
      (status : MonadVM.Evmc.Result.StatusCode.t)
      (gas_left gas_refund : Z) (state : State) :
    let next := snd (MonadVM.Vm.Make.Executor.merge_child_gas_and_refund
      status gas_left gas_refund state) in
    next.(MonadVM.Vm.Make.MachineState.t.gas) =
    (state.(MonadVM.Vm.Make.MachineState.t.gas) +
      MonadVM.Gas.of_int64 gas_left)%N.
  Proof.
    destruct status; reflexivity.
  Qed.

  Lemma spend_success_exact (amount : N) (state next : State) :
    MonadVM.Vm.Make.spend amount state = (inl tt, next) ->
    amount <= state.(MonadVM.Vm.Make.MachineState.t.gas) /\
    next.(MonadVM.Vm.Make.MachineState.t.gas) =
      state.(MonadVM.Vm.Make.MachineState.t.gas) - amount.
  Proof.
    unfold MonadVM.Vm.Make.spend.
    unfold MonadVM.Gas.op_lt, MonadVM.Support.UintN.op_lt.
    destruct (N.ltb state.(MonadVM.Vm.Make.MachineState.t.gas) amount)
      eqn:Hlt.
    - discriminate.
    - apply N.ltb_ge in Hlt.
      unfold MonadVM.Gas.op_minus,
        MonadVM.Support.UintN.op_minus.
      assert (Hge : N.leb amount
        state.(MonadVM.Vm.Make.MachineState.t.gas) = true).
      { apply N.leb_le. exact Hlt. }
      rewrite Hge.
      intro Hsuccess.
      inversion Hsuccess; subst next.
      cbn.
      lia.
  Qed.

  Lemma host_call_merge_exact
      (msg : MonadVM.Evmc.Message.t)
      (state middle next : State)
      (result : MonadVM.Evmc.Result.t) :
    MonadVM.Vm.Make.M.HostAPI.call msg state =
      (inl result, middle) ->
    MonadVM.Vm.Make.Executor.merge_child_gas_and_refund
      result.(MonadVM.Evmc.Result.t.status_code)
      result.(MonadVM.Evmc.Result.t.gas_left)
      result.(MonadVM.Evmc.Result.t.gas_refund)
      middle = (inl tt, next) ->
    next.(MonadVM.Vm.Make.MachineState.t.gas) =
      (state.(MonadVM.Vm.Make.MachineState.t.gas) +
        Z.to_N result.(MonadVM.Evmc.Result.t.gas_left))%N /\
    (0 <= result.(MonadVM.Evmc.Result.t.gas_left) <=
      RocqOfOCaml.OCamlZ.of_int64_unsigned
        msg.(MonadVM.Evmc.Message.t.gas))%Z.
  Proof.
    intros Hcall Hmerge.
    pose proof (host_api_call_checked_gas_bounded msg state middle result
      Hcall) as [[Hnonnegative Hbounded] Hpreserve].
    pose proof (merge_child_gas_exact
      result.(MonadVM.Evmc.Result.t.status_code)
      result.(MonadVM.Evmc.Result.t.gas_left)
      result.(MonadVM.Evmc.Result.t.gas_refund) middle) as Hgas.
    rewrite Hmerge in Hgas.
    cbn in Hgas.
    rewrite Hpreserve in Hgas.
    rewrite nonnegative_host_gas in Hgas by exact Hnonnegative.
    split; [exact Hgas | lia].
  Qed.

  Lemma host_call_merge_decreases
      (transfer : bool)
      (access_status : MonadVM.Support.Variants.AccessStatus.t)
      (requested before memory access delegation new_account : N)
      (msg : MonadVM.Evmc.Message.t)
      (state middle next : State)
      (result : MonadVM.Evmc.Result.t) :
    let transfer_cost := if transfer then MonadVM.Gas.call_value else 0 in
    let extra := access + delegation + transfer_cost + new_account in
    let quote :=
      MonadVM.Gas.call_gas_value transfer requested before memory extra in
    MonadVM.Vm.Make.M.HostAPI.call msg state =
      (inl result, middle) ->
    MonadVM.Vm.Make.Executor.merge_child_gas_and_refund
      result.(MonadVM.Evmc.Result.t.status_code)
      result.(MonadVM.Evmc.Result.t.gas_left)
      result.(MonadVM.Evmc.Result.t.gas_refund)
      middle = (inl tt, next) ->
    state.(MonadVM.Vm.Make.MachineState.t.gas) =
      before - (quote.(MonadVM.Gas.call_gas.caller_spent_gas) + memory) ->
    RocqOfOCaml.OCamlZ.of_int64_unsigned
      msg.(MonadVM.Evmc.Message.t.gas) =
      Z.of_N quote.(MonadVM.Gas.call_gas.callee_available_gas) ->
    MonadVM.Gas.account_access_cost access_status <= access ->
    quote.(MonadVM.Gas.call_gas.caller_spent_gas) + memory <= before ->
    next.(MonadVM.Vm.Make.MachineState.t.gas) < before.
  Proof.
    cbn zeta.
    intros Hcall Hmerge Hcharged Hforwarded Haccess Hspent.
    pose proof (host_call_merge_exact msg state middle next result
      Hcall Hmerge) as [Hgas [Hnonnegative Hbounded]].
    rewrite Hforwarded in Hbounded.
    rewrite Hgas, Hcharged.
    rewrite <- nonnegative_host_gas by exact Hnonnegative.
    eapply call_host_result_decreases; eauto.
  Qed.

  Lemma spend_host_call_merge_decreases
      (transfer : bool)
      (access_status : MonadVM.Support.Variants.AccessStatus.t)
      (requested memory access delegation new_account : N)
      (msg : MonadVM.Evmc.Message.t)
      (initial charged middle next : State)
      (result : MonadVM.Evmc.Result.t) :
    let before := initial.(MonadVM.Vm.Make.MachineState.t.gas) in
    let transfer_cost := if transfer then MonadVM.Gas.call_value else 0 in
    let extra := access + delegation + transfer_cost + new_account in
    let quote :=
      MonadVM.Gas.call_gas_value transfer requested before memory extra in
    MonadVM.Vm.Make.spend
      (quote.(MonadVM.Gas.call_gas.caller_spent_gas) + memory)
      initial = (inl tt, charged) ->
    MonadVM.Vm.Make.M.HostAPI.call msg charged =
      (inl result, middle) ->
    MonadVM.Vm.Make.Executor.merge_child_gas_and_refund
      result.(MonadVM.Evmc.Result.t.status_code)
      result.(MonadVM.Evmc.Result.t.gas_left)
      result.(MonadVM.Evmc.Result.t.gas_refund)
      middle = (inl tt, next) ->
    RocqOfOCaml.OCamlZ.of_int64_unsigned
      msg.(MonadVM.Evmc.Message.t.gas) =
      Z.of_N quote.(MonadVM.Gas.call_gas.callee_available_gas) ->
    MonadVM.Gas.account_access_cost access_status <= access ->
    next.(MonadVM.Vm.Make.MachineState.t.gas) < before.
  Proof.
    cbn zeta.
    intros Hspend Hcall Hmerge Hforwarded Haccess.
    pose proof (spend_success_exact _ _ _ Hspend)
      as [Hspent Hcharged].
    eapply host_call_merge_decreases; eauto.
  Qed.
End ChildGasMerge.
