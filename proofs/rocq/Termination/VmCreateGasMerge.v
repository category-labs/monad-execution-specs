(** Generated CREATE spend, forwarding, host return, and gas merge. *)

From Stdlib Require Import ZArith NArith Lia.
Require Import RocqOfOCaml.RocqOfOCaml.
Require MonadVM.Byte_string.
Require MonadVM.Evmc.
Require MonadVM.Gas.
Require MonadVM.Numeric.
Require MonadVM.Support.UintN.
Require MonadVM.Vm.
Require Import MonadExecutionSpecs.Termination.VmCallGas.
Require Import MonadExecutionSpecs.Termination.VmChildGasMerge.
Require Import MonadExecutionSpecs.Termination.VmHostGasBound.
Require Import MonadExecutionSpecs.Termination.VmOpcodeProgress.
Require Import MonadExecutionSpecs.Termination.VmUnsignedGas.

Local Open Scope N_scope.

Section CreateGasMerge.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{U :
    RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}.
  Context `{I :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.Integer.t}.
  Context `{V : RocqOfOCaml.Basics.Unreachable unit}.

  Let State := @MonadVM.Vm.Make.MachineState.t Host_t F.

  Definition create_no_child_action
      (pushed : MonadVM.Numeric.U256.t) :
      @MonadVM.Vm.Make.M.t Host_t F unit :=
    MonadVM.Vm.Make.M.op_letdollar
      (MonadVM.Vm.Make.M.op_coloneq
        MonadVM.Vm.Make.MachineState.output_buffer
        MonadVM.Byte_string.Bytes.empty)
      (fun _ => MonadVM.Vm.Make.push pushed).

  Lemma create_no_child_preserves_gas
      (pushed : MonadVM.Numeric.U256.t) (state next : State) :
    create_no_child_action pushed state = (inl tt, next) ->
    next.(MonadVM.Vm.Make.MachineState.t.gas) =
      state.(MonadVM.Vm.Make.MachineState.t.gas).
  Proof.
    intro Hsuccess.
    unfold create_no_child_action in Hsuccess.
    destruct (bind_success_decompose _ _ _ _ _ Hsuccess)
      as [after_clear [cleared [Hclear Hpush]]].
    pose proof (f_equal snd Hclear) as Hclear_state.
    cbn in Hclear_state.
    pose proof (push_preserves_gas pushed after_clear) as Hpush_gas.
    rewrite Hpush in Hpush_gas.
    cbn in Hpush_gas.
    subst after_clear.
    cbn in Hpush_gas.
    exact Hpush_gas.
  Qed.

  Lemma spend_create_no_child_decreases
      (memory initcode : N)
      (pushed : MonadVM.Numeric.U256.t)
      (initial charged next : State) :
    let charge := memory + MonadVM.Gas.create_cost + initcode in
    MonadVM.Vm.Make.spend charge initial = (inl tt, charged) ->
    create_no_child_action pushed charged = (inl tt, next) ->
    next.(MonadVM.Vm.Make.MachineState.t.gas) <
      initial.(MonadVM.Vm.Make.MachineState.t.gas).
  Proof.
    cbn zeta.
    intros Hspend Hno_child.
    pose proof (create_no_child_preserves_gas _ _ _ Hno_child)
      as Hgas.
    assert (Hpositive :
      0 < memory + MonadVM.Gas.create_cost + initcode).
    { rewrite create_cost_value. lia. }
    pose proof (spend_success_decreases
      (memory + MonadVM.Gas.create_cost + initcode)
      initial charged Hpositive Hspend) as Hspend_decreases.
    lia.
  Qed.

  Lemma subtract_forwarded_gas_exact
      (forwarded : N) (state next : State) :
    MonadVM.Vm.Make.M.update_field
      MonadVM.Vm.Make.MachineState.gas
      (fun gas => MonadVM.Support.UintN.op_minus gas forwarded)
      state = (inl tt, next) ->
    forwarded <= state.(MonadVM.Vm.Make.MachineState.t.gas) ->
    next.(MonadVM.Vm.Make.MachineState.t.gas) =
      state.(MonadVM.Vm.Make.MachineState.t.gas) - forwarded.
  Proof.
    intros Hupdate Hle.
    pose proof (f_equal snd Hupdate) as Hstate.
    cbn in Hstate.
    unfold MonadVM.Support.UintN.op_minus in Hstate.
    assert (Hguard : N.leb forwarded
      state.(MonadVM.Vm.Make.MachineState.t.gas) = true).
    { apply N.leb_le. exact Hle. }
    rewrite Hguard in Hstate.
    subst next.
    reflexivity.
  Qed.

  Lemma create_host_merge_nonincreasing
      `{U64 : RocqOfOCaml.Basics.Unreachable int64}
      (msg : MonadVM.Evmc.Message.t)
      (available_state forwarded_state middle next : State)
      (result : MonadVM.Evmc.Result.t) :
    let available :=
      available_state.(MonadVM.Vm.Make.MachineState.t.gas) in
    let forwarded := MonadVM.Gas.minus_1_64th available in
    (Z.of_N available < 2 ^ 64)%Z ->
    MonadVM.Vm.Make.M.update_field
      MonadVM.Vm.Make.MachineState.gas
      (fun gas => MonadVM.Support.UintN.op_minus gas forwarded)
      available_state = (inl tt, forwarded_state) ->
    MonadVM.Vm.Make.M.HostAPI.call msg forwarded_state =
      (inl result, middle) ->
    MonadVM.Vm.Make.Executor.merge_child_gas_and_refund
      result.(MonadVM.Evmc.Result.t.status_code)
      result.(MonadVM.Evmc.Result.t.gas_left)
      result.(MonadVM.Evmc.Result.t.gas_refund)
      middle = (inl tt, next) ->
    msg.(MonadVM.Evmc.Message.t.gas) =
      MonadVM.Support.UintN.to_uint64 forwarded ->
    next.(MonadVM.Vm.Make.MachineState.t.gas) <= available.
  Proof.
    cbn zeta.
    intros Havailable Hsubtract Hcall Hmerge Hmessage.
    pose proof (create_forwarded_le
      available_state.(MonadVM.Vm.Make.MachineState.t.gas))
      as Hforwarded.
    pose proof (subtract_forwarded_gas_exact _ _ _ Hsubtract
      Hforwarded) as Hsubtracted.
    pose proof (host_call_merge_exact msg forwarded_state middle
      next result Hcall Hmerge) as [Hnext [Hnonnegative Hbounded]].
    rewrite Hmessage in Hbounded.
    pose proof (create_message_gas_roundtrip _ Havailable)
      as Hroundtrip.
    rewrite Hroundtrip in Hbounded.
    rewrite Hnext, Hsubtracted.
    lia.
  Qed.

  Lemma spend_create_host_merge_decreases
      (memory initcode : N)
      (msg : MonadVM.Evmc.Message.t)
      (initial charged forwarded_state middle next : State)
      (result : MonadVM.Evmc.Result.t) :
    let before := initial.(MonadVM.Vm.Make.MachineState.t.gas) in
    let charge := memory + MonadVM.Gas.create_cost + initcode in
    let available := before - charge in
    let forwarded := MonadVM.Gas.minus_1_64th available in
    MonadVM.Vm.Make.spend charge initial = (inl tt, charged) ->
    MonadVM.Vm.Make.M.update_field
      MonadVM.Vm.Make.MachineState.gas
      (fun gas => MonadVM.Support.UintN.op_minus gas forwarded)
      charged = (inl tt, forwarded_state) ->
    MonadVM.Vm.Make.M.HostAPI.call msg forwarded_state =
      (inl result, middle) ->
    MonadVM.Vm.Make.Executor.merge_child_gas_and_refund
      result.(MonadVM.Evmc.Result.t.status_code)
      result.(MonadVM.Evmc.Result.t.gas_left)
      result.(MonadVM.Evmc.Result.t.gas_refund)
      middle = (inl tt, next) ->
    RocqOfOCaml.OCamlZ.of_int64_unsigned
      msg.(MonadVM.Evmc.Message.t.gas) = Z.of_N forwarded ->
    next.(MonadVM.Vm.Make.MachineState.t.gas) < before.
  Proof.
    cbn zeta.
    intros Hspend Hsubtract Hcall Hmerge Hmessage.
    pose proof (spend_success_exact _ _ _ Hspend)
      as [Hcharge Hcharged].
    pose proof (create_forwarded_le
      (initial.(MonadVM.Vm.Make.MachineState.t.gas) -
        (memory + MonadVM.Gas.create_cost + initcode)))
      as Hforwarded.
    assert (Hle :
      MonadVM.Gas.minus_1_64th
        (initial.(MonadVM.Vm.Make.MachineState.t.gas) -
          (memory + MonadVM.Gas.create_cost + initcode)) <=
      charged.(MonadVM.Vm.Make.MachineState.t.gas)).
    { rewrite Hcharged. exact Hforwarded. }
    pose proof (subtract_forwarded_gas_exact _ _ _ Hsubtract Hle)
      as Hsubtracted.
    pose proof (host_call_merge_exact msg forwarded_state middle
      next result Hcall Hmerge) as [Hnext [Hnonnegative Hbounded]].
    rewrite Hmessage in Hbounded.
    rewrite Hnext, Hsubtracted, Hcharged.
    rewrite <- nonnegative_host_gas by exact Hnonnegative.
    eapply create_host_result_decreases; eauto.
  Qed.

  Lemma spend_create_unsigned_message_decreases
      `{U64 : RocqOfOCaml.Basics.Unreachable int64}
      (memory initcode : N)
      (msg : MonadVM.Evmc.Message.t)
      (initial charged forwarded_state middle next : State)
      (result : MonadVM.Evmc.Result.t) :
    let before := initial.(MonadVM.Vm.Make.MachineState.t.gas) in
    let charge := memory + MonadVM.Gas.create_cost + initcode in
    let available := before - charge in
    let forwarded := MonadVM.Gas.minus_1_64th available in
    (Z.of_N before < 2 ^ 64)%Z ->
    MonadVM.Vm.Make.spend charge initial = (inl tt, charged) ->
    MonadVM.Vm.Make.M.update_field
      MonadVM.Vm.Make.MachineState.gas
      (fun gas => MonadVM.Support.UintN.op_minus gas forwarded)
      charged = (inl tt, forwarded_state) ->
    MonadVM.Vm.Make.M.HostAPI.call msg forwarded_state =
      (inl result, middle) ->
    MonadVM.Vm.Make.Executor.merge_child_gas_and_refund
      result.(MonadVM.Evmc.Result.t.status_code)
      result.(MonadVM.Evmc.Result.t.gas_left)
      result.(MonadVM.Evmc.Result.t.gas_refund)
      middle = (inl tt, next) ->
    msg.(MonadVM.Evmc.Message.t.gas) =
      MonadVM.Support.UintN.to_uint64 forwarded ->
    next.(MonadVM.Vm.Make.MachineState.t.gas) < before.
  Proof.
    cbn zeta.
    intros Hbefore Hspend Hsubtract Hcall Hmerge Hmessage.
    pose proof (spend_success_exact _ _ _ Hspend)
      as [Hcharge _].
    assert (Havailable :
      (Z.of_N
        (initial.(MonadVM.Vm.Make.MachineState.t.gas) -
          (memory + MonadVM.Gas.create_cost + initcode)) < 2 ^ 64)%Z)
      by lia.
    pose proof (create_message_gas_roundtrip _ Havailable)
      as Hroundtrip.
    eapply spend_create_host_merge_decreases; eauto.
    rewrite Hmessage. exact Hroundtrip.
  Qed.
End CreateGasMerge.
