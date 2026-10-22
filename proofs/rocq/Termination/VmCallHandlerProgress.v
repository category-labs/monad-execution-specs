(** Gas effects of the generated CALL return and output path. *)

From Stdlib Require Import ZArith NArith Lia.
Require Import RocqOfOCaml.RocqOfOCaml.
Require MonadVM.Byte_string.
Require MonadVM.Chain.Ethereum.
Require MonadVM.Evmc.
Require MonadVM.Delegation.
Require MonadVM.Gas.
Require MonadVM.Numeric.
Require MonadVM.Support.UintN.
Require MonadVM.Support.Variants.
Require MonadVM.Uint64.
Require MonadVM.Vm.
Require Import MonadExecutionSpecs.Termination.VmChildGasMerge.
Require Import MonadExecutionSpecs.Termination.VmCallGas.
Require Import MonadExecutionSpecs.Termination.VmCreateHandlerProgress.
Require Import MonadExecutionSpecs.Termination.VmHostGasBound.
Require Import MonadExecutionSpecs.Termination.VmOpcodeProgress.
Require Import MonadExecutionSpecs.Termination.VmUnsignedGas.
Require Import MonadExecutionSpecs.Termination.VmUncalledGas.

Local Open Scope N_scope.

Section CallOutput.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.

  Let State := @MonadVM.Vm.Make.MachineState.t Host_t F.

  Definition call_output_action
      (output : MonadVM.Byte_string.Bytes.t)
      (write_memory : @MonadVM.Vm.Make.Memory.t Host_t F ->
        @MonadVM.Vm.Make.Memory.t Host_t F)
      (pushed : MonadVM.Numeric.U256.t) :
      @MonadVM.Vm.Make.M.t Host_t F unit :=
    MonadVM.Vm.Make.M.op_letdollar
      (MonadVM.Vm.Make.M.op_coloneq
        MonadVM.Vm.Make.MachineState.output_buffer output)
      (fun _ =>
        MonadVM.Vm.Make.M.op_letdollar
          (MonadVM.Vm.Make.M.update_field
            MonadVM.Vm.Make.MachineState.memory write_memory)
          (fun _ => MonadVM.Vm.Make.push pushed)).

  Lemma call_output_preserves_gas
      (output : MonadVM.Byte_string.Bytes.t)
      (write_memory : @MonadVM.Vm.Make.Memory.t Host_t F ->
        @MonadVM.Vm.Make.Memory.t Host_t F)
      (pushed : MonadVM.Numeric.U256.t)
      (state next : State) :
    call_output_action output write_memory pushed state =
      (inl tt, next) ->
    next.(MonadVM.Vm.Make.MachineState.t.gas) =
      state.(MonadVM.Vm.Make.MachineState.t.gas).
  Proof.
    intro Hsuccess.
    unfold call_output_action in Hsuccess.
    destruct (bind_success_decompose _ _ _ _ _ Hsuccess)
      as [after_buffer [cleared [Hbuffer Hafter_buffer]]].
    destruct (bind_success_decompose _ _ _ _ _ Hafter_buffer)
      as [after_memory [written [Hmemory Hpush]]].
    pose proof (f_equal snd Hbuffer) as Hbuffer_state.
    pose proof (f_equal snd Hmemory) as Hmemory_state.
    cbn in Hbuffer_state, Hmemory_state.
    pose proof (push_preserves_gas pushed after_memory) as Hpush_gas.
    rewrite Hpush in Hpush_gas.
    cbn in Hpush_gas.
    subst after_buffer after_memory.
    cbn in Hpush_gas.
    exact Hpush_gas.
  Qed.
End CallOutput.

Section CallRefund.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context `{Uuint :
    RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}.

  Let State := @MonadVM.Vm.Make.MachineState.t Host_t F.

  Definition refund_then_push
      (forwarded : MonadVM.Support.UintN.t)
      (pushed : MonadVM.Numeric.U256.t) :
      @MonadVM.Vm.Make.M.t Host_t F unit :=
    MonadVM.Vm.Make.M.op_letdollar
      (MonadVM.Vm.Make.M.update_field
        MonadVM.Vm.Make.MachineState.gas
        (fun gas => MonadVM.Support.UintN.op_plus gas forwarded))
      (fun _ => MonadVM.Vm.Make.push pushed).

  Lemma refund_then_push_gas_exact
      (forwarded : MonadVM.Support.UintN.t)
      (pushed : MonadVM.Numeric.U256.t)
      (state next : State) :
    refund_then_push forwarded pushed state = (inl tt, next) ->
    next.(MonadVM.Vm.Make.MachineState.t.gas) =
      state.(MonadVM.Vm.Make.MachineState.t.gas) + forwarded.
  Proof.
    intro Hsuccess.
    unfold refund_then_push in Hsuccess.
    destruct (bind_success_decompose _ _ _ _ _ Hsuccess)
      as [after_refund [refunded [Hrefund Hpush]]].
    pose proof (f_equal snd Hrefund) as Hrefund_state.
    cbn in Hrefund_state.
    pose proof (push_preserves_gas pushed after_refund) as Hpush_gas.
    rewrite Hpush in Hpush_gas.
    cbn in Hpush_gas.
    subst after_refund.
    cbn in Hpush_gas.
    exact Hpush_gas.
  Qed.
End CallRefund.

Section CallHostOutput.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{Uuint :
    RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}.
  Context `{Uinteger :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.Integer.t}.
  Context `{Uunit : RocqOfOCaml.Basics.Unreachable unit}.

  Let State := @MonadVM.Vm.Make.MachineState.t Host_t F.

  Lemma call_host_output_bounded
      (msg : MonadVM.Evmc.Message.t)
      (result : MonadVM.Evmc.Result.t)
      (forwarded : N)
      (output : MonadVM.Byte_string.Bytes.t)
      (write_memory : @MonadVM.Vm.Make.Memory.t Host_t F ->
        @MonadVM.Vm.Make.Memory.t Host_t F)
      (pushed : MonadVM.Numeric.U256.t)
      (state middle merged next : State) :
    MonadVM.Vm.Make.M.HostAPI.call msg state = (inl result, middle) ->
    MonadVM.Vm.Make.Executor.merge_child_gas_and_refund
      result.(MonadVM.Evmc.Result.t.status_code)
      result.(MonadVM.Evmc.Result.t.gas_left)
      result.(MonadVM.Evmc.Result.t.gas_refund)
      middle = (inl tt, merged) ->
    call_output_action output write_memory pushed merged =
      (inl tt, next) ->
    (RocqOfOCaml.OCamlZ.of_int64_unsigned
      msg.(MonadVM.Evmc.Message.t.gas) <= Z.of_N forwarded)%Z ->
    next.(MonadVM.Vm.Make.MachineState.t.gas) <=
      state.(MonadVM.Vm.Make.MachineState.t.gas) + forwarded.
  Proof.
    intros Hcall Hmerge Houtput Hmessage.
    pose proof (host_call_merge_exact msg state middle merged
      result Hcall Hmerge) as [Hmerged [Hnonnegative Hbounded]].
    pose proof (call_output_preserves_gas output write_memory pushed
      merged next Houtput) as Hfinal.
    rewrite Hfinal, Hmerged.
    lia.
  Qed.
End CallHostOutput.

Section GenericCallBody.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{Uint32 :
    RocqOfOCaml.Basics.Unreachable RocqOfOCaml.OCamlInt32.t}.
  Context `{Uevmc64 : RocqOfOCaml.Basics.Unreachable MonadVM.Uint64.t}.
  Context `{Uuint :
    RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}.
  Context `{U256 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
  Context `{Uinteger :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.Integer.t}.
  Context `{Uaddress :
    RocqOfOCaml.Basics.Unreachable MonadVM.Chain.Ethereum.Address.t}.
  Context `{Ubytes :
    RocqOfOCaml.Basics.Unreachable MonadVM.Byte_string.Bytes.t}.
  Context `{Uunit : RocqOfOCaml.Basics.Unreachable unit}.
  Context `{Ustring : RocqOfOCaml.Basics.Unreachable string}.
  Context `{Ubytes_list :
    RocqOfOCaml.Basics.Unreachable
      (list MonadVM.Byte_string.Bytes.t)}.
  Context `{Uint_list : RocqOfOCaml.Basics.Unreachable (list int)}.
  Context `{Uint : RocqOfOCaml.Basics.Unreachable int}.
  Context `{Ub32 :
    RocqOfOCaml.Basics.Unreachable
      MonadVM.Byte_string.B32.(MonadVM.Byte_string.Fixed.Fixed_result.t)}.
  Context `{Umemory_size :
    RocqOfOCaml.Basics.Unreachable
      (@MonadVM.Vm.Make.Memory.t Host_t F -> MonadVM.Support.UintN.t)}.

  Let State := @MonadVM.Vm.Make.MachineState.t Host_t F.

  Lemma generic_call_impl_gas_bounded
      (kind : MonadVM.Evmc.Message.CallKind.t)
      (call_gas value : MonadVM.Numeric.U256.t)
      (sender recipient code_address : MonadVM.Vm.Make.Address.t)
      (delegation : @MonadVM.Vm.Make.Executor.delegation Host_t F E)
      (static : bool)
      (input_start input_size output_start output_size :
        MonadVM.Numeric.U256.t)
      (forwarded : N)
      (state next : State) :
    MonadVM.Numeric.U256.to_uint
      (_rocq_assumption_0 := Uuint) call_gas = forwarded ->
    (forall (U64 : RocqOfOCaml.Basics.Unreachable int64),
      RocqOfOCaml.OCamlZ.of_int64_unsigned
        (MonadVM.Numeric.U256.to_uint64
          (_rocq_assumption_0 := U64) call_gas) <= Z.of_N forwarded)%Z ->
    MonadVM.Vm.Make.Executor.generic_call_impl
      (_rocq_assumption_0 := Uint32)
      (_rocq_assumption_1 := Uevmc64)
      (_rocq_assumption_2 := Uuint)
      (_rocq_assumption_3 := U256)
      (_rocq_assumption_4 := Uinteger)
      (_rocq_assumption_5 := Uaddress)
      (_rocq_assumption_6 := Ubytes)
      (_rocq_assumption_7 := Uunit)
      (_rocq_assumption_8 := Ustring)
      (_rocq_assumption_9 := Ubytes_list)
      (_rocq_assumption_10 := Uint_list)
      (_rocq_assumption_11 := Uint)
      (_rocq_assumption_12 := Ub32)
      (_rocq_assumption_13 := Umemory_size)
      kind call_gas value sender recipient code_address delegation static
      input_start input_size output_start output_size state =
        (inl tt, next) ->
    next.(MonadVM.Vm.Make.MachineState.t.gas) <=
      state.(MonadVM.Vm.Make.MachineState.t.gas) + forwarded.
  Proof.
    intros Hforwarded Hmessage Hrun.
    unfold MonadVM.Vm.Make.Executor.generic_call_impl in Hrun.
    destruct (bind_success_decompose _ _ _ _ _ Hrun)
      as [cleared [clear_value [Hclear Hafter_clear]]].
    pose proof (f_equal snd Hclear) as Hclear_state.
    cbn in Hclear_state.
    subst cleared.
    destruct (Z.gtb _ _) eqn:Hdepth.
    - destruct (bind_success_decompose _ _ _ _ _ Hafter_clear)
        as [refunded [refund_value [Hrefund Hpush]]].
      destruct refund_value.
      pose proof (f_equal snd Hrefund) as Hrefund_state.
      cbn in Hrefund_state.
      pose proof (push_preserves_gas
        (MonadVM.Numeric.U256.zero (_rocq_assumption_0 := U256))
        refunded) as Hpush_gas.
      rewrite Hpush in Hpush_gas.
      cbn in Hpush_gas.
      subst refunded.
      cbn in Hpush_gas.
      unfold MonadVM.Support.UintN.op_plus in Hpush_gas.
      unfold MonadVM.Numeric.U256.to_uint in Hforwarded.
      cbn in Hforwarded.
      rewrite Hforwarded in Hpush_gas.
      lia.
    - destruct (bind_success_decompose _ _ _ _ _ Hafter_clear)
        as [memory_state [memory [Hmemory Hafter_memory]]].
      pose proof (f_equal snd Hmemory) as Hmemory_state.
      cbn in Hmemory_state.
      subst memory_state.
      destruct delegation; cbn zeta in Hafter_memory.
      all: destruct (bind_success_decompose _ _ _ _ _ Hafter_memory)
        as [middle [result [Hcall Hafter_call]]].
      all: destruct result as [status gas_left gas_refund output address].
      all: destruct (bind_success_decompose _ _ _ _ _ Hafter_call)
        as [merged [merge_value [Hmerge Houtput]]].
      all: destruct merge_value.
      all: cbn zeta in Houtput.
      all: pose proof (call_output_preserves_gas _ _ _ _ _ Houtput)
        as Hfinal.
      all: pose proof (host_call_merge_exact _
        (MonadVM.Vm.Make.MachineState.t.with_output_buffer
          MonadVM.Byte_string.Bytes.empty state) middle merged
        {| MonadVM.Evmc.Result.t.status_code := status;
           MonadVM.Evmc.Result.t.gas_left := gas_left;
           MonadVM.Evmc.Result.t.gas_refund := gas_refund;
           MonadVM.Evmc.Result.t.output_data := output;
           MonadVM.Evmc.Result.t.create_address := address |}
        Hcall Hmerge) as [Hmerged [Hnonnegative Hbounded]].
      all: rewrite Hfinal, Hmerged.
      all: cbn.
      all: cbn [MonadVM.Evmc.Result.t.gas_left
        MonadVM.Evmc.Message.t.gas] in Hbounded, Hnonnegative.
      all: assert (Hgas_bound : (gas_left <= Z.of_N forwarded)%Z)
        by (eapply Z.le_trans; [exact Hbounded | apply Hmessage]).
      all: lia.
  Qed.

  Lemma generic_call_impl_forwarded_bound
      (kind : MonadVM.Evmc.Message.CallKind.t)
      (value : MonadVM.Numeric.U256.t)
      (sender recipient code_address : MonadVM.Vm.Make.Address.t)
      (delegation : @MonadVM.Vm.Make.Executor.delegation Host_t F E)
      (static : bool)
      (input_start input_size output_start output_size :
        MonadVM.Numeric.U256.t)
      (forwarded : N)
      (state next : State) :
    (Z.of_N forwarded < 2 ^ 64)%Z ->
    MonadVM.Vm.Make.Executor.generic_call_impl
      (_rocq_assumption_0 := Uint32)
      (_rocq_assumption_1 := Uevmc64)
      (_rocq_assumption_2 := Uuint)
      (_rocq_assumption_3 := U256)
      (_rocq_assumption_4 := Uinteger)
      (_rocq_assumption_5 := Uaddress)
      (_rocq_assumption_6 := Ubytes)
      (_rocq_assumption_7 := Uunit)
      (_rocq_assumption_8 := Ustring)
      (_rocq_assumption_9 := Ubytes_list)
      (_rocq_assumption_10 := Uint_list)
      (_rocq_assumption_11 := Uint)
      (_rocq_assumption_12 := Ub32)
      (_rocq_assumption_13 := Umemory_size)
      kind
      (MonadVM.Numeric.U256.of_uint_exn
        (_rocq_assumption_0 := U256) forwarded)
      value sender recipient code_address delegation static
      input_start input_size output_start output_size state =
        (inl tt, next) ->
    next.(MonadVM.Vm.Make.MachineState.t.gas) <=
      state.(MonadVM.Vm.Make.MachineState.t.gas) + forwarded.
  Proof.
    intros Hfits Hrun.
    eapply (generic_call_impl_gas_bounded kind
      (MonadVM.Numeric.U256.of_uint_exn
        (_rocq_assumption_0 := U256) forwarded)
      value sender recipient code_address delegation static
      input_start input_size output_start output_size
      forwarded state next).
    - apply u256_forwarded_uint_roundtrip. exact Hfits.
    - intro U64.
      pose proof (u256_forwarded_gas_roundtrip
        (U256 := U256) (U64 := U64) forwarded Hfits) as Hroundtrip.
      lia.
    - exact Hrun.
  Qed.

  Lemma spend_generic_call_decreases
      `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}
      (transfer : bool)
      (access_status : MonadVM.Support.Variants.AccessStatus.t)
      (requested memory access delegation_gas new_account : N)
      (kind : MonadVM.Evmc.Message.CallKind.t)
      (value : MonadVM.Numeric.U256.t)
      (sender recipient code_address : MonadVM.Vm.Make.Address.t)
      (delegation : @MonadVM.Vm.Make.Executor.delegation Host_t F E)
      (static : bool)
      (input_start input_size output_start output_size :
        MonadVM.Numeric.U256.t)
      (state charged next : State) :
    let before := state.(MonadVM.Vm.Make.MachineState.t.gas) in
    let transfer_cost := if transfer then MonadVM.Gas.call_value else 0 in
    let extra := access + delegation_gas + transfer_cost + new_account in
    let quote := MonadVM.Gas.call_gas_value
      transfer requested before memory extra in
    (Z.of_N before < 2 ^ 64)%Z ->
    MonadVM.Gas.account_access_cost access_status <= access ->
    MonadVM.Vm.Make.spend
      (quote.(MonadVM.Gas.call_gas.caller_spent_gas) + memory)
      state = (inl tt, charged) ->
    MonadVM.Vm.Make.Executor.generic_call_impl
      (_rocq_assumption_0 := Uint32)
      (_rocq_assumption_1 := Uevmc64)
      (_rocq_assumption_2 := Uuint)
      (_rocq_assumption_3 := U256)
      (_rocq_assumption_4 := Uinteger)
      (_rocq_assumption_5 := Uaddress)
      (_rocq_assumption_6 := Ubytes)
      (_rocq_assumption_7 := Uunit)
      (_rocq_assumption_8 := Ustring)
      (_rocq_assumption_9 := Ubytes_list)
      (_rocq_assumption_10 := Uint_list)
      (_rocq_assumption_11 := Uint)
      (_rocq_assumption_12 := Ub32)
      (_rocq_assumption_13 := Umemory_size)
      kind
      (MonadVM.Numeric.U256.of_uint_exn
        (_rocq_assumption_0 := U256)
        quote.(MonadVM.Gas.call_gas.callee_available_gas))
      value sender recipient code_address delegation static
      input_start input_size output_start output_size charged =
        (inl tt, next) ->
    next.(MonadVM.Vm.Make.MachineState.t.gas) < before.
  Proof.
    cbn zeta.
    intros Hbefore Haccess Hspend Hcall.
    pose proof (spend_success_exact _ _ _ Hspend)
      as [Hspent Hcharged].
    pose proof (call_forwarded_fits_uint64 transfer access_status
      requested state.(MonadVM.Vm.Make.MachineState.t.gas)
      memory access delegation_gas new_account
      Hbefore Haccess Hspent) as Hforwarded.
    pose proof (generic_call_impl_forwarded_bound kind value
      sender recipient code_address delegation static input_start
      input_size output_start output_size _ charged next Hforwarded Hcall)
      as Hnext.
    pose proof (call_not_made_decreases transfer access_status requested
      state.(MonadVM.Vm.Make.MachineState.t.gas)
      memory access delegation_gas new_account Haccess Hspent)
      as Hstrict.
    cbn zeta in Hstrict.
    rewrite Hcharged in Hnext.
    lia.
  Qed.

  Lemma call_quote_total_decreases
      `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}
      (transfer : bool)
      (requested before memory extra : N) :
    let quote := MonadVM.Gas.call_gas_value
      transfer requested before memory extra in
    100 + (if transfer then MonadVM.Gas.call_value else 0) <= extra ->
    quote.(MonadVM.Gas.call_gas.caller_spent_gas) + memory <= before ->
    before - (quote.(MonadVM.Gas.call_gas.caller_spent_gas) + memory)
      + quote.(MonadVM.Gas.call_gas.callee_available_gas) < before.
  Proof.
    cbn zeta.
    intros Hextra Hspent.
    destruct transfer;
      unfold MonadVM.Gas.call_gas_value in *;
      cbn [MonadVM.Gas.call_gas.caller_spent_gas
           MonadVM.Gas.call_gas.callee_available_gas] in *;
      try rewrite call_value_cost in *;
      try rewrite call_stipend_value in *;
      unfold MonadVM.Support.UintN.op_plus in *;
      lia.
  Qed.

  Lemma quote_call_branch_decreases
      `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}
      (transfer : bool)
      (requested memory extra : N)
      (kind : MonadVM.Evmc.Message.CallKind.t)
      (value pushed : MonadVM.Numeric.U256.t)
      (sender recipient code_address : MonadVM.Vm.Make.Address.t)
      (delegation : @MonadVM.Vm.Make.Executor.delegation Host_t F E)
      (static skip : bool)
      (input_start input_size output_start output_size :
        MonadVM.Numeric.U256.t)
      (state charged branch_state next : State) :
    let before := state.(MonadVM.Vm.Make.MachineState.t.gas) in
    let quote := MonadVM.Gas.call_gas_value
      transfer requested before memory extra in
    (Z.of_N before < 2 ^ 64)%Z ->
    100 + (if transfer then MonadVM.Gas.call_value else 0) <= extra ->
    MonadVM.Vm.Make.spend
      (quote.(MonadVM.Gas.call_gas.caller_spent_gas) + memory)
      state = (inl tt, charged) ->
    branch_state.(MonadVM.Vm.Make.MachineState.t.gas) <=
      charged.(MonadVM.Vm.Make.MachineState.t.gas) ->
    (if skip then
      uncalled_refund_action pushed
        quote.(MonadVM.Gas.call_gas.callee_available_gas)
    else
      MonadVM.Vm.Make.Executor.generic_call_impl
        (_rocq_assumption_0 := Uint32)
        (_rocq_assumption_1 := Uevmc64)
        (_rocq_assumption_2 := Uuint)
        (_rocq_assumption_3 := U256)
        (_rocq_assumption_4 := Uinteger)
        (_rocq_assumption_5 := Uaddress)
        (_rocq_assumption_6 := Ubytes)
        (_rocq_assumption_7 := Uunit)
        (_rocq_assumption_8 := Ustring)
        (_rocq_assumption_9 := Ubytes_list)
        (_rocq_assumption_10 := Uint_list)
        (_rocq_assumption_11 := Uint)
        (_rocq_assumption_12 := Ub32)
        (_rocq_assumption_13 := Umemory_size)
        kind
        (MonadVM.Numeric.U256.of_uint_exn
          (_rocq_assumption_0 := U256)
          quote.(MonadVM.Gas.call_gas.callee_available_gas))
        value sender recipient code_address delegation static
        input_start input_size output_start output_size)
      branch_state = (inl tt, next) ->
    next.(MonadVM.Vm.Make.MachineState.t.gas) < before.
  Proof.
    cbn zeta.
    intros Hbefore Hextra Hspend Hbranch_gas Hbranch.
    pose proof (spend_success_exact _ _ _ Hspend)
      as [Hspent Hcharged].
    pose proof (call_quote_total_decreases transfer requested
      state.(MonadVM.Vm.Make.MachineState.t.gas)
      memory extra Hextra Hspent)
      as Hstrict.
    cbn zeta in Hstrict.
    destruct skip.
    - pose proof (uncalled_refund_gas_exact _ _ branch_state next
        Hbranch) as Hnext.
      rewrite Hnext.
      rewrite Hcharged in Hbranch_gas.
      lia.
    - assert (Hfits :
        (Z.of_N
          (MonadVM.Gas.call_gas_value transfer requested
            state.(MonadVM.Vm.Make.MachineState.t.gas)
            memory extra).(MonadVM.Gas.call_gas.callee_available_gas)
          < 2 ^ 64)%Z) by lia.
      pose proof (generic_call_impl_forwarded_bound kind value
        sender recipient code_address delegation static input_start
        input_size output_start output_size _ branch_state next
        Hfits Hbranch) as Hnext.
      rewrite Hcharged in Hbranch_gas.
      lia.
  Qed.
End GenericCallBody.

Section CallAccessCost.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.

  Lemma delegation_access_keeps_base
      (status : MonadVM.Support.Variants.AccessStatus.t)
      (delegation : @MonadVM.Vm.Make.Executor.delegation Host_t F E) :
    MonadVM.Gas.account_access_cost status <=
      match delegation with
      | MonadVM.Vm.Make.Executor.Direct _ =>
          MonadVM.Gas.account_access_cost status
      | MonadVM.Vm.Make.Executor.Delegated details =>
          MonadVM.Gas.account_access_cost status +
            details.(MonadVM.Vm.Make.Executor.delegation.Delegated.delegation_access_gas)
      end.
  Proof.
    destruct delegation; cbn; lia.
  Qed.

  Lemma account_exists_nonincreasing
      (address : MonadVM.Vm.Make.Address.t) :
    gas_nonincreasing
      (MonadVM.Vm.Make.M.HostAPI.account_exists address).
  Proof.
    unfold MonadVM.Vm.Make.M.HostAPI.account_exists.
    apply host_lift_nonincreasing.
  Qed.

  Lemma call_write_guard_nonincreasing (condition : bool) :
    gas_nonincreasing
      (MonadVM.Vm.Make.M.when_ condition
        (@MonadVM.Vm.Make.Executor.check_write_permissions Host_t F E)).
  Proof.
    destruct condition.
    - apply check_write_permissions_nonincreasing.
    - apply return_nonincreasing.
  Qed.
End CallAccessCost.

(** Strict gas decrease for every successful continuation of the generated
    CALL handler, under the unsigned bounded host-return contract. *)
Section CallOpcode.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{Uint32 :
    RocqOfOCaml.Basics.Unreachable RocqOfOCaml.OCamlInt32.t}.
  Context `{Uevmc64 : RocqOfOCaml.Basics.Unreachable MonadVM.Uint64.t}.
  Context `{Uuint :
    RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}.
  Context `{U256 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
  Context `{Uinteger :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.Integer.t}.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
  Context `{Udelegation :
    RocqOfOCaml.Basics.Unreachable MonadVM.Delegation.Address.t}.
  Context `{Uaddress :
    RocqOfOCaml.Basics.Unreachable MonadVM.Chain.Ethereum.Address.t}.
  Context `{Ubytes :
    RocqOfOCaml.Basics.Unreachable MonadVM.Byte_string.Bytes.t}.
  Context `{Uunit : RocqOfOCaml.Basics.Unreachable unit}.
  Context `{Ustring : RocqOfOCaml.Basics.Unreachable string}.
  Context `{Ubytes_list :
    RocqOfOCaml.Basics.Unreachable
      (list MonadVM.Byte_string.Bytes.t)}.
  Context `{Uint_list : RocqOfOCaml.Basics.Unreachable (list int)}.
  Context `{Uint : RocqOfOCaml.Basics.Unreachable int}.
  Context `{Uuint_function :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Support.UintN.t -> MonadVM.Support.UintN.t)}.
  Context `{Ub32 :
    RocqOfOCaml.Basics.Unreachable
      MonadVM.Byte_string.B32.(MonadVM.Byte_string.Fixed.Fixed_result.t)}.
  Context `{Uextend :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Numeric.U256.t -> MonadVM.Numeric.U256.t ->
        @MonadVM.Vm.Make.Memory.t Host_t F ->
        @MonadVM.Vm.Make.M.Option.t Host_t F
          (@MonadVM.Vm.Make.Memory.t Host_t F))}.
  Context `{Umemory_size :
    RocqOfOCaml.Basics.Unreachable
      (@MonadVM.Vm.Make.Memory.t Host_t F -> MonadVM.Support.UintN.t)}.

  Lemma call_opcode_impl_bounded_decreasing
      (kind : MonadVM.Evmc.Message.CallKind.t)
      (gas : MonadVM.Support.UintN.t)
      (value : MonadVM.Numeric.U256.t)
      (sender recipient code_address : MonadVM.Vm.Make.Address.t)
      (input_start input_size output_start output_size :
        MonadVM.Numeric.U256.t)
      (static_call : bool) :
    gas_bounded_decreasing
      (MonadVM.Vm.Make.Executor.call_opcode_impl
        (_rocq_assumption_0 := Uint32)
        (_rocq_assumption_1 := Uevmc64)
        (_rocq_assumption_2 := Uuint)
        (_rocq_assumption_3 := U256)
        (_rocq_assumption_4 := Uinteger)
        (_rocq_assumption_5 := Ugas)
        (_rocq_assumption_6 := Udelegation)
        (_rocq_assumption_7 := Uaddress)
        (_rocq_assumption_8 := Ubytes)
        (_rocq_assumption_9 := Uunit)
        (_rocq_assumption_10 := Ustring)
        (_rocq_assumption_11 := Ubytes_list)
        (_rocq_assumption_12 := Uint_list)
        (_rocq_assumption_13 := Uint)
        (_rocq_assumption_14 := Uuint_function)
        (_rocq_assumption_15 := Ub32)
        (_rocq_assumption_16 := Uextend)
        (_rocq_assumption_17 := Umemory_size)
        kind gas value sender recipient code_address
        input_start input_size output_start output_size static_call).
  Proof.
    intros state continuing next Hbound Hrun.
    unfold MonadVM.Vm.Make.Executor.call_opcode_impl in Hrun.
    destruct (bind_success_decompose _ _ _ _ _ Hrun)
      as [after_input [input_memory_gas [Hinput Hafter_input]]].
    destruct (bind_success_decompose _ _ _ _ _ Hafter_input)
      as [after_output [output_memory_gas [Houtput Hafter_output]]].
    destruct (bind_success_decompose _ _ _ _ _ Hafter_output)
      as [after_access [base_access [Haccess Hafter_access]]].
    destruct (map_success_value _ _ _ _ _ Haccess)
      as [access_status [Haccount Hbase_access]].
    destruct (bind_success_decompose _ _ _ _ _ Hafter_access)
      as [after_delegation [delegation [Hdelegation Hafter_delegation]]].
    destruct (bind_success_decompose _ _ _ _ _ Hafter_delegation)
      as [after_exists [target_is_alive [Hexists Hafter_exists]]].
    destruct (bind_success_decompose _ _ _ _ _ Hafter_exists)
      as [after_read [before [Hread Hafter_read]]].
    cbn in Hread.
    inversion Hread; subst after_read before.
    destruct (bind_success_decompose _ _ _ _ _ Hafter_read)
      as [after_spend [spent [Hspend Hafter_spend]]].
    destruct spent.
    destruct (bind_success_decompose _ _ _ _ _ Hafter_spend)
      as [after_guard [guarded [Hguard Hafter_guard]]].
    destruct guarded.
    destruct (bind_success_decompose _ _ _ _ _ Hafter_guard)
      as [after_balance [self_balance [Hbalance Hafter_balance]]].
    destruct (bind_success_decompose _ _ _ _ _ Hafter_balance)
      as [after_branch [branch_value [Hbranch Hpc]]].
    destruct branch_value.
    pose proof ((@extend_memory_to_nonincreasing Host_t F E
      Uuint U256 Ugas Uuint_function Uextend input_start input_size)
      state input_memory_gas after_input Hinput) as Hinput_gas.
    pose proof ((@extend_memory_to_nonincreasing Host_t F E
      Uuint U256 Ugas Uuint_function Uextend output_start output_size)
      after_input output_memory_gas after_output Houtput)
      as Houtput_gas.
    pose proof (access_account_nonincreasing code_address
      after_output access_status after_access Haccount) as Haccess_gas.
    pose proof (access_delegation_nonincreasing code_address
      after_access delegation after_delegation Hdelegation)
      as Hdelegation_gas.
    pose proof (account_exists_nonincreasing recipient
      after_delegation target_is_alive after_exists Hexists)
      as Hexists_gas.
    pose proof (call_write_guard_nonincreasing _
      after_spend tt after_guard Hguard) as Hguard_gas.
    pose proof (get_balance_nonincreasing
      (@MonadVM.Vm.Make.Executor.self Host_t F E)
      after_guard self_balance after_balance Hbalance)
      as Hbalance_gas.
    pose proof (increase_pc_nonincreasing
      after_branch continuing next Hpc) as Hpc_gas.
    set (transfer := andb
      (negb (match kind with
        | MonadVM.Evmc.Message.CallKind.DelegateCall => true
        | _ => false end))
      (MonadVM.Numeric.U256.op_ltgt value
        (MonadVM.Numeric.U256.zero (_rocq_assumption_0 := U256)))) in *.
    set (memory := MonadVM.Gas.op_plus
      input_memory_gas output_memory_gas) in *.
    set (access_total := match delegation with
      | MonadVM.Vm.Make.Executor.Direct _ => base_access
      | MonadVM.Vm.Make.Executor.Delegated d =>
          MonadVM.Gas.op_plus base_access
            d.(MonadVM.Vm.Make.Executor.delegation.Delegated.delegation_access_gas)
      end) in *.
    set (extra := MonadVM.Support.UintN.op_plus
      (MonadVM.Support.UintN.op_plus access_total
        (if transfer then MonadVM.Gas.call_value else MonadVM.Gas.zero))
      (if andb transfer (negb target_is_alive)
       then MonadVM.Gas.new_account_cost else MonadVM.Gas.zero)) in *.
    assert (Hbefore_exists :
      (Z.of_N after_exists.(MonadVM.Vm.Make.MachineState.t.gas) <
        2 ^ 64)%Z) by lia.
    assert (Hbranch_gas :
      after_balance.(MonadVM.Vm.Make.MachineState.t.gas) <=
        after_spend.(MonadVM.Vm.Make.MachineState.t.gas)) by lia.
    assert (Hextra :
      100 + (if transfer then MonadVM.Gas.call_value else 0) <= extra).
    { unfold extra, access_total.
      rewrite Hbase_access.
      pose proof (account_access_min access_status) as Hmin.
      destruct transfer, delegation, target_is_alive;
        cbn [andb negb];
        unfold MonadVM.Gas.op_plus, MonadVM.Gas.zero,
          MonadVM.Support.UintN.op_plus,
          MonadVM.Support.UintN.zero.
      all: lia. }
    pose proof (quote_call_branch_decreases transfer gas memory
      extra kind value (MonadVM.Numeric.U256.zero
        (_rocq_assumption_0 := U256))
      sender recipient code_address delegation _ _
      input_start input_size output_start output_size
      after_exists after_spend after_balance after_branch
      Hbefore_exists Hextra Hspend Hbranch_gas Hbranch) as Houter.
    lia.
  Qed.
End CallOpcode.

Section CallFamily.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{Uint32 :
    RocqOfOCaml.Basics.Unreachable RocqOfOCaml.OCamlInt32.t}.
  Context `{Uevmc64 : RocqOfOCaml.Basics.Unreachable MonadVM.Uint64.t}.
  Context `{Uuint :
    RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}.
  Context `{U256 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
  Context `{Uinteger :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.Integer.t}.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
  Context `{Udelegation :
    RocqOfOCaml.Basics.Unreachable MonadVM.Delegation.Address.t}.
  Context `{Uaddress :
    RocqOfOCaml.Basics.Unreachable MonadVM.Chain.Ethereum.Address.t}.
  Context `{Ubytes :
    RocqOfOCaml.Basics.Unreachable MonadVM.Byte_string.Bytes.t}.
  Context `{Uunit : RocqOfOCaml.Basics.Unreachable unit}.
  Context `{Ustring : RocqOfOCaml.Basics.Unreachable string}.
  Context `{Ubytes_list :
    RocqOfOCaml.Basics.Unreachable
      (list MonadVM.Byte_string.Bytes.t)}.
  Context `{Uint_list : RocqOfOCaml.Basics.Unreachable (list int)}.
  Context `{Uint : RocqOfOCaml.Basics.Unreachable int}.
  Context `{Uuint_function :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Support.UintN.t -> MonadVM.Support.UintN.t)}.
  Context `{Ub32 :
    RocqOfOCaml.Basics.Unreachable
      MonadVM.Byte_string.B32.(MonadVM.Byte_string.Fixed.Fixed_result.t)}.
  Context `{Uextend :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Numeric.U256.t -> MonadVM.Numeric.U256.t ->
        @MonadVM.Vm.Make.Memory.t Host_t F ->
        @MonadVM.Vm.Make.M.Option.t Host_t F
          (@MonadVM.Vm.Make.Memory.t Host_t F))}.
  Context `{Umemory_size :
    RocqOfOCaml.Basics.Unreachable
      (@MonadVM.Vm.Make.Memory.t Host_t F -> MonadVM.Support.UintN.t)}.

  Context `{Urepr :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.Repr.t}.
  Context `{Uascii : RocqOfOCaml.Basics.Unreachable ascii}.
  Context `{Uint_pair : RocqOfOCaml.Basics.Unreachable (int * int)}.

  Lemma call_opcode_wrapper_bounded_decreasing :
    gas_bounded_decreasing
      (MonadVM.Vm.Make.Executor.call
        (_rocq_assumption_0 := Uint32)
        (_rocq_assumption_1 := Uevmc64)
        (_rocq_assumption_2 := Uuint)
        (_rocq_assumption_3 := Urepr)
        (_rocq_assumption_4 := U256)
        (_rocq_assumption_5 := Uinteger)
        (_rocq_assumption_6 := Ugas)
        (_rocq_assumption_7 := Udelegation)
        (_rocq_assumption_8 := Uaddress)
        (_rocq_assumption_9 := Ubytes)
        (_rocq_assumption_10 := Uunit)
        (_rocq_assumption_11 := Ustring)
        (_rocq_assumption_12 := Ubytes_list)
        (_rocq_assumption_13 := Uint_list)
        (_rocq_assumption_14 := Uint)
        (_rocq_assumption_15 := Uascii)
        (_rocq_assumption_16 := Uint_pair)
        (_rocq_assumption_17 := Uuint_function)
        (_rocq_assumption_18 := Ub32)
        (_rocq_assumption_19 := Uextend)
        (_rocq_assumption_20 := Umemory_size)).
  Proof.
    unfold MonadVM.Vm.Make.Executor.call.
    eapply bounded_bind_decrease_after.
    - apply map_nonincreasing. apply pop_nonincreasing.
    - intro gas.
      eapply bounded_bind_decrease_after.
      + apply map_nonincreasing. apply pop_nonincreasing.
      + intro recipient.
        eapply bounded_bind_decrease_after.
        * apply pop3_nonincreasing.
        * intros [[value input_start] input_size].
          eapply bounded_bind_decrease_after.
          -- apply pop2_nonincreasing.
          -- intros [output_start output_size].
             apply call_opcode_impl_bounded_decreasing.
  Qed.

  Lemma callcode_opcode_wrapper_bounded_decreasing :
    gas_bounded_decreasing
      (MonadVM.Vm.Make.Executor.callcode
        (_rocq_assumption_0 := Uint32)
        (_rocq_assumption_1 := Uevmc64)
        (_rocq_assumption_2 := Uuint)
        (_rocq_assumption_3 := Urepr)
        (_rocq_assumption_4 := U256)
        (_rocq_assumption_5 := Uinteger)
        (_rocq_assumption_6 := Ugas)
        (_rocq_assumption_7 := Udelegation)
        (_rocq_assumption_8 := Uaddress)
        (_rocq_assumption_9 := Ubytes)
        (_rocq_assumption_10 := Uunit)
        (_rocq_assumption_11 := Ustring)
        (_rocq_assumption_12 := Ubytes_list)
        (_rocq_assumption_13 := Uint_list)
        (_rocq_assumption_14 := Uint)
        (_rocq_assumption_15 := Uascii)
        (_rocq_assumption_16 := Uint_pair)
        (_rocq_assumption_17 := Uuint_function)
        (_rocq_assumption_18 := Ub32)
        (_rocq_assumption_19 := Uextend)
        (_rocq_assumption_20 := Umemory_size)).
  Proof.
    unfold MonadVM.Vm.Make.Executor.callcode.
    eapply bounded_bind_decrease_after.
    - apply map_nonincreasing. apply pop_nonincreasing.
    - intro gas.
      eapply bounded_bind_decrease_after.
      + apply map_nonincreasing. apply pop_nonincreasing.
      + intro code_address.
        eapply bounded_bind_decrease_after.
        * apply pop3_nonincreasing.
        * intros [[value input_start] input_size].
          eapply bounded_bind_decrease_after.
          -- apply pop2_nonincreasing.
          -- intros [output_start output_size].
             apply call_opcode_impl_bounded_decreasing.
  Qed.

  Lemma delegatecall_opcode_wrapper_bounded_decreasing :
    gas_bounded_decreasing
      (MonadVM.Vm.Make.Executor.delegatecall
        (_rocq_assumption_0 := Uint32)
        (_rocq_assumption_1 := Uevmc64)
        (_rocq_assumption_2 := Uuint)
        (_rocq_assumption_3 := Urepr)
        (_rocq_assumption_4 := U256)
        (_rocq_assumption_5 := Uinteger)
        (_rocq_assumption_6 := Ugas)
        (_rocq_assumption_7 := Udelegation)
        (_rocq_assumption_8 := Uaddress)
        (_rocq_assumption_9 := Ubytes)
        (_rocq_assumption_10 := Uunit)
        (_rocq_assumption_11 := Ustring)
        (_rocq_assumption_12 := Ubytes_list)
        (_rocq_assumption_13 := Uint_list)
        (_rocq_assumption_14 := Uint)
        (_rocq_assumption_15 := Uascii)
        (_rocq_assumption_16 := Uint_pair)
        (_rocq_assumption_17 := Uuint_function)
        (_rocq_assumption_18 := Ub32)
        (_rocq_assumption_19 := Uextend)
        (_rocq_assumption_20 := Umemory_size)).
  Proof.
    unfold MonadVM.Vm.Make.Executor.delegatecall.
    eapply bounded_bind_decrease_after.
    - apply map_nonincreasing. apply pop_nonincreasing.
    - intro gas.
      eapply bounded_bind_decrease_after.
      + apply map_nonincreasing. apply pop_nonincreasing.
      + intro code_address.
        eapply bounded_bind_decrease_after.
        * apply pop3_nonincreasing.
        * intros [[input_start input_size] output_start].
          eapply bounded_bind_decrease_after.
          -- apply pop_nonincreasing.
          -- intro output_size.
             apply call_opcode_impl_bounded_decreasing.
  Qed.

  Lemma staticcall_opcode_wrapper_bounded_decreasing :
    gas_bounded_decreasing
      (MonadVM.Vm.Make.Executor.staticcall
        (_rocq_assumption_0 := Uint32)
        (_rocq_assumption_1 := Uevmc64)
        (_rocq_assumption_2 := Uuint)
        (_rocq_assumption_3 := Urepr)
        (_rocq_assumption_4 := U256)
        (_rocq_assumption_5 := Uinteger)
        (_rocq_assumption_6 := Ugas)
        (_rocq_assumption_7 := Udelegation)
        (_rocq_assumption_8 := Uaddress)
        (_rocq_assumption_9 := Ubytes)
        (_rocq_assumption_10 := Uunit)
        (_rocq_assumption_11 := Ustring)
        (_rocq_assumption_12 := Ubytes_list)
        (_rocq_assumption_13 := Uint_list)
        (_rocq_assumption_14 := Uint)
        (_rocq_assumption_15 := Uascii)
        (_rocq_assumption_16 := Uint_pair)
        (_rocq_assumption_17 := Uuint_function)
        (_rocq_assumption_18 := Ub32)
        (_rocq_assumption_19 := Uextend)
        (_rocq_assumption_20 := Umemory_size)).
  Proof.
    unfold MonadVM.Vm.Make.Executor.staticcall.
    eapply bounded_bind_decrease_after.
    - apply map_nonincreasing. apply pop_nonincreasing.
    - intro gas.
      eapply bounded_bind_decrease_after.
      + apply map_nonincreasing. apply pop_nonincreasing.
      + intro recipient.
        eapply bounded_bind_decrease_after.
        * apply pop3_nonincreasing.
        * intros [[input_start input_size] output_start].
          eapply bounded_bind_decrease_after.
          -- apply pop_nonincreasing.
          -- intro output_size.
             apply call_opcode_impl_bounded_decreasing.
  Qed.
End CallFamily.
