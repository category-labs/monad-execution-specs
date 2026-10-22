(** Gas preservation in the generated CREATE handler's delegation prelude. *)

From Stdlib Require Import ZArith NArith Lia.
Require Import RocqOfOCaml.RocqOfOCaml.
Require MonadVM.Byte_string.
Require MonadVM.Chain.Ethereum.
Require MonadVM.Delegation.
Require MonadVM.Evmc.
Require MonadVM.Gas.
Require MonadVM.Numeric.
Require MonadVM.Support.UintN.
Require MonadVM.Uint64.
Require MonadVM.Vm.
Require Import MonadExecutionSpecs.Termination.VmCallGas.
Require Import MonadExecutionSpecs.Termination.VmCreateGasMerge.
Require Import MonadExecutionSpecs.Termination.VmHostGasBound.
Require Import MonadExecutionSpecs.Termination.VmOpcodeProgress.
Require Import MonadExecutionSpecs.Termination.VmUnsignedGas.

Local Open Scope N_scope.

Section CreateHandlerPrelude.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
  Context `{Udelegation :
    RocqOfOCaml.Basics.Unreachable MonadVM.Delegation.Address.t}.
  Context `{Ubytes :
    RocqOfOCaml.Basics.Unreachable MonadVM.Byte_string.Bytes.t}.
  Context `{Uint : RocqOfOCaml.Basics.Unreachable int}.

  Let State := @MonadVM.Vm.Make.MachineState.t Host_t F.

  Definition gas_bounded_nonincreasing {A : Set}
      (action : @MonadVM.Vm.Make.M.t Host_t F A) : Prop :=
    forall state value next,
      (Z.of_N state.(MonadVM.Vm.Make.MachineState.t.gas) < 2 ^ 63)%Z ->
      action state = (inl value, next) ->
      next.(MonadVM.Vm.Make.MachineState.t.gas) <=
        state.(MonadVM.Vm.Make.MachineState.t.gas).

  Definition gas_bounded_decreasing {A : Set}
      (action : @MonadVM.Vm.Make.M.t Host_t F A) : Prop :=
    forall state value next,
      (Z.of_N state.(MonadVM.Vm.Make.MachineState.t.gas) < 2 ^ 63)%Z ->
      action state = (inl value, next) ->
      next.(MonadVM.Vm.Make.MachineState.t.gas) <
        state.(MonadVM.Vm.Make.MachineState.t.gas).

  Lemma bounded_bind_nonincreasing {A B : Set}
      (first : @MonadVM.Vm.Make.M.t Host_t F A)
      (second : A -> @MonadVM.Vm.Make.M.t Host_t F B) :
    gas_nonincreasing first ->
    (forall value, gas_bounded_nonincreasing (second value)) ->
    gas_bounded_nonincreasing
      (MonadVM.Vm.Make.M.op_letdollar first second).
  Proof.
    intros Hfirst Hsecond state value next Hbound Hsuccess.
    destruct (bind_success_decompose _ _ _ _ _ Hsuccess)
      as [middle [intermediate [Hleft Hright]]].
    pose proof (Hfirst state intermediate middle Hleft) as Hprefix.
    pose proof (Hsecond intermediate middle value next) as Hsuffix.
    unfold gas_bounded_nonincreasing in Hsuffix.
    specialize (Hsuffix ltac:(lia) Hright).
    lia.
  Qed.

  Lemma bounded_bind_nonincreasing_after {A B : Set}
      (first : @MonadVM.Vm.Make.M.t Host_t F A)
      (second : A -> @MonadVM.Vm.Make.M.t Host_t F B) :
    gas_bounded_nonincreasing first ->
    (forall value, gas_nonincreasing (second value)) ->
    gas_bounded_nonincreasing
      (MonadVM.Vm.Make.M.op_letdollar first second).
  Proof.
    intros Hfirst Hsecond state value next Hbound Hsuccess.
    destruct (bind_success_decompose _ _ _ _ _ Hsuccess)
      as [middle [intermediate [Hleft Hright]]].
    pose proof (Hfirst state intermediate middle Hbound Hleft) as Hprefix.
    pose proof (Hsecond intermediate middle value next Hright) as Hsuffix.
    lia.
  Qed.

  Lemma bounded_bind_decrease_after {A B : Set}
      (first : @MonadVM.Vm.Make.M.t Host_t F A)
      (second : A -> @MonadVM.Vm.Make.M.t Host_t F B) :
    gas_nonincreasing first ->
    (forall value, gas_bounded_decreasing (second value)) ->
    gas_bounded_decreasing
      (MonadVM.Vm.Make.M.op_letdollar first second).
  Proof.
    intros Hfirst Hsecond state value next Hbound Hsuccess.
    destruct (bind_success_decompose _ _ _ _ _ Hsuccess)
      as [middle [intermediate [Hleft Hright]]].
    pose proof (Hfirst state intermediate middle Hleft) as Hprefix.
    pose proof (Hsecond intermediate middle value next) as Hsuffix.
    specialize (Hsuffix ltac:(lia) Hright).
    lia.
  Qed.

  Lemma bounded_spend_then_decreases {A : Set}
      (amount : N)
      (continuation : unit -> @MonadVM.Vm.Make.M.t Host_t F A) :
    0 < amount ->
    (forall value, gas_bounded_nonincreasing (continuation value)) ->
    gas_bounded_decreasing
      (MonadVM.Vm.Make.M.op_letdollar
        (MonadVM.Vm.Make.spend amount) continuation).
  Proof.
    intros Hpositive Hcontinuation state value next Hbound Hsuccess.
    destruct (bind_success_decompose _ _ _ _ _ Hsuccess)
      as [charged [charged_value [Hspend Hrest]]].
    destruct charged_value.
    pose proof (spend_success_decreases amount state charged
      Hpositive Hspend) as Hcharged.
    pose proof (Hcontinuation tt charged value next) as Hnext.
    specialize (Hnext ltac:(lia) Hrest).
    lia.
  Qed.

  Lemma access_delegation_nonincreasing
      (address : MonadVM.Vm.Make.Address.t) :
    gas_nonincreasing
      (MonadVM.Vm.Make.Executor.access_delegation
        (_rocq_assumption_0 := Ugas)
        (_rocq_assumption_1 := Udelegation)
        (_rocq_assumption_2 := Ubytes)
        (_rocq_assumption_3 := Uint) address).
  Proof.
    unfold MonadVM.Vm.Make.Executor.access_delegation.
    eapply bind_nonincreasing.
    - unfold MonadVM.Vm.Make.M.HostAPI.copy_code.
      apply host_lift_nonincreasing.
    - intro code.
      match goal with
      | |- gas_nonincreasing (match ?option with _ => _ end) =>
          destruct option as [code_address|]
      end.
      + eapply bind_nonincreasing.
        * apply map_nonincreasing.
          unfold MonadVM.Vm.Make.M.HostAPI.access_account.
          apply host_lift_nonincreasing.
        * intro access_gas. apply return_nonincreasing.
      + apply return_nonincreasing.
  Qed.

  Lemma create_delegation_guard_nonincreasing
      (address : MonadVM.Vm.Make.Address.t) :
    gas_nonincreasing
      (MonadVM.Vm.Make.M.op_letdollar
        (MonadVM.Vm.Make.Executor.access_delegation
          (_rocq_assumption_0 := Ugas)
          (_rocq_assumption_1 := Udelegation)
          (_rocq_assumption_2 := Ubytes)
          (_rocq_assumption_3 := Uint) address)
        (fun delegation =>
          match delegation with
          | MonadVM.Vm.Make.Executor.Delegated _ =>
              MonadVM.Vm.Make.M.fail
                MonadVM.Evmc.Result.StatusCode.Create_from_delegated_eoa
          | MonadVM.Vm.Make.Executor.Direct _ =>
              MonadVM.Vm.Make.M._return tt
          end)).
  Proof.
    eapply bind_nonincreasing.
    - apply access_delegation_nonincreasing.
    - intros [delegated | direct].
      + apply fail_nonincreasing.
      + apply return_nonincreasing.
  Qed.

  Lemma create_forwarded_read_exact
      (state next : State) (forwarded : MonadVM.Support.UintN.t) :
    MonadVM.Vm.Make.M.op_ltdollargt MonadVM.Gas.minus_1_64th
      (MonadVM.Vm.Make.M.op_exclamation
        MonadVM.Vm.Make.MachineState.gas)
      state = (inl forwarded, next) ->
    forwarded = MonadVM.Gas.minus_1_64th
      state.(MonadVM.Vm.Make.MachineState.t.gas) /\
    next = state.
  Proof.
    intro Hread.
    cbn in Hread.
    inversion Hread; subst.
    split; reflexivity.
  Qed.

  Definition buffer_push_action
      (buffer : MonadVM.Byte_string.Bytes.t)
      (pushed : MonadVM.Numeric.U256.t) :
      @MonadVM.Vm.Make.M.t Host_t F unit :=
    MonadVM.Vm.Make.M.op_letdollar
      (MonadVM.Vm.Make.M.op_coloneq
        MonadVM.Vm.Make.MachineState.output_buffer buffer)
      (fun _ => MonadVM.Vm.Make.push pushed).

  Lemma buffer_push_preserves_gas
      (buffer : MonadVM.Byte_string.Bytes.t)
      (pushed : MonadVM.Numeric.U256.t)
      (state next : State) :
    buffer_push_action buffer pushed state = (inl tt, next) ->
    next.(MonadVM.Vm.Make.MachineState.t.gas) =
      state.(MonadVM.Vm.Make.MachineState.t.gas).
  Proof.
    intro Hsuccess.
    unfold buffer_push_action in Hsuccess.
    destruct (bind_success_decompose _ _ _ _ _ Hsuccess)
      as [after_buffer [cleared [Hbuffer Hpush]]].
    pose proof (f_equal snd Hbuffer) as Hbuffer_state.
    cbn in Hbuffer_state.
    pose proof (push_preserves_gas pushed after_buffer) as Hpush_gas.
    rewrite Hpush in Hpush_gas.
    cbn in Hpush_gas.
    subst after_buffer.
    cbn in Hpush_gas.
    exact Hpush_gas.
  Qed.

  Lemma create_result_preserves_gas
      (success : bool)
      (output : MonadVM.Byte_string.Bytes.t)
      (address_value zero : MonadVM.Numeric.U256.t)
      (state next : State) :
    (if success then
      buffer_push_action MonadVM.Byte_string.Bytes.empty address_value
    else buffer_push_action output zero) state = (inl tt, next) ->
    next.(MonadVM.Vm.Make.MachineState.t.gas) =
      state.(MonadVM.Vm.Make.MachineState.t.gas).
  Proof.
    destruct success; apply buffer_push_preserves_gas.
  Qed.

  Lemma create_host_result_nonincreasing
      `{Uuint :
        RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}
      `{Uinteger :
        RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.Integer.t}
      `{Uunit : RocqOfOCaml.Basics.Unreachable unit}
      `{U64 : RocqOfOCaml.Basics.Unreachable int64}
      (msg : MonadVM.Evmc.Message.t)
      (available forwarded_state middle merged next : State)
      (result : MonadVM.Evmc.Result.t)
      (success : bool)
      (output : MonadVM.Byte_string.Bytes.t)
      (address_value zero : MonadVM.Numeric.U256.t) :
    (Z.of_N available.(MonadVM.Vm.Make.MachineState.t.gas) <
      2 ^ 64)%Z ->
    MonadVM.Vm.Make.M.update_field
      MonadVM.Vm.Make.MachineState.gas
      (fun gas => MonadVM.Support.UintN.op_minus gas
        (MonadVM.Gas.minus_1_64th
          available.(MonadVM.Vm.Make.MachineState.t.gas)))
      available = (inl tt, forwarded_state) ->
    MonadVM.Vm.Make.M.HostAPI.call msg forwarded_state =
      (inl result, middle) ->
    MonadVM.Vm.Make.Executor.merge_child_gas_and_refund
      result.(MonadVM.Evmc.Result.t.status_code)
      result.(MonadVM.Evmc.Result.t.gas_left)
      result.(MonadVM.Evmc.Result.t.gas_refund)
      middle = (inl tt, merged) ->
    msg.(MonadVM.Evmc.Message.t.gas) =
      MonadVM.Support.UintN.to_uint64
        (MonadVM.Gas.minus_1_64th
          available.(MonadVM.Vm.Make.MachineState.t.gas)) ->
    (if success then
      buffer_push_action MonadVM.Byte_string.Bytes.empty address_value
    else buffer_push_action output zero) merged = (inl tt, next) ->
    next.(MonadVM.Vm.Make.MachineState.t.gas) <=
      available.(MonadVM.Vm.Make.MachineState.t.gas).
  Proof.
    intros Hbound Hsubtract Hcall Hmerge Hmessage Hfinish.
    pose proof (create_host_merge_nonincreasing msg available
      forwarded_state middle merged result Hbound Hsubtract Hcall
      Hmerge Hmessage) as Hmerged.
    pose proof (create_result_preserves_gas success output
      address_value zero merged next Hfinish) as Hresult.
    lia.
  Qed.

  Context `{Uuint :
    RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}.
  Context `{Uinteger :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.Integer.t}.
  Context `{Uunit : RocqOfOCaml.Basics.Unreachable unit}.
  Context `{U64 : RocqOfOCaml.Basics.Unreachable int64}.

  Definition create_host_path
      (message_of : MonadVM.Support.UintN.t ->
        @MonadVM.Vm.Make.Memory.t Host_t F -> MonadVM.Evmc.Message.t)
      (finish : MonadVM.Evmc.Result.t ->
        @MonadVM.Vm.Make.M.t Host_t F unit) :
      @MonadVM.Vm.Make.M.t Host_t F unit :=
    MonadVM.Vm.Make.M.op_letdollar
      (MonadVM.Vm.Make.M.op_ltdollargt MonadVM.Gas.minus_1_64th
        (MonadVM.Vm.Make.M.op_exclamation
          MonadVM.Vm.Make.MachineState.gas))
      (fun forwarded =>
        MonadVM.Vm.Make.M.op_letdollar
          (MonadVM.Vm.Make.M.update_field
            MonadVM.Vm.Make.MachineState.gas
            (fun gas => MonadVM.Support.UintN.op_minus gas forwarded))
          (fun _ =>
            MonadVM.Vm.Make.M.op_letdollar
              (MonadVM.Vm.Make.M.op_exclamation
                MonadVM.Vm.Make.MachineState.memory)
              (fun memory =>
                MonadVM.Vm.Make.M.op_letdollar
                  (MonadVM.Vm.Make.M.HostAPI.call
                    (message_of forwarded memory))
                  (fun result =>
                    MonadVM.Vm.Make.M.op_letdollar
                      (MonadVM.Vm.Make.Executor.merge_child_gas_and_refund
                        result.(MonadVM.Evmc.Result.t.status_code)
                        result.(MonadVM.Evmc.Result.t.gas_left)
                        result.(MonadVM.Evmc.Result.t.gas_refund))
                      (fun _ => finish result))))).

  Lemma create_host_path_nonincreasing
      (message_of : MonadVM.Support.UintN.t ->
        @MonadVM.Vm.Make.Memory.t Host_t F -> MonadVM.Evmc.Message.t)
      (finish : MonadVM.Evmc.Result.t ->
        @MonadVM.Vm.Make.M.t Host_t F unit)
      (state next : State) :
    (Z.of_N state.(MonadVM.Vm.Make.MachineState.t.gas) < 2 ^ 64)%Z ->
    (forall forwarded memory,
      (message_of forwarded memory).(MonadVM.Evmc.Message.t.gas) =
        MonadVM.Support.UintN.to_uint64 forwarded) ->
    (forall result middle final,
      finish result middle = (inl tt, final) ->
      final.(MonadVM.Vm.Make.MachineState.t.gas) =
        middle.(MonadVM.Vm.Make.MachineState.t.gas)) ->
    create_host_path message_of finish state = (inl tt, next) ->
    next.(MonadVM.Vm.Make.MachineState.t.gas) <=
      state.(MonadVM.Vm.Make.MachineState.t.gas).
  Proof.
    intros Hbound Hmessage Hfinish Hrun.
    unfold create_host_path in Hrun.
    destruct (bind_success_decompose _ _ _ _ _ Hrun)
      as [read_state [forwarded [Hread Hafter_read]]].
    destruct (create_forwarded_read_exact _ _ _ Hread)
      as [Hforwarded Hread_state].
    subst forwarded read_state.
    destruct (bind_success_decompose _ _ _ _ _ Hafter_read)
      as [forwarded_state [updated [Hsubtract Hafter_subtract]]].
    destruct updated.
    destruct (bind_success_decompose _ _ _ _ _ Hafter_subtract)
      as [memory_state [memory [Hmemory Hafter_memory]]].
    pose proof (f_equal snd Hmemory) as Hmemory_state.
    cbn in Hmemory_state.
    subst memory_state.
    destruct (bind_success_decompose _ _ _ _ _ Hafter_memory)
      as [middle [result [Hcall Hafter_call]]].
    destruct (bind_success_decompose _ _ _ _ _ Hafter_call)
      as [merged [merged_value [Hmerge Hresult]]].
    destruct merged_value.
    pose proof (create_host_merge_nonincreasing
      (message_of
        (MonadVM.Gas.minus_1_64th
          state.(MonadVM.Vm.Make.MachineState.t.gas)) memory)
      state forwarded_state middle merged result Hbound Hsubtract Hcall
      Hmerge (Hmessage _ _)) as Hmerged.
    pose proof (Hfinish result merged next Hresult) as Hfinal.
    lia.
  Qed.

  Context `{Uint32 :
    RocqOfOCaml.Basics.Unreachable RocqOfOCaml.OCamlInt32.t}.
  Context `{Uevmc64 : RocqOfOCaml.Basics.Unreachable MonadVM.Uint64.t}.
  Context `{U256 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
  Context `{Uaddress :
    RocqOfOCaml.Basics.Unreachable MonadVM.Chain.Ethereum.Address.t}.
  Context `{Ustring : RocqOfOCaml.Basics.Unreachable string}.
  Context `{Ubytes_list :
    RocqOfOCaml.Basics.Unreachable
      (list MonadVM.Byte_string.Bytes.t)}.
  Context `{Uascii : RocqOfOCaml.Basics.Unreachable ascii}.
  Context `{Ub32 :
    RocqOfOCaml.Basics.Unreachable
      MonadVM.Byte_string.B32.(MonadVM.Byte_string.Fixed.Fixed_result.t)}.
  Context `{Umemory_size :
    RocqOfOCaml.Basics.Unreachable
      (@MonadVM.Vm.Make.Memory.t Host_t F -> MonadVM.Support.UintN.t)}.

  Lemma generic_create_impl_nonincreasing
      (kind : MonadVM.Evmc.Message.CallKind.t)
      (create2_salt : string)
      (endowment input_start input_size : MonadVM.Numeric.U256.t) :
    gas_bounded_nonincreasing
      (MonadVM.Vm.Make.Executor.generic_create_impl
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
        (_rocq_assumption_12 := Uint)
        (_rocq_assumption_13 := Uascii)
        (_rocq_assumption_14 := Ub32)
        (_rocq_assumption_15 := Umemory_size)
        kind create2_salt endowment input_start input_size).
  Proof.
    unfold MonadVM.Vm.Make.Executor.generic_create_impl.
    eapply bounded_bind_nonincreasing.
    - apply stipend_guard_nonincreasing.
    - intros []. eapply bounded_bind_nonincreasing.
      + apply check_write_permissions_nonincreasing.
      + intros []. eapply bounded_bind_nonincreasing.
        * apply get_balance_nonincreasing.
        * intro self_balance. eapply bounded_bind_nonincreasing.
          { apply create_delegation_guard_nonincreasing. }
          intros [].
          match goal with
          | |- gas_bounded_nonincreasing (if ?skip then _ else _) =>
              destruct skip eqn:Hskip
          end.
          { intros state [] next Hbound Hrun.
            pose proof (buffer_push_preserves_gas _ _ _ _ Hrun).
            lia. }
          intros state [] next Hbound Hrun.
          destruct (bind_success_decompose _ _ _ _ _ Hrun)
            as [read_state [forwarded [Hread Hafter_read]]].
          destruct (create_forwarded_read_exact _ _ _ Hread)
            as [Hforwarded Hread_state].
          subst forwarded read_state.
          destruct (bind_success_decompose _ _ _ _ _ Hafter_read)
            as [forwarded_state [updated [Hsubtract Hafter_subtract]]].
          destruct updated.
          destruct (bind_success_decompose _ _ _ _ _ Hafter_subtract)
            as [memory_state [memory [Hmemory Hafter_memory]]].
          pose proof (f_equal snd Hmemory) as Hmemory_state.
          cbn in Hmemory_state.
          subst memory_state.
          destruct (bind_success_decompose _ _ _ _ _ Hafter_memory)
            as [middle [result [Hcall Hafter_call]]].
          destruct result as [status gas_left gas_refund output address].
          destruct (bind_success_decompose _ _ _ _ _ Hafter_call)
            as [merged [merged_value [Hmerge Hresult]]].
          destruct merged_value.
          assert (Hmessage :
            (Z.of_N state.(MonadVM.Vm.Make.MachineState.t.gas) <
              2 ^ 64)%Z) by lia.
          pose proof (create_host_merge_nonincreasing (U64 := Uint)
            _ state
            forwarded_state middle merged
            {| MonadVM.Evmc.Result.t.status_code := status;
               MonadVM.Evmc.Result.t.gas_left := gas_left;
               MonadVM.Evmc.Result.t.gas_refund := gas_refund;
               MonadVM.Evmc.Result.t.output_data := output;
               MonadVM.Evmc.Result.t.create_address := address |}
            Hmessage Hsubtract Hcall Hmerge
            ltac:(cbn;
              apply (create_message_signed_unsigned_equal
                (UGas := Uuint));
              exact Hbound)) as Hmerged.
          destruct status; cbn in Hresult;
            pose proof (buffer_push_preserves_gas _ _ _ _ Hresult)
              as Hfinal; lia.
  Qed.

  Context `{Uuint_function :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Support.UintN.t -> MonadVM.Support.UintN.t)}.
  Context `{Uextend :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Numeric.U256.t -> MonadVM.Numeric.U256.t ->
        @MonadVM.Vm.Make.Memory.t Host_t F ->
        @MonadVM.Vm.Make.M.Option.t Host_t F
          (@MonadVM.Vm.Make.Memory.t Host_t F))}.

  Lemma create_opcode_bounded_decreasing :
    gas_bounded_decreasing
      (MonadVM.Vm.Make.Executor.create
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
        (_rocq_assumption_12 := Uint)
        (_rocq_assumption_13 := Uascii)
        (_rocq_assumption_14 := Uuint_function)
        (_rocq_assumption_15 := Ub32)
        (_rocq_assumption_16 := Uextend)
        (_rocq_assumption_17 := Umemory_size)).
  Proof.
    unfold MonadVM.Vm.Make.Executor.create.
    eapply bounded_bind_decrease_after.
    - apply pop3_nonincreasing.
    - intros [[endowment input_start] input_size_bytes].
      eapply bounded_bind_decrease_after.
      + apply extend_memory_to_nonincreasing.
      + intro memory_extension_gas.
        eapply bounded_spend_then_decreases.
        * rewrite create_cost_value.
          unfold MonadVM.Gas.op_plus, MonadVM.Support.UintN.op_plus,
            MonadVM.Gas.op_star, MonadVM.Support.UintN.op_star.
          lia.
        * intros [].
          eapply bounded_bind_nonincreasing_after.
          { apply generic_create_impl_nonincreasing. }
          intros []. apply increase_pc_nonincreasing.
  Qed.

  Context `{Urepr :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.Repr.t}.
  Context `{Uint_pair :
    RocqOfOCaml.Basics.Unreachable (int * int)}.

  Lemma create2_opcode_bounded_decreasing :
    gas_bounded_decreasing
      (MonadVM.Vm.Make.Executor.create2
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
        (_rocq_assumption_13 := Uint)
        (_rocq_assumption_14 := Uascii)
        (_rocq_assumption_15 := Uint_pair)
        (_rocq_assumption_16 := Uuint_function)
        (_rocq_assumption_17 := Ub32)
        (_rocq_assumption_18 := Uextend)
        (_rocq_assumption_19 := Umemory_size)).
  Proof.
    unfold MonadVM.Vm.Make.Executor.create2.
    eapply bounded_bind_decrease_after.
    - apply pop3_nonincreasing.
    - intros [[endowment input_start] input_size_bytes].
      eapply bounded_bind_decrease_after.
      + apply map_nonincreasing. apply pop_nonincreasing.
      + intro create2_salt.
        eapply bounded_bind_decrease_after.
        * apply extend_memory_to_nonincreasing.
        * intro memory_extension_gas.
          eapply bounded_spend_then_decreases.
          { rewrite create_cost_value.
            unfold MonadVM.Gas.op_plus, MonadVM.Support.UintN.op_plus,
              MonadVM.Gas.op_star, MonadVM.Support.UintN.op_star.
            lia. }
          intros [].
          eapply bounded_bind_nonincreasing_after.
          { apply generic_create_impl_nonincreasing. }
          intros []. apply increase_pc_nonincreasing.
  Qed.
End CreateHandlerPrelude.
