(** Bridge generated opcode handlers to the generated dispatcher. *)

From Stdlib Require Import NArith Lia.
Require Import RocqOfOCaml.RocqOfOCaml.
Require MonadVM.Evmc.
Require MonadVM.Gas.
Require MonadVM.Numeric.
Require MonadVM.Opcode.
Require MonadVM.Support.UintN.
Require MonadVM.Support.Variants.
Require MonadVM.Vm.
Require Import MonadExecutionSpecs.Termination.VmCallHandlerProgress.
Require Import MonadExecutionSpecs.Termination.VmCreateHandlerProgress.
Require Import MonadExecutionSpecs.Termination.VmHostGasBound.
Require Import MonadExecutionSpecs.Termination.VmOpcodeProgress.
Require Import MonadExecutionSpecs.Termination.VmExternalCodeCopyProgress.
Require Import MonadExecutionSpecs.Refinement.VmNativeRunBridge.
Require Import MonadExecutionSpecs.Refinement.VmPcConversion.
Require Import MonadExecutionSpecs.Refinement.VmPcIncrement.

Local Open Scope N_scope.

Section Dispatch.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{U0 : RocqOfOCaml.Basics.Unreachable Z.t}.
  Context `{U1 :
    RocqOfOCaml.Basics.Unreachable (RocqOfOCaml.OCamlSeq.t int)}.
  Context `{U2 : RocqOfOCaml.Basics.Unreachable RocqOfOCaml.OCamlInt32.t}.
  Context `{U3 : RocqOfOCaml.Basics.Unreachable MonadVM.Uint64.t}.
  Context `{U4 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}.
  Context `{U5 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.Repr.t}.
  Context `{U6 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
  Context `{U7 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.Integer.t}.
  Context `{U8 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.I256.t}.
  Context `{U9 : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
  Context `{U10 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Delegation.Address.t}.
  Context `{U11 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Chain.Ethereum.Address.t}.
  Context `{U12 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Byte_string.Bytes.t}.
  Context `{U13 :
    RocqOfOCaml.Basics.Unreachable
      (@MonadVM.Vm.Make.M.Option.t Host_t F MonadVM.Numeric.U256.t)}.
  Context `{U15 : RocqOfOCaml.Basics.Unreachable unit}.
  Context `{U16 : RocqOfOCaml.Basics.Unreachable string}.
  Context `{U17 :
    RocqOfOCaml.Basics.Unreachable (option MonadVM.Numeric.U256.t)}.
  Context `{U18 : RocqOfOCaml.Basics.Unreachable (option string)}.
  Context `{U19 :
    RocqOfOCaml.Basics.Unreachable
      (list MonadVM.Byte_string.Bytes.t)}.
  Context `{U20 : RocqOfOCaml.Basics.Unreachable (list int)}.
  Context `{U21 : RocqOfOCaml.Basics.Unreachable int}.
  Context `{U22 : RocqOfOCaml.Basics.Unreachable ascii}.
  Context `{U23 : RocqOfOCaml.Basics.Unreachable (int * int)}.
  Context `{U24 :
    RocqOfOCaml.Basics.Unreachable
      (Z.t -> MonadVM.Numeric.U256.t)}.
  Context `{U25 :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Support.UintN.t -> MonadVM.Support.UintN.t)}.
  Context `{U26 :
    RocqOfOCaml.Basics.Unreachable
      (unit -> RocqOfOCaml.OCamlSeq.node int)}.
  Context `{U27 :
    RocqOfOCaml.Basics.Unreachable
      (@MonadVM.Vm.Make.opcode_impl Host_t F)}.
  Context `{U28 :
    RocqOfOCaml.Basics.Unreachable
      MonadVM.Numeric.IntegerBase.(MonadVM.Numeric.Make.Make_result.t)}.
  Context `{U29 :
    RocqOfOCaml.Basics.Unreachable
      MonadVM.Numeric.Bits256.(
        MonadVM.Numeric.TwosComplement.TwosComplement_result.U).(
          MonadVM.Numeric.Make.Make_result.t)}.
  Context `{U30 :
    RocqOfOCaml.Basics.Unreachable
      MonadVM.Numeric.Bits256.(
        MonadVM.Numeric.TwosComplement.TwosComplement_result.Signed_t)}.
  Context `{U31 :
    RocqOfOCaml.Basics.Unreachable
      MonadVM.Byte_string.B32.(MonadVM.Byte_string.Fixed.Fixed_result.t)}.
  Context `{U32 :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Numeric.U256.t -> MonadVM.Numeric.U256.t ->
        @MonadVM.Vm.Make.Memory.t Host_t F ->
        @MonadVM.Vm.Make.M.Option.t Host_t F
          (@MonadVM.Vm.Make.Memory.t Host_t F))}.
  Context `{U33 :
    RocqOfOCaml.Basics.Unreachable
      (@MonadVM.Vm.Make.Memory.t Host_t F ->
        MonadVM.Support.UintN.t)}.

  Let State := @MonadVM.Vm.Make.MachineState.t Host_t F.

  Definition dispatch (opcode : MonadVM.Opcode.t) :
      @MonadVM.Vm.Make.opcode_impl Host_t F :=
    @MonadVM.Vm.Make.Executor.execute_opcode Host_t F E
      U0 U1 U2 U3 U4 U5 U6 U7 U8 U9 U10 U11 U12 U13 U15 U16
      U17 U18 U19 U20 U21 U22 U23 U24 U25 U26 U27 U28 U29 U30 U31
      U32 U33 opcode.

  Definition continuing_progress (opcode : MonadVM.Opcode.t) : Prop :=
    forall (state next : State),
      (Z.of_N state.(MonadVM.Vm.Make.MachineState.t.gas) < 2 ^ 63)%Z ->
      dispatch opcode state =
        ((inl true : sum bool MonadVM.Evmc.Result.StatusCode.t), next) ->
      next.(MonadVM.Vm.Make.MachineState.t.gas) <
        state.(MonadVM.Vm.Make.MachineState.t.gas).

  Definition no_continuing
      (action : @MonadVM.Vm.Make.M.t Host_t F bool) : Prop :=
    forall (state next : State),
      action state =
        ((inl true : sum bool MonadVM.Evmc.Result.StatusCode.t), next) ->
      False.

  Lemma bind_no_continuing {A : Set}
      (first : @MonadVM.Vm.Make.M.t Host_t F A)
      (second : A -> @MonadVM.Vm.Make.M.t Host_t F bool) :
    (forall value, no_continuing (second value)) ->
    no_continuing
      (@MonadVM.Vm.Make.M.op_letdollar Host_t F A bool first second).
  Proof.
    intros Hsecond state next Hsuccess.
    destruct (bind_success_decompose first second state true next Hsuccess)
      as [middle [value [_ Hright]]].
    exact (Hsecond value middle next Hright).
  Qed.

  Lemma return_false_no_continuing :
    no_continuing (@MonadVM.Vm.Make.M._return Host_t F bool false).
  Proof.
    intros state next Hsuccess.
    discriminate Hsuccess.
  Qed.

  Lemma fail_no_continuing
      (error : MonadVM.Evmc.Result.StatusCode.t) :
    no_continuing (@MonadVM.Vm.Make.M.fail Host_t F bool error).
  Proof.
    intros state next Hsuccess.
    discriminate Hsuccess.
  Qed.

  Lemma finish_execution_no_continuing (return_output : bool) :
    no_continuing
      (@MonadVM.Vm.Make.finish_execution Host_t F return_output).
  Proof.
    unfold MonadVM.Vm.Make.finish_execution.
    eapply bind_no_continuing.
    intros []. apply return_false_no_continuing.
  Qed.

  Lemma no_continuing_progress (opcode : MonadVM.Opcode.t) :
    no_continuing (dispatch opcode) -> continuing_progress opcode.
  Proof.
    intros Hnone state next _ Hsuccess.
    exfalso. exact (Hnone state next Hsuccess).
  Qed.

  Lemma invalid_no_continuing :
    no_continuing (dispatch MonadVM.Opcode.Invalid).
  Proof.
    unfold dispatch.
    cbn [MonadVM.Vm.Make.Executor.execute_opcode].
    apply fail_no_continuing.
  Qed.

  Lemma invalid_exact (state : State) :
    dispatch MonadVM.Opcode.Invalid state =
      (inr MonadVM.Evmc.Result.StatusCode.Invalid_instruction, state).
  Proof.
    unfold dispatch.
    cbn [MonadVM.Vm.Make.Executor.execute_opcode].
    reflexivity.
  Qed.

  Lemma undefined_no_continuing (byte : ascii) :
    no_continuing (dispatch (MonadVM.Opcode.Undefined byte)).
  Proof.
    unfold dispatch.
    cbn [MonadVM.Vm.Make.Executor.execute_opcode].
    apply fail_no_continuing.
  Qed.

  Lemma undefined_exact (byte : ascii) (state : State) :
    dispatch (MonadVM.Opcode.Undefined byte) state =
      (inr MonadVM.Evmc.Result.StatusCode.Undefined_instruction, state).
  Proof.
    unfold dispatch.
    cbn [MonadVM.Vm.Make.Executor.execute_opcode].
    reflexivity.
  Qed.

  Lemma stop_no_continuing :
    no_continuing (dispatch MonadVM.Opcode.Stop).
  Proof.
    unfold dispatch.
    cbn [MonadVM.Vm.Make.Executor.execute_opcode].
    unfold MonadVM.Vm.Make.Executor.stop.
    eapply bind_no_continuing.
    intros []. apply finish_execution_no_continuing.
  Qed.

  Lemma stop_exact (state : State) :
    (@MonadVM.Vm.Make.Params Host_t F).(
      MonadVM.Vm.Make_Params_signature.debug_tstore) = false ->
    dispatch MonadVM.Opcode.Stop state =
      (inl false,
       MonadVM.Vm.Make.MachineState.t.with_output_buffer
         MonadVM.Byte_string.Bytes.empty state).
  Proof.
    intro Hdebug.
    unfold dispatch.
    cbn [MonadVM.Vm.Make.Executor.execute_opcode].
    unfold MonadVM.Vm.Make.Executor.stop,
      MonadVM.Vm.Make.Executor.debug_tstore_stack.
    rewrite Hdebug.
    reflexivity.
  Qed.

  Lemma jumpdest_after_spend (state after_spend : State) :
    (@MonadVM.Vm.Make.Params Host_t F).(
      MonadVM.Vm.Make_Params_signature.debug_tstore) = false ->
    @MonadVM.Vm.Make.spend Host_t F U9
      (MonadVM.Gas.jumpdest (_rocq_assumption_0 := U9)) state =
      (inl tt, after_spend) ->
    dispatch MonadVM.Opcode.Jumpdest state =
      @MonadVM.Vm.Make.increase_pc_and_continue Host_t F U6 after_spend.
  Proof.
    intros Hdebug Hspend.
    unfold dispatch.
    cbn [MonadVM.Vm.Make.Executor.execute_opcode].
    unfold MonadVM.Vm.Make.Executor.jumpdest,
      MonadVM.Vm.Make.Executor.debug_tstore_stack.
    rewrite Hdebug.
    cbn -[MonadVM.Vm.Make.spend].
    change (@MonadVM.Vm.Make.spend Host_t F U9 1 state =
      (inl tt, after_spend)) in Hspend.
    rewrite Hspend.
    reflexivity.
  Qed.

  Lemma increase_pc_exact (state : State) :
    @MonadVM.Vm.Make.increase_pc_and_continue Host_t F U6 state =
      (inl true,
       MonadVM.Vm.Make.MachineState.t.with_pc
         (MonadVM.Numeric.U256.op_plus (_rocq_assumption_0 := U6)
           (MonadVM.Numeric.U256.one (_rocq_assumption_0 := U6))
           state.(MonadVM.Vm.Make.MachineState.t.pc)) state).
  Proof. reflexivity. Qed.

  Lemma increase_pc_mod (state : State) :
    @MonadVM.Vm.Make.increase_pc_and_continue Host_t F U6 state =
      (inl true,
       MonadVM.Vm.Make.MachineState.t.with_pc
         ((state.(MonadVM.Vm.Make.MachineState.t.pc) + 1)
           mod (2 ^ 256))%Z state).
  Proof.
    rewrite increase_pc_exact.
    rewrite generated_u256_increment_mod.
    reflexivity.
  Qed.

  Lemma pc_after_spend_and_push (state spent pushed : State) :
    @MonadVM.Vm.Make.spend Host_t F U9
      (MonadVM.Gas.base (_rocq_assumption_0 := U9)) state =
      (inl tt, spent) ->
    @MonadVM.Vm.Make.push Host_t F
      spent.(MonadVM.Vm.Make.MachineState.t.pc) spent =
      (inl tt, pushed) ->
    dispatch MonadVM.Opcode.Pc state =
      @MonadVM.Vm.Make.increase_pc_and_continue Host_t F U6 pushed.
  Proof.
    intros Hspent Hpush.
    unfold dispatch.
    cbn [MonadVM.Vm.Make.Executor.execute_opcode].
    unfold MonadVM.Vm.Make.Executor.pc_,
      MonadVM.Vm.Make.Executor.fetch_environment_variable_opcode_impl'.
    cbn -[MonadVM.Vm.Make.spend MonadVM.Vm.Make.push].
    change (@MonadVM.Vm.Make.spend Host_t F U9 2 state =
      (inl tt, spent)) in Hspent.
    rewrite Hspent.
    cbn -[MonadVM.Vm.Make.push].
    rewrite Hpush.
    reflexivity.
  Qed.

  Lemma pc_out_of_gas_exact (state : State) :
    MonadVM.Gas.op_lt
      state.(MonadVM.Vm.Make.MachineState.t.gas)
      (MonadVM.Gas.base (_rocq_assumption_0 := U9)) = true ->
    dispatch MonadVM.Opcode.Pc state =
      (inr MonadVM.Evmc.Result.StatusCode.Out_of_gas, state).
  Proof.
    intro Hgas.
    unfold dispatch.
    cbn [MonadVM.Vm.Make.Executor.execute_opcode].
    unfold MonadVM.Vm.Make.Executor.pc_,
      MonadVM.Vm.Make.Executor.fetch_environment_variable_opcode_impl',
      MonadVM.Vm.Make.spend.
    change (MonadVM.Gas.op_lt
      state.(MonadVM.Vm.Make.MachineState.t.gas) 2 = true) in Hgas.
    cbn -[MonadVM.Gas.op_lt].
    rewrite Hgas.
    reflexivity.
  Qed.

  Lemma pc_stack_overflow_exact (state : State) :
    MonadVM.Gas.op_lt
      state.(MonadVM.Vm.Make.MachineState.t.gas)
      (MonadVM.Gas.base (_rocq_assumption_0 := U9)) = false ->
    Z.geb state.(MonadVM.Vm.Make.MachineState.t.stack_depth)
      MonadVM.Vm.Make.max_stack_depth = true ->
    let spent := MonadVM.Vm.Make.MachineState.t.with_gas
      (MonadVM.Gas.op_minus (_rocq_assumption_0 := U9)
        state.(MonadVM.Vm.Make.MachineState.t.gas)
        (MonadVM.Gas.base (_rocq_assumption_0 := U9))) state in
    dispatch MonadVM.Opcode.Pc state =
      (inr MonadVM.Evmc.Result.StatusCode.Stack_overflow, spent).
  Proof.
    intros Hgas Hdepth.
    unfold dispatch.
    cbn [MonadVM.Vm.Make.Executor.execute_opcode].
    unfold MonadVM.Vm.Make.Executor.pc_,
      MonadVM.Vm.Make.Executor.fetch_environment_variable_opcode_impl',
      MonadVM.Vm.Make.spend.
    change (MonadVM.Gas.op_lt
      state.(MonadVM.Vm.Make.MachineState.t.gas) 2 = false) in Hgas.
    cbn -[MonadVM.Gas.op_lt MonadVM.Vm.Make.push].
    rewrite Hgas.
    cbn -[MonadVM.Vm.Make.push].
    unfold MonadVM.Vm.Make.push.
    cbn.
    rewrite Hdepth.
    reflexivity.
  Qed.

  Lemma pc_success_exact (state : State) :
    MonadVM.Gas.op_lt
      state.(MonadVM.Vm.Make.MachineState.t.gas)
      (MonadVM.Gas.base (_rocq_assumption_0 := U9)) = false ->
    Z.geb state.(MonadVM.Vm.Make.MachineState.t.stack_depth)
      MonadVM.Vm.Make.max_stack_depth = false ->
    let spent := MonadVM.Vm.Make.MachineState.t.with_gas
      (MonadVM.Gas.op_minus (_rocq_assumption_0 := U9)
        state.(MonadVM.Vm.Make.MachineState.t.gas)
        (MonadVM.Gas.base (_rocq_assumption_0 := U9))) state in
    let pushed := MonadVM.Vm.Make.MachineState.t.with_stack_depth
      (Z.add state.(MonadVM.Vm.Make.MachineState.t.stack_depth) 1)
      (MonadVM.Vm.Make.MachineState.t.with_stack
        (state.(MonadVM.Vm.Make.MachineState.t.pc) ::
          state.(MonadVM.Vm.Make.MachineState.t.stack)) spent) in
    dispatch MonadVM.Opcode.Pc state =
      (inl true,
       MonadVM.Vm.Make.MachineState.t.with_pc
         ((state.(MonadVM.Vm.Make.MachineState.t.pc) + 1)
            mod (2 ^ 256))%Z pushed).
  Proof.
    intros Hgas Hdepth.
    rewrite (pc_after_spend_and_push state
      (MonadVM.Vm.Make.MachineState.t.with_gas
        (MonadVM.Gas.op_minus (_rocq_assumption_0 := U9)
          state.(MonadVM.Vm.Make.MachineState.t.gas)
          (MonadVM.Gas.base (_rocq_assumption_0 := U9))) state)
      (MonadVM.Vm.Make.MachineState.t.with_stack_depth
        (Z.add state.(MonadVM.Vm.Make.MachineState.t.stack_depth) 1)
        (MonadVM.Vm.Make.MachineState.t.with_stack
          (state.(MonadVM.Vm.Make.MachineState.t.pc) ::
            state.(MonadVM.Vm.Make.MachineState.t.stack))
          (MonadVM.Vm.Make.MachineState.t.with_gas
            (MonadVM.Gas.op_minus (_rocq_assumption_0 := U9)
              state.(MonadVM.Vm.Make.MachineState.t.gas)
              (MonadVM.Gas.base (_rocq_assumption_0 := U9))) state))));
      [rewrite increase_pc_mod; reflexivity| |].
    - unfold MonadVM.Vm.Make.spend. now rewrite Hgas.
    - unfold MonadVM.Vm.Make.push. cbn. now rewrite Hdepth.
  Qed.

  Lemma gas_after_spend_and_push (state spent pushed : State) :
    @MonadVM.Vm.Make.spend Host_t F U9
      (MonadVM.Gas.base (_rocq_assumption_0 := U9)) state =
      (inl tt, spent) ->
    @MonadVM.Vm.Make.push Host_t F
      (MonadVM.Numeric.U256.of_uint_truncating
        (_rocq_assumption_0 := U6) (_rocq_assumption_1 := U24)
        spent.(MonadVM.Vm.Make.MachineState.t.gas)) spent =
      (inl tt, pushed) ->
    dispatch MonadVM.Opcode.Gas state =
      @MonadVM.Vm.Make.increase_pc_and_continue Host_t F U6 pushed.
  Proof.
    intros Hspent Hpush.
    unfold dispatch.
    cbn [MonadVM.Vm.Make.Executor.execute_opcode].
    unfold MonadVM.Vm.Make.Executor.gas_.
    cbn -[MonadVM.Vm.Make.spend MonadVM.Vm.Make.push
      MonadVM.Numeric.U256.of_uint_truncating].
    change (@MonadVM.Vm.Make.spend Host_t F U9 2 state =
      (inl tt, spent)) in Hspent.
    rewrite Hspent.
    cbn -[MonadVM.Vm.Make.push
      MonadVM.Numeric.U256.of_uint_truncating].
    rewrite Hpush.
    reflexivity.
  Qed.

  Lemma gas_out_of_gas_exact (state : State) :
    MonadVM.Gas.op_lt
      state.(MonadVM.Vm.Make.MachineState.t.gas)
      (MonadVM.Gas.base (_rocq_assumption_0 := U9)) = true ->
    dispatch MonadVM.Opcode.Gas state =
      (inr MonadVM.Evmc.Result.StatusCode.Out_of_gas, state).
  Proof.
    intro Hgas.
    unfold dispatch.
    cbn [MonadVM.Vm.Make.Executor.execute_opcode].
    unfold MonadVM.Vm.Make.Executor.gas_, MonadVM.Vm.Make.spend.
    change (MonadVM.Gas.op_lt
      state.(MonadVM.Vm.Make.MachineState.t.gas) 2 = true) in Hgas.
    cbn -[MonadVM.Gas.op_lt].
    rewrite Hgas.
    reflexivity.
  Qed.

  Lemma gas_stack_overflow_exact (state : State) :
    MonadVM.Gas.op_lt
      state.(MonadVM.Vm.Make.MachineState.t.gas)
      (MonadVM.Gas.base (_rocq_assumption_0 := U9)) = false ->
    Z.geb state.(MonadVM.Vm.Make.MachineState.t.stack_depth)
      MonadVM.Vm.Make.max_stack_depth = true ->
    let spent := MonadVM.Vm.Make.MachineState.t.with_gas
      (MonadVM.Gas.op_minus (_rocq_assumption_0 := U9)
        state.(MonadVM.Vm.Make.MachineState.t.gas)
        (MonadVM.Gas.base (_rocq_assumption_0 := U9))) state in
    dispatch MonadVM.Opcode.Gas state =
      (inr MonadVM.Evmc.Result.StatusCode.Stack_overflow, spent).
  Proof.
    intros Hgas Hdepth.
    unfold dispatch.
    cbn [MonadVM.Vm.Make.Executor.execute_opcode].
    unfold MonadVM.Vm.Make.Executor.gas_, MonadVM.Vm.Make.spend.
    change (MonadVM.Gas.op_lt
      state.(MonadVM.Vm.Make.MachineState.t.gas) 2 = false) in Hgas.
    cbn -[MonadVM.Gas.op_lt MonadVM.Vm.Make.push].
    rewrite Hgas.
    cbn -[MonadVM.Vm.Make.push].
    unfold MonadVM.Vm.Make.push.
    cbn.
    rewrite Hdepth.
    reflexivity.
  Qed.

  Lemma gas_success_exact (state : State) :
    MonadVM.Gas.op_lt
      state.(MonadVM.Vm.Make.MachineState.t.gas)
      (MonadVM.Gas.base (_rocq_assumption_0 := U9)) = false ->
    Z.geb state.(MonadVM.Vm.Make.MachineState.t.stack_depth)
      MonadVM.Vm.Make.max_stack_depth = false ->
    let spent := MonadVM.Vm.Make.MachineState.t.with_gas
      (MonadVM.Gas.op_minus (_rocq_assumption_0 := U9)
        state.(MonadVM.Vm.Make.MachineState.t.gas)
        (MonadVM.Gas.base (_rocq_assumption_0 := U9))) state in
    let pushed := MonadVM.Vm.Make.MachineState.t.with_stack_depth
      (Z.add state.(MonadVM.Vm.Make.MachineState.t.stack_depth) 1)
      (MonadVM.Vm.Make.MachineState.t.with_stack
        (MonadVM.Numeric.U256.of_uint_truncating
          (_rocq_assumption_0 := U6) (_rocq_assumption_1 := U24)
          spent.(MonadVM.Vm.Make.MachineState.t.gas) ::
          state.(MonadVM.Vm.Make.MachineState.t.stack)) spent) in
    dispatch MonadVM.Opcode.Gas state =
      (inl true,
       MonadVM.Vm.Make.MachineState.t.with_pc
         ((state.(MonadVM.Vm.Make.MachineState.t.pc) + 1)
            mod (2 ^ 256))%Z pushed).
  Proof.
    intros Hgas Hdepth.
    rewrite (gas_after_spend_and_push state
      (MonadVM.Vm.Make.MachineState.t.with_gas
        (MonadVM.Gas.op_minus (_rocq_assumption_0 := U9)
          state.(MonadVM.Vm.Make.MachineState.t.gas)
          (MonadVM.Gas.base (_rocq_assumption_0 := U9))) state)
      (MonadVM.Vm.Make.MachineState.t.with_stack_depth
        (Z.add state.(MonadVM.Vm.Make.MachineState.t.stack_depth) 1)
        (MonadVM.Vm.Make.MachineState.t.with_stack
          (MonadVM.Numeric.U256.of_uint_truncating
            (_rocq_assumption_0 := U6) (_rocq_assumption_1 := U24)
            (MonadVM.Vm.Make.MachineState.t.with_gas
              (MonadVM.Gas.op_minus (_rocq_assumption_0 := U9)
                state.(MonadVM.Vm.Make.MachineState.t.gas)
                (MonadVM.Gas.base (_rocq_assumption_0 := U9))) state).(
                  MonadVM.Vm.Make.MachineState.t.gas) ::
            state.(MonadVM.Vm.Make.MachineState.t.stack))
          (MonadVM.Vm.Make.MachineState.t.with_gas
            (MonadVM.Gas.op_minus (_rocq_assumption_0 := U9)
              state.(MonadVM.Vm.Make.MachineState.t.gas)
              (MonadVM.Gas.base (_rocq_assumption_0 := U9))) state))));
      [rewrite increase_pc_mod; reflexivity| |].
    - unfold MonadVM.Vm.Make.spend. now rewrite Hgas.
    - unfold MonadVM.Vm.Make.push. cbn. now rewrite Hdepth.
  Qed.

  Lemma jumpdest_spend_exact (state : State) :
    MonadVM.Gas.op_lt
      state.(MonadVM.Vm.Make.MachineState.t.gas)
      (MonadVM.Gas.jumpdest (_rocq_assumption_0 := U9)) = false ->
    @MonadVM.Vm.Make.spend Host_t F U9
      (MonadVM.Gas.jumpdest (_rocq_assumption_0 := U9)) state =
      (inl tt,
       MonadVM.Vm.Make.MachineState.t.with_gas
         (MonadVM.Gas.op_minus (_rocq_assumption_0 := U9)
           state.(MonadVM.Vm.Make.MachineState.t.gas)
           (MonadVM.Gas.jumpdest (_rocq_assumption_0 := U9))) state).
  Proof.
    intro Hgas.
    unfold MonadVM.Vm.Make.spend.
    rewrite Hgas.
    reflexivity.
  Qed.

  Lemma jumpdest_exact (state : State) :
    (@MonadVM.Vm.Make.Params Host_t F).(
      MonadVM.Vm.Make_Params_signature.debug_tstore) = false ->
    MonadVM.Gas.op_lt
      state.(MonadVM.Vm.Make.MachineState.t.gas)
      (MonadVM.Gas.jumpdest (_rocq_assumption_0 := U9)) = false ->
    dispatch MonadVM.Opcode.Jumpdest state =
      @MonadVM.Vm.Make.increase_pc_and_continue Host_t F U6
        (MonadVM.Vm.Make.MachineState.t.with_gas
          (MonadVM.Gas.op_minus (_rocq_assumption_0 := U9)
            state.(MonadVM.Vm.Make.MachineState.t.gas)
            (MonadVM.Gas.jumpdest (_rocq_assumption_0 := U9))) state).
  Proof.
    intros Hdebug Hgas.
    eapply jumpdest_after_spend.
    - exact Hdebug.
    - apply jumpdest_spend_exact. exact Hgas.
  Qed.

  Lemma jumpdest_out_of_gas_exact (state : State) :
    (@MonadVM.Vm.Make.Params Host_t F).(
      MonadVM.Vm.Make_Params_signature.debug_tstore) = false ->
    MonadVM.Gas.op_lt
      state.(MonadVM.Vm.Make.MachineState.t.gas)
      (MonadVM.Gas.jumpdest (_rocq_assumption_0 := U9)) = true ->
    dispatch MonadVM.Opcode.Jumpdest state =
      (inr MonadVM.Evmc.Result.StatusCode.Out_of_gas, state).
  Proof.
    intros Hdebug Hgas.
    unfold dispatch.
    cbn [MonadVM.Vm.Make.Executor.execute_opcode].
    unfold MonadVM.Vm.Make.Executor.jumpdest,
      MonadVM.Vm.Make.Executor.debug_tstore_stack.
    rewrite Hdebug.
    cbn -[MonadVM.Vm.Make.spend].
    unfold MonadVM.Vm.Make.spend.
    change (MonadVM.Gas.op_lt
      state.(MonadVM.Vm.Make.MachineState.t.gas) 1 = true) in Hgas.
    rewrite Hgas.
    reflexivity.
  Qed.

  Lemma pop_after_spend (state after_pop after_spend : State)
      (head : MonadVM.Numeric.U256.t) :
    @MonadVM.Vm.Make.pop Host_t F state = (inl head, after_pop) ->
    @MonadVM.Vm.Make.spend Host_t F U9
      (MonadVM.Gas.base (_rocq_assumption_0 := U9)) after_pop =
      (inl tt, after_spend) ->
    dispatch MonadVM.Opcode.Pop state =
      @MonadVM.Vm.Make.increase_pc_and_continue Host_t F U6 after_spend.
  Proof.
    intros Hpop Hspend.
    unfold dispatch.
    cbn [MonadVM.Vm.Make.Executor.execute_opcode].
    unfold MonadVM.Vm.Make.Executor.pop_.
    cbn -[MonadVM.Vm.Make.pop MonadVM.Vm.Make.spend].
    rewrite Hpop.
    cbn -[MonadVM.Vm.Make.spend].
    change (@MonadVM.Vm.Make.spend Host_t F U9 2 after_pop =
      (inl tt, after_spend)) in Hspend.
    rewrite Hspend.
    reflexivity.
  Qed.

  Lemma pop_underflow_exact (state : State) :
    state.(MonadVM.Vm.Make.MachineState.t.stack) = Datatypes.nil ->
    dispatch MonadVM.Opcode.Pop state =
      (inr MonadVM.Evmc.Result.StatusCode.Stack_underflow, state).
  Proof.
    intro Hstack.
    unfold dispatch.
    cbn [MonadVM.Vm.Make.Executor.execute_opcode].
    unfold MonadVM.Vm.Make.Executor.pop_, MonadVM.Vm.Make.pop.
    cbn -[MonadVM.Vm.Make.spend].
    rewrite Hstack.
    reflexivity.
  Qed.

  Lemma pop_head_exact (state : State)
      (head : MonadVM.Numeric.U256.t)
      (tail : list MonadVM.Numeric.U256.t) :
    state.(MonadVM.Vm.Make.MachineState.t.stack) =
      Datatypes.cons head tail ->
    @MonadVM.Vm.Make.pop Host_t F state =
      (inl head,
       MonadVM.Vm.Make.MachineState.t.with_stack_depth
         (Z.sub state.(MonadVM.Vm.Make.MachineState.t.stack_depth) 1)
         (MonadVM.Vm.Make.MachineState.t.with_stack tail state)).
  Proof.
    intro Hstack.
    unfold MonadVM.Vm.Make.pop.
    rewrite Hstack.
    reflexivity.
  Qed.

  Lemma pop_spend_exact (state : State) :
    MonadVM.Gas.op_lt
      state.(MonadVM.Vm.Make.MachineState.t.gas)
      (MonadVM.Gas.base (_rocq_assumption_0 := U9)) = false ->
    @MonadVM.Vm.Make.spend Host_t F U9
      (MonadVM.Gas.base (_rocq_assumption_0 := U9)) state =
      (inl tt,
       MonadVM.Vm.Make.MachineState.t.with_gas
         (MonadVM.Gas.op_minus (_rocq_assumption_0 := U9)
           state.(MonadVM.Vm.Make.MachineState.t.gas)
           (MonadVM.Gas.base (_rocq_assumption_0 := U9))) state).
  Proof.
    intro Hgas.
    unfold MonadVM.Vm.Make.spend.
    rewrite Hgas.
    reflexivity.
  Qed.

  Lemma pop_success_exact (state : State)
      (head : MonadVM.Numeric.U256.t)
      (tail : list MonadVM.Numeric.U256.t) :
    state.(MonadVM.Vm.Make.MachineState.t.stack) =
      Datatypes.cons head tail ->
    MonadVM.Gas.op_lt
      state.(MonadVM.Vm.Make.MachineState.t.gas)
      (MonadVM.Gas.base (_rocq_assumption_0 := U9)) = false ->
    let popped :=
      MonadVM.Vm.Make.MachineState.t.with_stack_depth
        (Z.sub state.(MonadVM.Vm.Make.MachineState.t.stack_depth) 1)
        (MonadVM.Vm.Make.MachineState.t.with_stack tail state) in
    dispatch MonadVM.Opcode.Pop state =
      @MonadVM.Vm.Make.increase_pc_and_continue Host_t F U6
        (MonadVM.Vm.Make.MachineState.t.with_gas
          (MonadVM.Gas.op_minus (_rocq_assumption_0 := U9)
            popped.(MonadVM.Vm.Make.MachineState.t.gas)
            (MonadVM.Gas.base (_rocq_assumption_0 := U9))) popped).
  Proof.
    intros Hstack Hgas.
    set (popped := MonadVM.Vm.Make.MachineState.t.with_stack_depth
      (Z.sub state.(MonadVM.Vm.Make.MachineState.t.stack_depth) 1)
      (MonadVM.Vm.Make.MachineState.t.with_stack tail state)).
    eapply pop_after_spend.
    - subst popped. apply pop_head_exact. exact Hstack.
    - apply pop_spend_exact.
      subst popped.
      cbn [MonadVM.Vm.Make.MachineState.t.gas
        MonadVM.Vm.Make.MachineState.t.with_stack_depth
        MonadVM.Vm.Make.MachineState.t.with_stack].
      exact Hgas.
  Qed.

  Lemma pop_out_of_gas_exact (state : State)
      (head : MonadVM.Numeric.U256.t)
      (tail : list MonadVM.Numeric.U256.t) :
    state.(MonadVM.Vm.Make.MachineState.t.stack) =
      Datatypes.cons head tail ->
    MonadVM.Gas.op_lt
      state.(MonadVM.Vm.Make.MachineState.t.gas)
      (MonadVM.Gas.base (_rocq_assumption_0 := U9)) = true ->
    dispatch MonadVM.Opcode.Pop state =
      (inr MonadVM.Evmc.Result.StatusCode.Out_of_gas,
       MonadVM.Vm.Make.MachineState.t.with_stack_depth
         (Z.sub state.(MonadVM.Vm.Make.MachineState.t.stack_depth) 1)
         (MonadVM.Vm.Make.MachineState.t.with_stack tail state)).
  Proof.
    intros Hstack Hgas.
    unfold dispatch.
    cbn [MonadVM.Vm.Make.Executor.execute_opcode].
    unfold MonadVM.Vm.Make.Executor.pop_, MonadVM.Vm.Make.pop.
    cbn -[MonadVM.Vm.Make.spend].
    rewrite Hstack.
    cbn -[MonadVM.Vm.Make.spend].
    unfold MonadVM.Vm.Make.spend.
    change (MonadVM.Gas.op_lt
      state.(MonadVM.Vm.Make.MachineState.t.gas) 2 = true) in Hgas.
    cbn [MonadVM.Vm.Make.MachineState.t.gas
      MonadVM.Vm.Make.MachineState.t.with_stack_depth
      MonadVM.Vm.Make.MachineState.t.with_stack].
    rewrite Hgas.
    reflexivity.
  Qed.

  Lemma return_no_continuing :
    no_continuing (dispatch MonadVM.Opcode.Return).
  Proof.
    unfold dispatch.
    cbn [MonadVM.Vm.Make.Executor.execute_opcode].
    unfold MonadVM.Vm.Make.Executor.return_.
    eapply bind_no_continuing. intros [].
    eapply bind_no_continuing. intros [start size_bytes].
    eapply bind_no_continuing. intros [].
    eapply bind_no_continuing. intros result_value.
    eapply bind_no_continuing. intros [].
    apply finish_execution_no_continuing.
  Qed.

  Lemma revert_no_continuing :
    no_continuing (dispatch MonadVM.Opcode.Revert).
  Proof.
    unfold dispatch.
    cbn [MonadVM.Vm.Make.Executor.execute_opcode].
    unfold MonadVM.Vm.Make.Executor.revert.
    eapply bind_no_continuing. intros [start size_bytes].
    eapply bind_no_continuing. intros [].
    eapply bind_no_continuing. intros result_value.
    eapply bind_no_continuing. intros [].
    apply fail_no_continuing.
  Qed.

  Lemma selfdestruct_no_continuing :
    no_continuing (dispatch MonadVM.Opcode.Selfdestruct).
  Proof.
    unfold dispatch.
    cbn [MonadVM.Vm.Make.Executor.execute_opcode].
    unfold MonadVM.Vm.Make.Executor.selfdestruct.
    eapply bind_no_continuing. intros [].
    eapply bind_no_continuing. intros beneficiary.
    eapply bind_no_continuing. intros access.
    eapply bind_no_continuing. intros self_balance.
    eapply bind_no_continuing. intros beneficiary_exists.
    eapply bind_no_continuing. intros [].
    eapply bind_no_continuing. intros [].
    eapply bind_no_continuing. intros [].
    apply finish_execution_no_continuing.
  Qed.

  Definition well_formed_opcode (opcode : MonadVM.Opcode.t) : Prop :=
    match opcode with
    | MonadVM.Opcode.Push width => (0 <= width <= 32)%Z
    | MonadVM.Opcode.Dup index => (1 <= index <= 16)%Z
    | MonadVM.Opcode.Swap index => (1 <= index <= 16)%Z
    | MonadVM.Opcode.Log topics => (0 <= topics <= 4)%Z
    | _ => True
    end.

  Definition unresolved_opcode (opcode : MonadVM.Opcode.t) : Prop :=
    match opcode with
    | MonadVM.Opcode.Create
    | MonadVM.Opcode.Call
    | MonadVM.Opcode.Callcode
    | MonadVM.Opcode.Delegatecall
    | MonadVM.Opcode.Create2
    | MonadVM.Opcode.Staticcall => True
    | _ => False
    end.

  Lemma decreasing_handler_continues (opcode : MonadVM.Opcode.t) :
    gas_decreasing (dispatch opcode) -> continuing_progress opcode.
  Proof.
    intros Hdecreasing state next _ Hsuccess.
    exact (Hdecreasing state true next Hsuccess).
  Qed.

  Ltac dispatch_exact fact :=
    eapply decreasing_handler_continues;
    unfold dispatch;
    cbn [MonadVM.Vm.Make.Executor.execute_opcode];
    apply fact.

  Ltac dispatch_bounded fact bound :=
    eapply decreasing_handler_continues;
    unfold dispatch;
    cbn [MonadVM.Vm.Make.Executor.execute_opcode];
    apply fact; exact bound.

  Lemma dispatch_continuing_progress (opcode : MonadVM.Opcode.t) :
    well_formed_opcode opcode ->
    ((@MonadVM.Vm.Make.Params Host_t F).(
      MonadVM.Vm.Make_Params_signature.revision) =
        MonadVM.Support.Variants.Revision.Eight \/
     (@MonadVM.Vm.Make.Params Host_t F).(
      MonadVM.Vm.Make_Params_signature.revision) =
        MonadVM.Support.Variants.Revision.Nine) ->
    (forall open_opcode, unresolved_opcode open_opcode ->
      continuing_progress open_opcode) ->
    continuing_progress opcode.
  Proof.
    intros Hvalid Hrevision Hopen.
    destruct opcode.
    - (* Stop *) apply no_continuing_progress, stop_no_continuing.
    - (* Add *) dispatch_exact add_opcode_compositional_decreasing.
    - (* Mul *) dispatch_exact mul_opcode_compositional_decreasing.
    - (* Sub *) dispatch_exact sub_opcode_compositional_decreasing.
    - (* Udiv *) dispatch_exact udiv_opcode_compositional_decreasing.
    - (* Sdiv *) dispatch_exact
        (@sdiv_opcode_compositional_decreasing Host_t F E
          U6 U8 U9 U29 U30).
    - (* Umod *) dispatch_exact umod_opcode_compositional_decreasing.
    - (* Smod *) dispatch_exact
        (@smod_opcode_compositional_decreasing Host_t F E
          U6 U8 U9 U29 U30).
    - (* Addmod *) dispatch_exact addmod_opcode_compositional_decreasing.
    - (* Mulmod *) dispatch_exact mulmod_opcode_compositional_decreasing.
    - (* Exp *) dispatch_exact
        (@exp_opcode_compositional_decreasing Host_t F E
          U0 U4 U6 U9 U15 U23).
    - (* Signextend *) dispatch_exact
        (@signextend_opcode_compositional_decreasing Host_t F E
          U0 U6 U9 U21 U29 U30).
    - (* Lt *) dispatch_exact lt_opcode_compositional_decreasing.
    - (* Gt *) dispatch_exact gt_opcode_compositional_decreasing.
    - (* Slt *) dispatch_exact
        (@slt_opcode_compositional_decreasing Host_t F E U9 U6 U30).
    - (* Sgt *) dispatch_exact
        (@sgt_opcode_compositional_decreasing Host_t F E U9 U6 U30).
    - (* Eq *) dispatch_exact eq_opcode_compositional_decreasing.
    - (* Iszero *) dispatch_exact is_zero_opcode_compositional_decreasing.
    - (* And *) dispatch_exact bitwise_and_opcode_compositional_decreasing.
    - (* Or *) dispatch_exact bitwise_or_opcode_compositional_decreasing.
    - (* Xor *) dispatch_exact bitwise_xor_opcode_compositional_decreasing.
    - (* Not *) dispatch_exact bitwise_not_opcode_compositional_decreasing.
    - (* Byte *) dispatch_exact
        (@byte_opcode_compositional_decreasing Host_t F E U9 U6 U21 U22).
    - (* Shl *) dispatch_exact
        (@shl_opcode_compositional_decreasing Host_t F E U9 U6 U21).
    - (* Shr *) dispatch_exact
        (@shr_opcode_compositional_decreasing Host_t F E U9 U6 U21).
    - (* Sar *) dispatch_exact
        (@sar_opcode_compositional_decreasing Host_t F E
          U6 U8 U9 U21 U29 U30).
    - (* Clz *) destruct Hrevision as [Heigh | Hnine].
      + intros state next _ Hsuccess.
        exfalso.
        unfold dispatch in Hsuccess.
        cbn [MonadVM.Vm.Make.Executor.execute_opcode] in Hsuccess.
        eapply (@clz_eight_has_no_successful_result Host_t F E
          U6 U9 U15 U23 U27);
          [exact Heigh | exact Hsuccess].
      + eapply decreasing_handler_continues.
        unfold dispatch.
        cbn [MonadVM.Vm.Make.Executor.execute_opcode].
        apply (@clz_nine_opcode_compositional_decreasing Host_t F E
          U6 U9 U15 U23 U27);
          exact Hnine.
    - (* Keccak *) dispatch_exact
        (@keccak_opcode_compositional_decreasing Host_t F E
          U4 U6 U9 U12 U15 U16 U19 U21 U22 U25 U31 U32).
    - (* Address *) dispatch_exact
        (@address_opcode_compositional_decreasing Host_t F E
          U9 U6 U16 U21 U22).
    - (* Balance *) dispatch_exact balance_opcode_compositional_decreasing.
    - (* Origin *) dispatch_exact
        (@origin_opcode_compositional_decreasing Host_t F E
          U9 U6 U16 U21 U22).
    - (* Caller *) dispatch_exact
        (@caller_opcode_compositional_decreasing Host_t F E
          U9 U6 U16 U21 U22).
    - (* Callvalue *) dispatch_exact callvalue_opcode_compositional_decreasing.
    - (* Calldataload *) dispatch_exact
        (@calldataload_opcode_compositional_decreasing Host_t F E
          U6 U9 U16 U21 U22).
    - (* Calldatasize *) dispatch_exact
        (@calldatasize_opcode_compositional_decreasing Host_t F E U9 U6).
    - (* Calldatacopy *) dispatch_exact
        (@calldatacopy_opcode_compositional_decreasing Host_t F E
          U4 U6 U9 U12 U15 U20 U21 U22 U25 U31 U32).
    - (* Codesize *) dispatch_exact
        (@codesize_opcode_compositional_decreasing Host_t F E U9 U6).
    - (* Codecopy *) dispatch_exact
        (@codecopy_opcode_compositional_decreasing Host_t F E
          U4 U6 U9 U12 U15 U20 U21 U22 U25 U31 U32).
    - (* Gasprice *) dispatch_exact gasprice_opcode_compositional_decreasing.
    - (* Extcodesize *) dispatch_exact
        (@extcodesize_opcode_compositional_decreasing Host_t F E
          U5 U6 U9 U11 U15 U21 U22 U23).
    - (* Extcodecopy *) dispatch_exact
        (@extcodecopy_opcode_compositional_decreasing Host_t F E
          U4 U5 U6 U9 U11 U12 U15 U16 U20 U21 U22 U23 U25 U31 U32).
    - (* Returndatasize *) dispatch_exact
        (@returndatasize_opcode_compositional_decreasing Host_t F E U9 U6).
    - (* Returndatacopy *) dispatch_exact
        (@returndatacopy_opcode_compositional_decreasing Host_t F E
          U4 U6 U9 U12 U15 U16 U20 U21 U25 U31 U32).
    - (* Extcodehash *) dispatch_exact
        (@extcodehash_opcode_compositional_decreasing Host_t F E
          U5 U6 U9 U11 U15 U21 U22 U23 U31).
    - (* Blockhash *) dispatch_exact
        (@blockhash_opcode_compositional_decreasing Host_t F E
          U3 U4 U6 U9 U22).
    - (* Coinbase *) dispatch_exact
        (@coinbase_opcode_compositional_decreasing Host_t F E
          U9 U6 U16 U21 U22).
    - (* Timestamp *) dispatch_exact timestamp_opcode_compositional_decreasing.
    - (* Number *) dispatch_exact number_opcode_compositional_decreasing.
    - (* Prevrandao *) dispatch_exact prevrandao_opcode_compositional_decreasing.
    - (* Gaslimit *) dispatch_exact gaslimit_opcode_compositional_decreasing.
    - (* Chainid *) dispatch_exact chainid_opcode_compositional_decreasing.
    - (* Selfbalance *) dispatch_exact selfbalance_opcode_compositional_decreasing.
    - (* Basefee *) dispatch_exact basefee_opcode_compositional_decreasing.
    - (* Blobhash *) dispatch_exact
        (@blobhash_opcode_compositional_decreasing Host_t F E
          U6 U9 U18 U21 U22).
    - (* Blobbasefee *) dispatch_exact blobbasefee_opcode_compositional_decreasing.
    - (* Pop *) dispatch_exact pop_opcode_compositional_decreasing.
    - (* Mload *) dispatch_exact
        (@mload_opcode_compositional_decreasing Host_t F E
          U4 U5 U6 U9 U12 U15 U19 U21 U22 U25 U31 U32).
    - (* Mstore *) dispatch_exact
        (@mstore_opcode_compositional_decreasing Host_t F E
          U4 U5 U6 U9 U12 U15 U16 U20 U21 U22 U23 U25 U31 U32).
    - (* Mstore8 *) dispatch_exact
        (@mstore8_opcode_compositional_decreasing Host_t F E
          U4 U6 U9 U12 U15 U16 U20 U21 U22 U25 U31 U32).
    - (* Sload *) dispatch_exact
        (@sload_opcode_compositional_decreasing Host_t F E
          U5 U6 U9 U15 U21 U22 U23).
    - (* Sstore *) dispatch_exact
        (@sstore_opcode_compositional_decreasing Host_t F E
          U5 U6 U7 U9 U15 U21 U22 U23 U28).
    - (* Jump *) dispatch_exact
        (@jump_opcode_compositional_decreasing Host_t F E U6 U9 U22).
    - (* Jumpi *) dispatch_exact
        (@jumpi_opcode_compositional_decreasing Host_t F E U6 U9 U22).
    - (* Pc *) dispatch_exact pc_opcode_compositional_decreasing.
    - (* Msize *) dispatch_exact msize_opcode_compositional_decreasing.
    - (* Gas *) dispatch_exact gas_opcode_compositional_decreasing.
    - (* Jumpdest *) dispatch_exact
        (@jumpdest_opcode_compositional_decreasing Host_t F E
          U5 U6 U9 U15 U21 U22 U23).
    - (* Tload *) dispatch_exact
        (@tload_opcode_compositional_decreasing Host_t F E
          U5 U6 U9 U15 U21 U22 U23).
    - (* Tstore *) dispatch_exact
        (@tstore_opcode_compositional_decreasing Host_t F E
          U5 U6 U9 U15 U21 U22 U23).
    - (* Mcopy *) dispatch_exact
        (@mcopy_opcode_compositional_decreasing Host_t F E
          U4 U6 U9 U12 U15 U16 U19 U20 U21 U25 U31 U32).
    - (* Push *) dispatch_bounded
        (@push_opcode_compositional_decreasing Host_t F E
          U4 U6 U9 U12 U15 U21 U22 i) Hvalid.
    - (* Dup *) dispatch_bounded
        (@dup_opcode_compositional_decreasing Host_t F E
          U9 U6 U13 U15 U17 i) Hvalid.
    - (* Swap *) dispatch_bounded
        (@swap_opcode_compositional_decreasing Host_t F E
          U9 U6 U15 i) Hvalid.
    - (* Log *) dispatch_bounded
        (@log_opcode_compositional_decreasing Host_t F E
          U1 U4 U5 U6 U9 U12 U15 U19 U21 U22 U23 U25 U26 U31 U32 i)
        Hvalid.
    - (* Create *) apply Hopen; exact I.
    - (* Call *) apply Hopen; exact I.
    - (* Callcode *) apply Hopen; exact I.
    - (* Return *) apply no_continuing_progress, return_no_continuing.
    - (* Delegatecall *) apply Hopen; exact I.
    - (* Create2 *) apply Hopen; exact I.
    - (* Staticcall *) apply Hopen; exact I.
    - (* Revert *) apply no_continuing_progress, revert_no_continuing.
    - (* Invalid *) apply no_continuing_progress, invalid_no_continuing.
    - (* Selfdestruct *)
      apply no_continuing_progress, selfdestruct_no_continuing.
    - (* Undefined *)
      apply no_continuing_progress, undefined_no_continuing.
  Qed.

  Lemma unresolved_opcode_progress
      (opcode : MonadVM.Opcode.t) :
    unresolved_opcode opcode -> continuing_progress opcode.
  Proof.
    intro Hopen.
    destruct opcode; cbn in Hopen; try contradiction;
      unfold continuing_progress; intros state next Hbound Hsuccess;
      unfold dispatch in Hsuccess;
      cbn [MonadVM.Vm.Make.Executor.execute_opcode] in Hsuccess.
    1: exact ((@create_opcode_bounded_decreasing Host_t F E
      U9 U10 U12 U21 U4 U7 U15 U2 U3 U6 U11 U16 U19 U22 U31 U33
      U25 U32) state true next ltac:(lia) Hsuccess).
    1: exact ((@call_opcode_wrapper_bounded_decreasing Host_t F E
      U2 U3 U4 U6 U7 U9 U10 U11 U12 U15 U16 U19 U20 U21 U25 U31
      U32 U33 U5 U22 U23) state true next ltac:(lia) Hsuccess).
    1: exact ((@callcode_opcode_wrapper_bounded_decreasing Host_t F E
      U2 U3 U4 U6 U7 U9 U10 U11 U12 U15 U16 U19 U20 U21 U25 U31
      U32 U33 U5 U22 U23) state true next ltac:(lia) Hsuccess).
    1: exact ((@delegatecall_opcode_wrapper_bounded_decreasing Host_t F E
      U2 U3 U4 U6 U7 U9 U10 U11 U12 U15 U16 U19 U20 U21 U25 U31
      U32 U33 U5 U22 U23) state true next ltac:(lia) Hsuccess).
    1: exact ((@create2_opcode_bounded_decreasing Host_t F E
      U9 U10 U12 U21 U4 U7 U15 U2 U3 U6 U11 U16 U19 U22 U31 U33
      U25 U32 U5 U23) state true next ltac:(lia) Hsuccess).
    1: exact ((@staticcall_opcode_wrapper_bounded_decreasing Host_t F E
      U2 U3 U4 U6 U7 U9 U10 U11 U12 U15 U16 U19 U20 U21 U25 U31
      U32 U33 U5 U22 U23) state true next ltac:(lia) Hsuccess).
  Qed.

  Lemma decoded_opcode_well_formed (byte : ascii) :
    well_formed_opcode (MonadVM.Opcode.of_byte byte).
  Proof.
    destruct (MonadVM.Opcode.of_byte byte) eqn:Hdecoded;
      cbn; try exact I;
      eauto using decoded_push_width, decoded_dup_index,
        decoded_swap_index, decoded_log_topics.
  Qed.

  Lemma dispatch_all_continuing_progress
      (opcode : MonadVM.Opcode.t) :
    well_formed_opcode opcode ->
    ((@MonadVM.Vm.Make.Params Host_t F).(
      MonadVM.Vm.Make_Params_signature.revision) =
        MonadVM.Support.Variants.Revision.Eight \/
     (@MonadVM.Vm.Make.Params Host_t F).(
      MonadVM.Vm.Make_Params_signature.revision) =
        MonadVM.Support.Variants.Revision.Nine) ->
    continuing_progress opcode.
  Proof.
    intros Hvalid Hrevision.
    eapply dispatch_continuing_progress; eauto.
    intros open_opcode Hopen.
    apply unresolved_opcode_progress; assumption.
  Qed.

  Lemma decoded_dispatch_continuing_progress (byte : ascii) :
    ((@MonadVM.Vm.Make.Params Host_t F).(
      MonadVM.Vm.Make_Params_signature.revision) =
        MonadVM.Support.Variants.Revision.Eight \/
     (@MonadVM.Vm.Make.Params Host_t F).(
      MonadVM.Vm.Make_Params_signature.revision) =
        MonadVM.Support.Variants.Revision.Nine) ->
    (forall open_opcode, unresolved_opcode open_opcode ->
      continuing_progress open_opcode) ->
    continuing_progress (MonadVM.Opcode.of_byte byte).
  Proof.
    intros Hrevision Hopen.
    apply dispatch_continuing_progress.
    - apply decoded_opcode_well_formed.
    - exact Hrevision.
    - exact Hopen.
  Qed.

  Lemma decoded_dispatch_all_continuing_progress
      (byte : ascii) :
    ((@MonadVM.Vm.Make.Params Host_t F).(
      MonadVM.Vm.Make_Params_signature.revision) =
        MonadVM.Support.Variants.Revision.Eight \/
     (@MonadVM.Vm.Make.Params Host_t F).(
      MonadVM.Vm.Make_Params_signature.revision) =
        MonadVM.Support.Variants.Revision.Nine) ->
    continuing_progress (MonadVM.Opcode.of_byte byte).
  Proof.
    intro Hrevision.
    apply dispatch_all_continuing_progress; auto.
    apply decoded_opcode_well_formed.
  Qed.

  Lemma decoded_dispatch_guard_true
      (byte : ascii) (state next : State) :
    ((@MonadVM.Vm.Make.Params Host_t F).(
      MonadVM.Vm.Make_Params_signature.revision) =
        MonadVM.Support.Variants.Revision.Eight \/
     (@MonadVM.Vm.Make.Params Host_t F).(
      MonadVM.Vm.Make_Params_signature.revision) =
        MonadVM.Support.Variants.Revision.Nine) ->
    (Z.of_N state.(MonadVM.Vm.Make.MachineState.t.gas) < 2 ^ 63)%Z ->
    dispatch (MonadVM.Opcode.of_byte byte) state =
      (inl true, next) ->
    MonadVM.Gas.op_lt
      next.(MonadVM.Vm.Make.MachineState.t.gas)
      state.(MonadVM.Vm.Make.MachineState.t.gas) = true /\
    (Z.of_N next.(MonadVM.Vm.Make.MachineState.t.gas) < 2 ^ 63)%Z.
  Proof.
    intros Hrevision Hbound Hrun.
    pose proof (decoded_dispatch_all_continuing_progress
      byte Hrevision state next Hbound Hrun) as Hstrict.
    split.
    - unfold MonadVM.Gas.op_lt, MonadVM.Support.UintN.op_lt.
      apply N.ltb_lt. exact Hstrict.
    - lia.
  Qed.

  (** The opcode chosen by the generated [run] loop is either decoded from
      bytecode or [Stop] when the program counter is outside the code. *)
  Let run_bytecode :=
    (@MonadVM.Vm.Make.Executor.C Host_t F E).(
      MonadVM.Vm.Make.Executor_C_signature.execution_environment).(
      MonadVM.Vm.Make.ExecutionEnvironment.t.bytecode).

  Definition run_selected_opcode (state : State) : MonadVM.Opcode.t :=
    let pc := state.(MonadVM.Vm.Make.MachineState.t.pc) in
    match
      (MonadVM.Numeric.U256.to_int_opt
         (_rocq_assumption_0 := U21) pc,
       match MonadVM.Numeric.U256.to_int_opt
         (_rocq_assumption_0 := U21) pc with
       | Some index => Z.ltb index
           (MonadVM.Byte_string.Bytes.length run_bytecode)
       | None => false
       end)
    with
    | (Some index, true) =>
        MonadVM.Opcode.of_byte
          (MonadVM.String.get (_rocq_assumption_0 := U22)
            run_bytecode index)
    | _ => MonadVM.Opcode.Stop
    end.

  Lemma run_selected_opcode_eq_generated_selector (state : State) :
    run_selected_opcode state =
      @MonadVM.Vm.Make.select_opcode Host_t F U21 U22
        run_bytecode state.(MonadVM.Vm.Make.MachineState.t.pc).
  Proof. reflexivity. Qed.

  Lemma run_selected_opcode_eq_model (state : State) :
    run_selected_opcode state =
      @selected_opcode_model U21 U22 run_bytecode
        state.(MonadVM.Vm.Make.MachineState.t.pc).
  Proof.
    unfold run_selected_opcode, selected_opcode_model.
    repeat rewrite generated_u256_to_int_opt_eq.
    destruct (@pc_to_int_opt U21
      state.(MonadVM.Vm.Make.MachineState.t.pc)) as [index |]; reflexivity.
  Qed.

  Lemma run_selected_dispatch_guard_true
      (state next : State) :
    ((@MonadVM.Vm.Make.Params Host_t F).(
      MonadVM.Vm.Make_Params_signature.revision) =
        MonadVM.Support.Variants.Revision.Eight \/
     (@MonadVM.Vm.Make.Params Host_t F).(
      MonadVM.Vm.Make_Params_signature.revision) =
        MonadVM.Support.Variants.Revision.Nine) ->
    (Z.of_N state.(MonadVM.Vm.Make.MachineState.t.gas) < 2 ^ 63)%Z ->
    dispatch (run_selected_opcode state) state =
      (inl true, next) ->
    MonadVM.Gas.op_lt
      next.(MonadVM.Vm.Make.MachineState.t.gas)
      state.(MonadVM.Vm.Make.MachineState.t.gas) = true /\
    (Z.of_N next.(MonadVM.Vm.Make.MachineState.t.gas) < 2 ^ 63)%Z.
  Proof.
    intros Hrevision Hbound Hrun.
    unfold run_selected_opcode in Hrun.
    destruct (MonadVM.Numeric.U256.to_int_opt
      (_rocq_assumption_0 := U21)
      state.(MonadVM.Vm.Make.MachineState.t.pc))
      as [index |] eqn:Hindex; cbn in Hrun.
    - destruct (Z.ltb index
        (MonadVM.Byte_string.Bytes.length run_bytecode))
        eqn:Hin_code; cbn in Hrun.
      + eapply decoded_dispatch_guard_true; eauto.
      + exfalso. eapply stop_no_continuing; exact Hrun.
    - exfalso. eapply stop_no_continuing; exact Hrun.
  Qed.

  (** A finite trace records the successful continuing transitions that
      generated [run] may recurse on. The equation below relates each edge
      of this trace to the generated fixpoint. *)
  Inductive selected_dispatch_trace : nat -> State -> State -> Prop :=
  | selected_dispatch_trace_refl (state : State) :
      selected_dispatch_trace 0 state state
  | selected_dispatch_trace_step
      (steps : nat) (state middle final : State) :
      dispatch (run_selected_opcode state) state = (inl true, middle) ->
      selected_dispatch_trace steps middle final ->
      selected_dispatch_trace (S steps) state final.

  (** A single step-preservation obligation is enough to carry a combined
      machine-state invariant across every reachable continuing frame. *)
  Lemma selected_dispatch_trace_preserves
      (invariant : State -> Prop)
      (steps : nat) (state final : State) :
    (forall before after,
      invariant before ->
      dispatch (run_selected_opcode before) before = (inl true, after) ->
      invariant after) ->
    invariant state ->
    selected_dispatch_trace steps state final ->
    invariant final.
  Proof.
    intros Hstep Hinitial Htrace.
    revert Hinitial.
    induction Htrace; intro Hinitial.
    - exact Hinitial.
    - apply IHHtrace.
      eapply Hstep; eassumption.
  Qed.

  Lemma selected_dispatch_trace_gas_bound
      (steps : nat) (state final : State) :
    ((@MonadVM.Vm.Make.Params Host_t F).(
      MonadVM.Vm.Make_Params_signature.revision) =
        MonadVM.Support.Variants.Revision.Eight \/
     (@MonadVM.Vm.Make.Params Host_t F).(
      MonadVM.Vm.Make_Params_signature.revision) =
        MonadVM.Support.Variants.Revision.Nine) ->
    (Z.of_N state.(MonadVM.Vm.Make.MachineState.t.gas) < 2 ^ 63)%Z ->
    selected_dispatch_trace steps state final ->
    (N.of_nat steps <= state.(MonadVM.Vm.Make.MachineState.t.gas))%N /\
    (final.(MonadVM.Vm.Make.MachineState.t.gas) <=
      state.(MonadVM.Vm.Make.MachineState.t.gas))%N /\
    (Z.of_N final.(MonadVM.Vm.Make.MachineState.t.gas) < 2 ^ 63)%Z.
  Proof.
    intros Hrevision Hbound Htrace.
    revert Hbound.
    induction Htrace as
      [state | steps state middle final Hstep Htail IH];
      intro Hbound.
    - repeat split; cbn; lia.
    - pose proof (run_selected_dispatch_guard_true state middle
        Hrevision Hbound Hstep) as [Hguard Hmiddle_bound].
      unfold MonadVM.Gas.op_lt, MonadVM.Support.UintN.op_lt
        in Hguard.
      apply N.ltb_lt in Hguard.
      specialize (IH Hmiddle_bound).
      destruct IH as [Hsteps [Hfinal Hfinal_bound]].
      rewrite Nat2N.inj_succ.
      repeat split; lia.
  Qed.

  Corollary selected_dispatch_trace_transaction_cap
      (steps : nat) (state final : State) :
    ((@MonadVM.Vm.Make.Params Host_t F).(
      MonadVM.Vm.Make_Params_signature.revision) =
        MonadVM.Support.Variants.Revision.Eight \/
     (@MonadVM.Vm.Make.Params Host_t F).(
      MonadVM.Vm.Make_Params_signature.revision) =
        MonadVM.Support.Variants.Revision.Nine) ->
    (Z.of_N state.(MonadVM.Vm.Make.MachineState.t.gas)
      <= 30_000_000)%Z ->
    selected_dispatch_trace steps state final ->
    (Z.of_N final.(MonadVM.Vm.Make.MachineState.t.gas)
      <= 30_000_000)%Z.
  Proof.
    intros Hrevision Hcap Htrace.
    pose proof (selected_dispatch_trace_gas_bound
      steps state final Hrevision ltac:(lia) Htrace)
      as [_ [Hfinal _]].
    apply N2Z.inj_le in Hfinal.
    lia.
  Qed.

  Corollary selected_dispatch_trace_no_extra_step
      (state final : State) :
    ((@MonadVM.Vm.Make.Params Host_t F).(
      MonadVM.Vm.Make_Params_signature.revision) =
        MonadVM.Support.Variants.Revision.Eight \/
     (@MonadVM.Vm.Make.Params Host_t F).(
      MonadVM.Vm.Make_Params_signature.revision) =
        MonadVM.Support.Variants.Revision.Nine) ->
    (Z.of_N state.(MonadVM.Vm.Make.MachineState.t.gas) < 2 ^ 63)%Z ->
    ~ selected_dispatch_trace
        (S (N.to_nat state.(MonadVM.Vm.Make.MachineState.t.gas)))
        state final.
  Proof.
    intros Hrevision Hbound Htrace.
    pose proof (selected_dispatch_trace_gas_bound _ _ _
      Hrevision Hbound Htrace) as [Hsteps _].
    rewrite Nat2N.inj_succ, N2Nat.id in Hsteps.
    lia.
  Qed.

  Context `{Urun :
    RocqOfOCaml.Basics.Unreachable
      (sum unit MonadVM.Evmc.Result.StatusCode.t * State)}.

  Definition generated_run :
      State -> sum unit MonadVM.Evmc.Result.StatusCode.t * State :=
    @MonadVM.Vm.Make.Executor.run Host_t F E
      U0 U1 U2 U3 U4 U5 U6 U7 U8 U9 U10 U11 U12 U13 U15 U16
      U17 U18 U19 U20 U21 U22 U23 U24 U25 U26 U27 U28 U29 U30 U31
      Urun U32 U33.

  Definition generated_run_step (state : State) :
      sum unit MonadVM.Evmc.Result.StatusCode.t * State :=
    let '(result, next) := dispatch (run_selected_opcode state) state in
    match result with
    | inl true =>
        if MonadVM.Gas.op_lt
            next.(MonadVM.Vm.Make.MachineState.t.gas)
            state.(MonadVM.Vm.Make.MachineState.t.gas)
        then generated_run next
        else Urun.(RocqOfOCaml.Basics.unreachable)
    | inl false => (inl tt, next)
    | inr err => (inr err, next)
    end.

  Lemma generated_run_step_eq (state : State) :
    generated_run state = generated_run_step state.
  Proof.
    unfold generated_run at 1.
    unfold MonadVM.Vm.Make.Executor.run at 1.
    rewrite Fix_eq.
    2: { intros x f g Hfg.
      lazymatch goal with
      | |- context [MonadVM.Vm.Make.Executor.execute_opcode ?op x] =>
        destruct (MonadVM.Vm.Make.Executor.execute_opcode op x)
          as [[continue | err] next] eqn:Hop
      end.
      cbn.
      all: try reflexivity.
      destruct continue; cbn; try reflexivity.
      unfold MonadVM.Gas.op_lt, MonadVM.Support.UintN.op_lt.
      generalize (N.ltb_lt
        next.(MonadVM.Vm.Make.MachineState.t.gas)
        x.(MonadVM.Vm.Make.MachineState.t.gas)); intro Hiff.
      destruct (N.ltb
        next.(MonadVM.Vm.Make.MachineState.t.gas)
        x.(MonadVM.Vm.Make.MachineState.t.gas)) eqn:Hguard;
        cbn; try reflexivity.
      apply Hfg. }
    unfold generated_run_step.
    unfold run_selected_opcode, dispatch.
    unfold MonadVM.Vm.Make.select_opcode.
    destruct (MonadVM.Numeric.U256.to_int_opt
      (_rocq_assumption_0 := U21)
      state.(MonadVM.Vm.Make.MachineState.t.pc))
      as [index |] eqn:Hpc.
    1: destruct (Z.ltb index
      (MonadVM.Byte_string.Bytes.length run_bytecode)) eqn:Hin_code.
    all: try unfold run_bytecode in Hin_code.
    all: try rewrite Hin_code.
    all: cbn -[generated_run MonadVM.Vm.Make.Executor.run
      MonadVM.Vm.Make.Executor.execute_opcode Fix Fix_F].
    all: (lazymatch goal with
    | |- context [MonadVM.Vm.Make.Executor.execute_opcode ?op ?st] =>
      destruct (MonadVM.Vm.Make.Executor.execute_opcode op st)
        as [[continue | err] next] eqn:Hop
    end).
    all: unfold run_bytecode in *.
    all: try rewrite Hop.
    all: cbn -[generated_run MonadVM.Vm.Make.Executor.run Fix Fix_F].
    all: try reflexivity.
    all: destruct continue;
      cbn -[generated_run MonadVM.Vm.Make.Executor.run Fix Fix_F];
      try reflexivity.
    all: unfold MonadVM.Gas.op_lt, MonadVM.Support.UintN.op_lt.
    all: generalize (N.ltb_lt
      next.(MonadVM.Vm.Make.MachineState.t.gas)
      state.(MonadVM.Vm.Make.MachineState.t.gas)); intro Hiff.
    all: destruct (N.ltb
      next.(MonadVM.Vm.Make.MachineState.t.gas)
      state.(MonadVM.Vm.Make.MachineState.t.gas)) eqn:Hguard;
      cbn -[generated_run MonadVM.Vm.Make.Executor.run Fix Fix_F];
      try reflexivity.
  Qed.

  Lemma generated_run_stop_exact (state : State) :
    (@MonadVM.Vm.Make.Params Host_t F).(
      MonadVM.Vm.Make_Params_signature.debug_tstore) = false ->
    run_selected_opcode state = MonadVM.Opcode.Stop ->
    generated_run state =
      (inl tt,
       MonadVM.Vm.Make.MachineState.t.with_output_buffer
         MonadVM.Byte_string.Bytes.empty state).
  Proof.
    intros Hdebug Hselected.
    rewrite generated_run_step_eq.
    unfold generated_run_step.
    rewrite Hselected.
    rewrite stop_exact by exact Hdebug.
    reflexivity.
  Qed.

  Lemma generated_run_invalid_exact (state : State) :
    run_selected_opcode state = MonadVM.Opcode.Invalid ->
    generated_run state =
      (inr MonadVM.Evmc.Result.StatusCode.Invalid_instruction, state).
  Proof.
    intro Hselected.
    rewrite generated_run_step_eq.
    unfold generated_run_step.
    rewrite Hselected.
    rewrite invalid_exact.
    reflexivity.
  Qed.

  Lemma generated_run_undefined_exact (byte : ascii) (state : State) :
    run_selected_opcode state = MonadVM.Opcode.Undefined byte ->
    generated_run state =
      (inr MonadVM.Evmc.Result.StatusCode.Undefined_instruction, state).
  Proof.
    intro Hselected.
    rewrite generated_run_step_eq.
    unfold generated_run_step.
    rewrite Hselected.
    rewrite undefined_exact.
    reflexivity.
  Qed.

  Lemma generated_run_continues
      (state next : State) :
    ((@MonadVM.Vm.Make.Params Host_t F).(
      MonadVM.Vm.Make_Params_signature.revision) =
        MonadVM.Support.Variants.Revision.Eight \/
     (@MonadVM.Vm.Make.Params Host_t F).(
      MonadVM.Vm.Make_Params_signature.revision) =
        MonadVM.Support.Variants.Revision.Nine) ->
    (Z.of_N state.(MonadVM.Vm.Make.MachineState.t.gas) < 2 ^ 63)%Z ->
    dispatch (run_selected_opcode state) state = (inl true, next) ->
    generated_run state = generated_run next /\
    next.(MonadVM.Vm.Make.MachineState.t.gas) <
      state.(MonadVM.Vm.Make.MachineState.t.gas) /\
    (Z.of_N next.(MonadVM.Vm.Make.MachineState.t.gas) < 2 ^ 63)%Z.
  Proof.
    intros Hrevision Hbound Hdispatch.
    pose proof (run_selected_dispatch_guard_true state next
      Hrevision Hbound Hdispatch) as [Hguard Hnext_bound].
    rewrite generated_run_step_eq.
    unfold generated_run_step.
    rewrite Hdispatch.
    rewrite Hguard.
    repeat split; try reflexivity; try assumption.
    unfold MonadVM.Gas.op_lt, MonadVM.Support.UintN.op_lt in Hguard.
    apply N.ltb_lt. exact Hguard.
  Qed.

  Lemma generated_run_selected_trace_invariant
      (steps : nat) (state final : State) :
    ((@MonadVM.Vm.Make.Params Host_t F).(
      MonadVM.Vm.Make_Params_signature.revision) =
        MonadVM.Support.Variants.Revision.Eight \/
     (@MonadVM.Vm.Make.Params Host_t F).(
      MonadVM.Vm.Make_Params_signature.revision) =
        MonadVM.Support.Variants.Revision.Nine) ->
    (Z.of_N state.(MonadVM.Vm.Make.MachineState.t.gas) < 2 ^ 63)%Z ->
    selected_dispatch_trace steps state final ->
    generated_run state = generated_run final.
  Proof.
    intros Hrevision Hbound Htrace.
    induction Htrace.
    - reflexivity.
    - pose proof (generated_run_continues _ _ Hrevision Hbound H)
        as [Heq [_ Hmiddle_bound]].
      rewrite Heq.
      apply IHHtrace; assumption.
  Qed.

  (** A bounded interpreter with the same opcode selection and dispatch as
      generated [run], but without its runtime gas-progress check. *)
  Definition generated_run_step_without_guard (state : State) :
      sum unit MonadVM.Evmc.Result.StatusCode.t * State :=
    let '(result, next) := dispatch (run_selected_opcode state) state in
    match result with
    | inl true => generated_run next
    | inl false => (inl tt, next)
    | inr err => (inr err, next)
    end.

  Lemma generated_run_step_without_guard_eq (state : State) :
    ((@MonadVM.Vm.Make.Params Host_t F).(
      MonadVM.Vm.Make_Params_signature.revision) =
        MonadVM.Support.Variants.Revision.Eight \/
     (@MonadVM.Vm.Make.Params Host_t F).(
      MonadVM.Vm.Make_Params_signature.revision) =
        MonadVM.Support.Variants.Revision.Nine) ->
    (Z.of_N state.(MonadVM.Vm.Make.MachineState.t.gas) < 2 ^ 63)%Z ->
    generated_run state = generated_run_step_without_guard state.
  Proof.
    intros Hrevision Hbound.
    rewrite generated_run_step_eq.
    unfold generated_run_step, generated_run_step_without_guard.
    destruct (dispatch (run_selected_opcode state) state)
      as [[continue | err] next] eqn:Hdispatch;
      cbn -[generated_run MonadVM.Vm.Make.Executor.run Fix Fix_F];
      try reflexivity.
    destruct continue; try reflexivity.
    pose proof (run_selected_dispatch_guard_true state next
      Hrevision Hbound Hdispatch) as [Hguard _].
    rewrite Hguard. reflexivity.
  Qed.

  Fixpoint run_without_guard_fuel (fuel : nat) (state : State) :
      option (sum unit MonadVM.Evmc.Result.StatusCode.t * State) :=
    match fuel with
    | O => None
    | S remaining =>
        let '(result, next) :=
          dispatch (run_selected_opcode state) state in
        match result with
        | inl true => run_without_guard_fuel remaining next
        | inl false => Some (inl tt, next)
        | inr err => Some (inr err, next)
        end
    end.

  Lemma run_without_guard_fuel_agrees (fuel : nat) :
    forall state : State,
      ((@MonadVM.Vm.Make.Params Host_t F).(
        MonadVM.Vm.Make_Params_signature.revision) =
          MonadVM.Support.Variants.Revision.Eight \/
       (@MonadVM.Vm.Make.Params Host_t F).(
        MonadVM.Vm.Make_Params_signature.revision) =
          MonadVM.Support.Variants.Revision.Nine) ->
      (Z.of_N state.(MonadVM.Vm.Make.MachineState.t.gas) < 2 ^ 63)%Z ->
      (N.to_nat state.(MonadVM.Vm.Make.MachineState.t.gas) < fuel)%nat ->
      run_without_guard_fuel fuel state = Some (generated_run state).
  Proof.
    induction fuel as [|fuel IH]; intros state Hrevision Hbound Hfuel.
    - lia.
    - cbn [run_without_guard_fuel].
      destruct (dispatch (run_selected_opcode state) state)
        as [[continue | err] next] eqn:Hdispatch.
      + destruct continue.
        * pose proof (generated_run_continues state next Hrevision
            Hbound Hdispatch) as [Hrun [Hdecrease Hnext_bound]].
          assert (Hnext_fuel :
            (N.to_nat next.(MonadVM.Vm.Make.MachineState.t.gas) < fuel)%nat).
          { lia. }
          rewrite (IH next Hrevision Hnext_bound Hnext_fuel).
          rewrite Hrun. reflexivity.
        * rewrite generated_run_step_eq.
          unfold generated_run_step.
          rewrite Hdispatch. reflexivity.
      + rewrite generated_run_step_eq.
        unfold generated_run_step.
        rewrite Hdispatch. reflexivity.
  Qed.

  Corollary run_without_guard_entry_fuel (state : State) :
    ((@MonadVM.Vm.Make.Params Host_t F).(
      MonadVM.Vm.Make_Params_signature.revision) =
        MonadVM.Support.Variants.Revision.Eight \/
     (@MonadVM.Vm.Make.Params Host_t F).(
      MonadVM.Vm.Make_Params_signature.revision) =
        MonadVM.Support.Variants.Revision.Nine) ->
    (Z.of_N state.(MonadVM.Vm.Make.MachineState.t.gas) < 2 ^ 63)%Z ->
    run_without_guard_fuel
      (S (N.to_nat state.(MonadVM.Vm.Make.MachineState.t.gas))) state =
      Some (generated_run state).
  Proof.
    intros Hrevision Hbound.
    apply run_without_guard_fuel_agrees; auto.
  Qed.

  Definition returning_terminal_nonincreasing : Prop :=
    (forall (state next : State),
      (Z.of_N state.(MonadVM.Vm.Make.MachineState.t.gas) < 2 ^ 63)%Z ->
      dispatch (run_selected_opcode state) state = (inl false, next) ->
      next.(MonadVM.Vm.Make.MachineState.t.gas) <=
        state.(MonadVM.Vm.Make.MachineState.t.gas)) /\
    (forall (state next : State),
      (Z.of_N state.(MonadVM.Vm.Make.MachineState.t.gas) < 2 ^ 63)%Z ->
      dispatch (run_selected_opcode state) state =
        (inr MonadVM.Evmc.Result.StatusCode.Revert, next) ->
      next.(MonadVM.Vm.Make.MachineState.t.gas) <=
        state.(MonadVM.Vm.Make.MachineState.t.gas)).

  Lemma run_without_guard_fuel_result_gas_bound (fuel : nat) :
    forall (state final : State)
      (outcome : sum unit MonadVM.Evmc.Result.StatusCode.t),
      ((@MonadVM.Vm.Make.Params Host_t F).(
        MonadVM.Vm.Make_Params_signature.revision) =
          MonadVM.Support.Variants.Revision.Eight \/
       (@MonadVM.Vm.Make.Params Host_t F).(
        MonadVM.Vm.Make_Params_signature.revision) =
          MonadVM.Support.Variants.Revision.Nine) ->
      (Z.of_N state.(MonadVM.Vm.Make.MachineState.t.gas) < 2 ^ 63)%Z ->
      returning_terminal_nonincreasing ->
      run_without_guard_fuel fuel state = Some (outcome, final) ->
      (outcome = inl tt \/
       outcome = inr MonadVM.Evmc.Result.StatusCode.Revert) ->
      final.(MonadVM.Vm.Make.MachineState.t.gas) <=
        state.(MonadVM.Vm.Make.MachineState.t.gas) /\
      (Z.of_N final.(MonadVM.Vm.Make.MachineState.t.gas)
        < 2 ^ 63)%Z.
  Proof.
    induction fuel as [|fuel IH];
      intros state final outcome Hrevision Hbound Hterminal Hrun Hreturns.
    - cbn in Hrun. discriminate.
    - cbn [run_without_guard_fuel] in Hrun.
      destruct (dispatch (run_selected_opcode state) state)
        as [[continue | err] next] eqn:Hdispatch.
      + destruct continue.
        * pose proof (run_selected_dispatch_guard_true state next
            Hrevision Hbound Hdispatch) as [Hguard Hnext_bound].
          unfold MonadVM.Gas.op_lt, MonadVM.Support.UintN.op_lt
            in Hguard.
          apply N.ltb_lt in Hguard.
          pose proof (IH next final outcome Hrevision Hnext_bound
            Hterminal Hrun Hreturns) as [Hfinal Hfinal_bound].
          split; lia.
        * inversion Hrun; subst outcome final.
          pose proof (proj1 Hterminal state next Hbound
            Hdispatch) as Hnext.
          split; lia.
      + inversion Hrun; subst outcome final.
        destruct Hreturns as [Hsuccess | Hrevert].
        { discriminate Hsuccess. }
        inversion Hrevert; subst err.
        pose proof (proj2 Hterminal state next Hbound
          Hdispatch) as Hnext.
        split; lia.
  Qed.

  Corollary generated_run_result_gas_bound (state : State) :
    ((@MonadVM.Vm.Make.Params Host_t F).(
      MonadVM.Vm.Make_Params_signature.revision) =
        MonadVM.Support.Variants.Revision.Eight \/
     (@MonadVM.Vm.Make.Params Host_t F).(
      MonadVM.Vm.Make_Params_signature.revision) =
        MonadVM.Support.Variants.Revision.Nine) ->
    (Z.of_N state.(MonadVM.Vm.Make.MachineState.t.gas) < 2 ^ 63)%Z ->
    returning_terminal_nonincreasing ->
    (fst (generated_run state) = inl tt \/
     fst (generated_run state) =
       inr MonadVM.Evmc.Result.StatusCode.Revert) ->
    let final := snd (generated_run state) in
    final.(MonadVM.Vm.Make.MachineState.t.gas) <=
      state.(MonadVM.Vm.Make.MachineState.t.gas) /\
    (Z.of_N final.(MonadVM.Vm.Make.MachineState.t.gas)
      < 2 ^ 63)%Z.
  Proof.
    intros Hrevision Hbound Hterminal Hreturns.
    pose proof (run_without_guard_entry_fuel state Hrevision Hbound)
      as Hrun.
    destruct (generated_run state) as [outcome final] eqn:Hgenerated.
    cbn in *.
    eapply (run_without_guard_fuel_result_gas_bound
      (S (N.to_nat state.(MonadVM.Vm.Make.MachineState.t.gas)))
      state final outcome); eauto.
  Qed.

  Definition generated_dispatch_step (state : State) :
      (bool + MonadVM.Evmc.Result.StatusCode.t) * State :=
    dispatch (run_selected_opcode state) state.

  Lemma generated_dispatch_fuel_eq (fuel : nat) (state : State) :
    @model_run_fuel State MonadVM.Evmc.Result.StatusCode.t
      generated_dispatch_step fuel state =
    run_without_guard_fuel fuel state.
  Proof.
    revert state.
    induction fuel as [|fuel IH]; intro state; simpl; [reflexivity |].
    unfold generated_dispatch_step.
    destruct (dispatch (run_selected_opcode state) state)
      as [[continue | error] next]; simpl; try reflexivity.
  Qed.

  Theorem native_run_generated_dispatch_correspondence
      {NativeState : Type}
      (encode : NativeState -> State)
      (native_gas : NativeState -> Z)
      (native_dispatch : NativeState ->
        (bool + MonadVM.Evmc.Result.StatusCode.t) * NativeState)
      (state : NativeState) :
    ((@MonadVM.Vm.Make.Params Host_t F).(
      MonadVM.Vm.Make_Params_signature.revision) =
        MonadVM.Support.Variants.Revision.Eight \/
     (@MonadVM.Vm.Make.Params Host_t F).(
       MonadVM.Vm.Make_Params_signature.revision) =
        MonadVM.Support.Variants.Revision.Nine) ->
    (forall source,
      native_gas source =
        Z.of_N (encode source).(MonadVM.Vm.Make.MachineState.t.gas)) ->
    (forall source result next,
      native_dispatch source = (result, next) ->
      generated_dispatch_step (encode source) = (result, encode next)) ->
    (Z.of_N (encode state).(MonadVM.Vm.Make.MachineState.t.gas)
      < 2 ^ 63)%Z ->
    exists result next,
      @native_run_fuel NativeState MonadVM.Evmc.Result.StatusCode.t
        native_gas native_dispatch
        (S (N.to_nat (encode state).(MonadVM.Vm.Make.MachineState.t.gas)))
        state = Some (inl (result, next)) /\
      @model_run_fuel State MonadVM.Evmc.Result.StatusCode.t
        generated_dispatch_step
        (S (N.to_nat (encode state).(MonadVM.Vm.Make.MachineState.t.gas)))
        (encode state) = Some (result, encode next).
  Proof.
    intros Hrevision Hgas Hdispatch Hbound.
    eapply (@native_run_entry_gas_fuel_corresponds
      NativeState State MonadVM.Evmc.Result.StatusCode.t
      encode native_gas
      (fun current => current.(MonadVM.Vm.Make.MachineState.t.gas))
      native_dispatch generated_dispatch_step).
    - exact Hgas.
    - exact Hdispatch.
    - intros current next Hcurrent_bound Hstep.
      unfold generated_dispatch_step in Hstep.
      pose proof (generated_run_continues current next
        Hrevision Hcurrent_bound Hstep) as [_ Hprogress].
      exact Hprogress.
    - exact Hbound.
  Qed.

  Corollary native_run_generated_result_correspondence
      {NativeState : Type}
      (encode : NativeState -> State)
      (native_gas : NativeState -> Z)
      (native_dispatch : NativeState ->
        (bool + MonadVM.Evmc.Result.StatusCode.t) * NativeState)
      (state : NativeState) :
    ((@MonadVM.Vm.Make.Params Host_t F).(
      MonadVM.Vm.Make_Params_signature.revision) =
        MonadVM.Support.Variants.Revision.Eight \/
     (@MonadVM.Vm.Make.Params Host_t F).(
       MonadVM.Vm.Make_Params_signature.revision) =
        MonadVM.Support.Variants.Revision.Nine) ->
    (forall source,
      native_gas source =
        Z.of_N (encode source).(MonadVM.Vm.Make.MachineState.t.gas)) ->
    (forall source result next,
      native_dispatch source = (result, next) ->
      generated_dispatch_step (encode source) = (result, encode next)) ->
    (Z.of_N (encode state).(MonadVM.Vm.Make.MachineState.t.gas)
      < 2 ^ 63)%Z ->
    exists result next,
      @native_run_fuel NativeState MonadVM.Evmc.Result.StatusCode.t
        native_gas native_dispatch
        (S (N.to_nat (encode state).(MonadVM.Vm.Make.MachineState.t.gas)))
        state = Some (inl (result, next)) /\
      generated_run (encode state) = (result, encode next).
  Proof.
    intros Hrevision Hgas Hdispatch Hbound.
    destruct (native_run_generated_dispatch_correspondence
      encode native_gas native_dispatch state
      Hrevision Hgas Hdispatch Hbound)
      as [result [next [Hnative Hmodel]]].
    exists result, next.
    split; [exact Hnative |].
    rewrite generated_dispatch_fuel_eq in Hmodel.
    pose proof (run_without_guard_entry_fuel (encode state)
      Hrevision Hbound) as Hgenerated.
    rewrite Hgenerated in Hmodel.
    now inversion Hmodel.
  Qed.
End Dispatch.
