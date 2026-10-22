(** Gas progress for generated VM charging and straight-line opcode handlers. *)

From Stdlib Require Import NArith Lia.
Require Import RocqOfOCaml.RocqOfOCaml.
Require MonadVM.Evmc.
Require MonadVM.Gas.
Require MonadVM.Monad.
Require MonadVM.Numeric.
Require MonadVM.Opcode.
Require MonadVM.Support.UintN.
Require MonadVM.Support.Variants.
Require MonadVM.Vm.

Local Open Scope N_scope.

Section GasBind.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.

  Let State := @MonadVM.Vm.Make.MachineState.t Host_t F.
  Let gas (state : State) : N :=
    state.(MonadVM.Vm.Make.MachineState.t.gas).

  Definition gas_nonincreasing {A : Set}
      (action : @MonadVM.Vm.Make.M.t Host_t F A) : Prop :=
    forall state value next,
      action state =
        ((inl value : sum A MonadVM.Evmc.Result.StatusCode.t), next) ->
      gas next <= gas state.

  Definition gas_decreasing {A : Set}
      (action : @MonadVM.Vm.Make.M.t Host_t F A) : Prop :=
    forall state value next,
      action state =
        ((inl value : sum A MonadVM.Evmc.Result.StatusCode.t), next) ->
      gas next < gas state.

  Lemma read_lens_nonincreasing {A : Set}
      (lens : Lens.t State A) :
    gas_nonincreasing
      (@MonadVM.Vm.Make.M.op_exclamation Host_t F A lens).
  Proof.
    intros state value next Hsuccess.
    assert (Hgas :
      gas (snd (@MonadVM.Vm.Make.M.op_exclamation
        Host_t F A lens state)) = gas state) by reflexivity.
    rewrite Hsuccess in Hgas.
    cbn in Hgas.
    lia.
  Qed.

  Lemma pure_read_nonincreasing {A : Set} (read : State -> A) :
    gas_nonincreasing
      (fun state =>
        ((inl (read state) : sum A MonadVM.Evmc.Result.StatusCode.t),
          state)).
  Proof.
    intros state value next Hsuccess.
    inversion Hsuccess; subst next.
    lia.
  Qed.

  Lemma host_lift_preserves_gas {A : Set}
      (host_action : Host_t -> A * Host_t) (state : State) :
    gas (snd (@MonadVM.Vm.Make.M.HostAPI.lift Host_t F A
      host_action state)) = gas state.
  Proof.
    unfold MonadVM.Vm.Make.M.HostAPI.lift.
    destruct (host_action state.(MonadVM.Vm.Make.MachineState.t.host)).
    reflexivity.
  Qed.

  Lemma host_lift_nonincreasing {A : Set}
      (host_action : Host_t -> A * Host_t) :
    gas_nonincreasing
      (@MonadVM.Vm.Make.M.HostAPI.lift Host_t F A host_action).
  Proof.
    intros state value next Hsuccess.
    pose proof (host_lift_preserves_gas host_action state) as Hgas.
    rewrite Hsuccess in Hgas.
    cbn in Hgas.
    lia.
  Qed.

  Lemma return_nonincreasing {A : Set} (value : A) :
    gas_nonincreasing
      (@MonadVM.Vm.Make.M._return Host_t F A value).
  Proof.
    intros state result next Hsuccess.
    cbn in Hsuccess.
    inversion Hsuccess; subst next.
    lia.
  Qed.

  Lemma fail_nonincreasing {A : Set}
      (error : MonadVM.Evmc.Result.StatusCode.t) :
    gas_nonincreasing
      (@MonadVM.Vm.Make.M.fail Host_t F A error).
  Proof.
    intros state result next Hsuccess.
    discriminate Hsuccess.
  Qed.

  Lemma bind_success_decompose {A B : Set}
      (first : @MonadVM.Vm.Make.M.t Host_t F A)
      (second : A -> @MonadVM.Vm.Make.M.t Host_t F B)
      (state : State) (value : B) (next : State) :
    @MonadVM.Vm.Make.M.op_letdollar Host_t F A B first second state =
      ((inl value : sum B MonadVM.Evmc.Result.StatusCode.t), next) ->
    exists intermediate_state intermediate_value,
      first state =
        ((inl intermediate_value :
          sum A MonadVM.Evmc.Result.StatusCode.t), intermediate_state) /\
      second intermediate_value intermediate_state =
        ((inl value : sum B MonadVM.Evmc.Result.StatusCode.t), next).
  Proof.
    intro Hsuccess.
    change (match first state with
      | (inl intermediate_value, intermediate_state) =>
          second intermediate_value intermediate_state
      | (inr error, intermediate_state) =>
          (inr error, intermediate_state)
      end = (inl value, next)) in Hsuccess.
    destruct (first state) as [[intermediate_value | error]
      intermediate_state] eqn:Hfirst.
    - exists intermediate_state, intermediate_value.
      cbn in Hsuccess.
      split; [reflexivity | exact Hsuccess].
    - discriminate Hsuccess.
  Qed.

  Lemma bind_decrease_after_preserve {A B : Set}
      (first : @MonadVM.Vm.Make.M.t Host_t F A)
      (second : A -> @MonadVM.Vm.Make.M.t Host_t F B) :
    gas_nonincreasing first ->
    (forall value, gas_decreasing (second value)) ->
    gas_decreasing
      (@MonadVM.Vm.Make.M.op_letdollar Host_t F A B first second).
  Proof.
    intros Hfirst Hsecond state value next Hsuccess.
    destruct (bind_success_decompose first second state value next Hsuccess)
      as [middle [intermediate [Hleft Hright]]].
    unfold gas_nonincreasing in Hfirst.
    unfold gas_decreasing in Hsecond.
    specialize (Hfirst _ _ _ Hleft).
    specialize (Hsecond intermediate _ _ _ Hright).
    lia.
  Qed.

  Lemma bind_decrease_after_preserve_if {A B : Set}
      (first : @MonadVM.Vm.Make.M.t Host_t F A)
      (second : A -> @MonadVM.Vm.Make.M.t Host_t F B)
      (valid : A -> Prop) :
    gas_nonincreasing first ->
    (forall state value next,
      first state =
        ((inl value : sum A MonadVM.Evmc.Result.StatusCode.t), next) ->
      valid value) ->
    (forall value, valid value -> gas_decreasing (second value)) ->
    gas_decreasing
      (@MonadVM.Vm.Make.M.op_letdollar Host_t F A B first second).
  Proof.
    intros Hfirst Hvalid Hsecond state result next Hsuccess.
    destruct (bind_success_decompose first second state result next Hsuccess)
      as [middle [intermediate [Hleft Hright]]].
    pose proof (Hfirst state intermediate middle Hleft) as Hnonincreasing.
    pose proof (Hvalid state intermediate middle Hleft) as Hproperty.
    pose proof (Hsecond intermediate Hproperty middle result next Hright)
      as Hdecreasing.
    lia.
  Qed.

  Lemma bind_nonincreasing {A B : Set}
      (first : @MonadVM.Vm.Make.M.t Host_t F A)
      (second : A -> @MonadVM.Vm.Make.M.t Host_t F B) :
    gas_nonincreasing first ->
    (forall value, gas_nonincreasing (second value)) ->
    gas_nonincreasing
      (@MonadVM.Vm.Make.M.op_letdollar Host_t F A B first second).
  Proof.
    intros Hfirst Hsecond state value next Hsuccess.
    destruct (bind_success_decompose first second state value next Hsuccess)
      as [middle [intermediate [Hleft Hright]]].
    unfold gas_nonincreasing in *.
    specialize (Hfirst _ _ _ Hleft).
    specialize (Hsecond intermediate _ _ _ Hright).
    lia.
  Qed.

  Lemma list_fold_leftM_nonincreasing {Acc Elem : Set}
      (step : Acc -> Elem -> @MonadVM.Vm.Make.M.t Host_t F Acc)
      (items : list Elem) :
    (forall current item, gas_nonincreasing (step current item)) ->
    forall initial,
      gas_nonincreasing
        (@MonadVM.Vm.Make.M.List.fold_leftM
          Host_t F Acc Elem step initial items).
  Proof.
    intro Hstep.
    induction items as [| item rest IH]; intro initial.
    - change (gas_nonincreasing
        (@MonadVM.Vm.Make.M._return Host_t F Acc initial)).
      apply return_nonincreasing.
    - change (gas_nonincreasing
        (@MonadVM.Vm.Make.M.op_letdollar Host_t F Acc Acc
          (step initial item)
          (fun next => @MonadVM.Vm.Make.M.List.fold_leftM
            Host_t F Acc Elem step next rest))).
      apply bind_nonincreasing.
      + apply Hstep.
      + intro next. apply IH.
  Qed.

  Lemma map_nonincreasing {A B : Set}
      (f : A -> B) (action : @MonadVM.Vm.Make.M.t Host_t F A) :
    gas_nonincreasing action ->
    gas_nonincreasing
      (@MonadVM.Vm.Make.M.op_ltdollargt Host_t F A B f action).
  Proof.
    intro Haction.
    change (gas_nonincreasing
      (@MonadVM.Vm.Make.M.op_letdollar Host_t F A B
        action (fun value => @MonadVM.Vm.Make.M._return Host_t F B
          (f value)))).
    apply bind_nonincreasing.
    - exact Haction.
    - intro value. apply return_nonincreasing.
  Qed.

  Lemma map_success_value {A B : Set}
      (f : A -> B) (action : @MonadVM.Vm.Make.M.t Host_t F A)
      (state : State) (result : B) (next : State) :
    @MonadVM.Vm.Make.M.op_ltdollargt Host_t F A B f action state =
      ((inl result : sum B MonadVM.Evmc.Result.StatusCode.t), next) ->
    exists original,
      action state =
        ((inl original : sum A MonadVM.Evmc.Result.StatusCode.t), next) /\
      result = f original.
  Proof.
    intro Hsuccess.
    change (@MonadVM.Vm.Make.M.op_letdollar Host_t F A B action
      (fun value => @MonadVM.Vm.Make.M._return Host_t F B (f value))
      state = (inl result, next)) in Hsuccess.
    destruct (bind_success_decompose action
      (fun value => @MonadVM.Vm.Make.M._return Host_t F B (f value))
      state result next Hsuccess) as [middle [original [Hleft Hright]]].
    cbn in Hright.
    inversion Hright; subst.
    exists original. split; [exact Hleft | reflexivity].
  Qed.

  Lemma fmap_nonincreasing {A B : Set}
      (f : A -> B) (action : @MonadVM.Vm.Make.M.t Host_t F A) :
    gas_nonincreasing action ->
    gas_nonincreasing
      (@MonadVM.Vm.Make.M.fmap Host_t F A B f action).
  Proof.
    intros Haction state value next Hsuccess.
    unfold MonadVM.Vm.Make.M.fmap in Hsuccess.
    cbn in Hsuccess.
    destruct (action state) as [[original | error] middle] eqn:Hfirst;
      cbn in Hsuccess.
    - inversion Hsuccess; subst next.
      eapply Haction; exact Hfirst.
    - discriminate Hsuccess.
  Qed.

  Lemma option_or_fail_nonincreasing {A : Set}
      (error : MonadVM.Evmc.Result.StatusCode.t)
      (choice : option A) :
    gas_nonincreasing
      (@MonadVM.Vm.Make.M.Option.or_fail Host_t F A error choice).
  Proof.
    destruct choice as [chosen | ];
      intros state value next Hsuccess; cbn in Hsuccess.
    - inversion Hsuccess; subst next; lia.
    - discriminate Hsuccess.
  Qed.

  Lemma gtgteq_nonincreasing {A B : Set}
      (first : @MonadVM.Vm.Make.M.t Host_t F A)
      (second : A -> @MonadVM.Vm.Make.M.t Host_t F B) :
    gas_nonincreasing first ->
    (forall value, gas_nonincreasing (second value)) ->
    gas_nonincreasing
      (@MonadVM.Vm.Make.M.op_gtgteq Host_t F A B first second).
  Proof.
    intros Hfirst Hsecond state value next Hsuccess.
    unfold MonadVM.Vm.Make.M.op_gtgteq in Hsuccess.
    cbn in Hsuccess.
    destruct (first state) as [[original | error] middle] eqn:Hleft;
      cbn in Hsuccess.
    - specialize (Hfirst _ _ _ Hleft).
      specialize (Hsecond original _ _ _ Hsuccess).
      unfold gas_nonincreasing in *.
      lia.
    - discriminate Hsuccess.
  Qed.

  Lemma bind_decrease_before_preserve {A B : Set}
      (first : @MonadVM.Vm.Make.M.t Host_t F A)
      (second : A -> @MonadVM.Vm.Make.M.t Host_t F B) :
    gas_decreasing first ->
    (forall value, gas_nonincreasing (second value)) ->
    gas_decreasing
      (@MonadVM.Vm.Make.M.op_letdollar Host_t F A B first second).
  Proof.
    intros Hfirst Hsecond state value next Hsuccess.
    destruct (bind_success_decompose first second state value next Hsuccess)
      as [middle [intermediate [Hleft Hright]]].
    unfold gas_decreasing in Hfirst.
    unfold gas_nonincreasing in Hsecond.
    specialize (Hfirst _ _ _ Hleft).
    specialize (Hsecond intermediate _ _ _ Hright).
    lia.
  Qed.
End GasBind.

Section Spend.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context `{U : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.

  Let State := @MonadVM.Vm.Make.MachineState.t Host_t F.

  Lemma spend_success_decreases (amount : N) (state next : State) :
    0 < amount ->
    @MonadVM.Vm.Make.spend Host_t F U amount state =
      ((inl tt : sum unit MonadVM.Evmc.Result.StatusCode.t), next) ->
    next.(MonadVM.Vm.Make.MachineState.t.gas) <
      state.(MonadVM.Vm.Make.MachineState.t.gas).
  Proof.
    intros Hpositive Hsuccess.
    unfold MonadVM.Vm.Make.spend in Hsuccess.
    unfold MonadVM.Gas.op_lt, MonadVM.Support.UintN.op_lt in Hsuccess.
    destruct (N.ltb state.(MonadVM.Vm.Make.MachineState.t.gas) amount)
      eqn:Hlt.
    - discriminate Hsuccess.
    - apply N.ltb_ge in Hlt.
      unfold MonadVM.Gas.op_minus,
        MonadVM.Support.UintN.op_minus in Hsuccess.
      assert (Hge : N.leb amount
        state.(MonadVM.Vm.Make.MachineState.t.gas) = true).
      { apply N.leb_le. lia. }
      rewrite Hge in Hsuccess.
      inversion Hsuccess; subst next.
      cbn [MonadVM.Vm.Make.MachineState.t.gas
        MonadVM.Vm.Make.MachineState.t.with_gas].
      lia.
  Qed.

  Lemma spend_positive_decreasing (amount : N) :
    0 < amount ->
    gas_decreasing (@MonadVM.Vm.Make.spend Host_t F U amount).
  Proof.
    intros Hpositive state [] next Hsuccess.
    eapply spend_success_decreases; eassumption.
  Qed.

  Lemma spend_then_preserving_decreases {A : Set} (amount : N)
      (continuation : unit -> @MonadVM.Vm.Make.M.t Host_t F A) :
    0 < amount ->
    (forall value, gas_nonincreasing (continuation value)) ->
    gas_decreasing
      (@MonadVM.Vm.Make.M.op_letdollar Host_t F unit A
        (@MonadVM.Vm.Make.spend Host_t F U amount) continuation).
  Proof.
    intros Hpositive Hcontinuation.
    eapply bind_decrease_before_preserve.
    - apply spend_positive_decreasing. exact Hpositive.
    - exact Hcontinuation.
  Qed.

  Lemma push_preserves_gas (value : MonadVM.Numeric.U256.t)
      (state : State) :
    (snd (@MonadVM.Vm.Make.push Host_t F value state)).(
      MonadVM.Vm.Make.MachineState.t.gas) =
    state.(MonadVM.Vm.Make.MachineState.t.gas).
  Proof.
    unfold MonadVM.Vm.Make.push.
    destruct (Z.geb state.(MonadVM.Vm.Make.MachineState.t.stack_depth)
      MonadVM.Vm.Make.max_stack_depth); reflexivity.
  Qed.

  Lemma pop_preserves_gas (state : State) :
    (snd (@MonadVM.Vm.Make.pop Host_t F state)).(
      MonadVM.Vm.Make.MachineState.t.gas) =
    state.(MonadVM.Vm.Make.MachineState.t.gas).
  Proof.
    unfold MonadVM.Vm.Make.pop.
    destruct state.(MonadVM.Vm.Make.MachineState.t.stack); reflexivity.
  Qed.

  Lemma pop2_preserves_gas (state : State) :
    (snd (@MonadVM.Vm.Make.pop2 Host_t F state)).(
      MonadVM.Vm.Make.MachineState.t.gas) =
    state.(MonadVM.Vm.Make.MachineState.t.gas).
  Proof.
    unfold MonadVM.Vm.Make.pop2.
    destruct state.(MonadVM.Vm.Make.MachineState.t.stack)
      as [| first [| second rest]]; reflexivity.
  Qed.

  Lemma pop3_preserves_gas (state : State) :
    (snd (@MonadVM.Vm.Make.pop3 Host_t F state)).(
      MonadVM.Vm.Make.MachineState.t.gas) =
    state.(MonadVM.Vm.Make.MachineState.t.gas).
  Proof.
    unfold MonadVM.Vm.Make.pop3.
    destruct state.(MonadVM.Vm.Make.MachineState.t.stack)
      as [| first [| second [| third rest]]]; reflexivity.
  Qed.

  Lemma pop_nonincreasing :
    gas_nonincreasing (@MonadVM.Vm.Make.pop Host_t F).
  Proof.
    intros state value next Hsuccess.
    pose proof (pop_preserves_gas state) as Hgas.
    rewrite Hsuccess in Hgas.
    cbn in Hgas.
    lia.
  Qed.

  Lemma pop2_nonincreasing :
    gas_nonincreasing (@MonadVM.Vm.Make.pop2 Host_t F).
  Proof.
    intros state value next Hsuccess.
    pose proof (pop2_preserves_gas state) as Hgas.
    rewrite Hsuccess in Hgas.
    cbn in Hgas.
    lia.
  Qed.

  Lemma pop3_nonincreasing :
    gas_nonincreasing (@MonadVM.Vm.Make.pop3 Host_t F).
  Proof.
    intros state value next Hsuccess.
    pose proof (pop3_preserves_gas state) as Hgas.
    rewrite Hsuccess in Hgas.
    cbn in Hgas.
    lia.
  Qed.

  Lemma push_nonincreasing (value : MonadVM.Numeric.U256.t) :
    gas_nonincreasing (@MonadVM.Vm.Make.push Host_t F value).
  Proof.
    intros state [] next Hsuccess.
    pose proof (push_preserves_gas value state) as Hgas.
    rewrite Hsuccess in Hgas.
    cbn in Hgas.
    lia.
  Qed.

  Lemma write_stack_preserves_gas
      (stack : list MonadVM.Numeric.U256.t) (state : State) :
    (snd (@MonadVM.Vm.Make.M.op_coloneq Host_t F _
      (@MonadVM.Vm.Make.MachineState.stack Host_t F) stack state)).(
      MonadVM.Vm.Make.MachineState.t.gas) =
    state.(MonadVM.Vm.Make.MachineState.t.gas).
  Proof. reflexivity. Qed.

  Lemma write_stack_nonincreasing
      (stack : list MonadVM.Numeric.U256.t) :
    gas_nonincreasing
      (@MonadVM.Vm.Make.M.op_coloneq Host_t F _
        (@MonadVM.Vm.Make.MachineState.stack Host_t F) stack).
  Proof.
    intros state [] next Hsuccess.
    pose proof (write_stack_preserves_gas stack state) as Hgas.
    rewrite Hsuccess in Hgas.
    cbn in Hgas.
    lia.
  Qed.

  Lemma spend_then_push_decreases (amount : N)
      (value : MonadVM.Numeric.U256.t) :
    0 < amount ->
    gas_decreasing
      (@MonadVM.Vm.Make.M.op_letdollar Host_t F unit unit
        (@MonadVM.Vm.Make.spend Host_t F U amount)
        (fun _ => @MonadVM.Vm.Make.push Host_t F value)).
  Proof.
    intro Hpositive.
    apply spend_then_preserving_decreases; [exact Hpositive |].
    intros []. apply push_nonincreasing.
  Qed.

  Lemma read_gas_preserves_gas (state : State) :
    (snd (@MonadVM.Vm.Make.M.op_exclamation Host_t F N
      (@MonadVM.Vm.Make.MachineState.gas Host_t F) state)).(
      MonadVM.Vm.Make.MachineState.t.gas) =
    state.(MonadVM.Vm.Make.MachineState.t.gas).
  Proof. reflexivity. Qed.

  Lemma read_gas_nonincreasing :
    gas_nonincreasing
      (@MonadVM.Vm.Make.M.op_exclamation Host_t F N
        (@MonadVM.Vm.Make.MachineState.gas Host_t F)).
  Proof.
    intros state value next Hsuccess.
    pose proof (read_gas_preserves_gas state) as Hgas.
    rewrite Hsuccess in Hgas.
    cbn in Hgas.
    lia.
  Qed.

  Context `{U256 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.

  Lemma increase_pc_preserves_gas (state : State) :
    (snd (@MonadVM.Vm.Make.increase_pc_and_continue
      Host_t F U256 state)).(MonadVM.Vm.Make.MachineState.t.gas) =
      state.(MonadVM.Vm.Make.MachineState.t.gas).
  Proof. reflexivity. Qed.

  Lemma increase_pc_nonincreasing :
    gas_nonincreasing
      (@MonadVM.Vm.Make.increase_pc_and_continue Host_t F U256).
  Proof.
    intros state value next Hsuccess.
    pose proof (increase_pc_preserves_gas state) as Hgas.
    rewrite Hsuccess in Hgas.
    cbn in Hgas.
    lia.
  Qed.

  Lemma update_pc_preserves_gas
      (update : MonadVM.Numeric.U256.t -> MonadVM.Numeric.U256.t)
      (state : State) :
    (snd (@MonadVM.Vm.Make.update_pc_and_continue
      Host_t F update state)).(MonadVM.Vm.Make.MachineState.t.gas) =
      state.(MonadVM.Vm.Make.MachineState.t.gas).
  Proof. reflexivity. Qed.

  Lemma update_pc_nonincreasing
      (update : MonadVM.Numeric.U256.t -> MonadVM.Numeric.U256.t) :
    gas_nonincreasing
      (@MonadVM.Vm.Make.update_pc_and_continue Host_t F update).
  Proof.
    intros state value next Hsuccess.
    pose proof (update_pc_preserves_gas update state) as Hgas.
    rewrite Hsuccess in Hgas.
    cbn in Hgas.
    lia.
  Qed.

  Lemma base_positive : 0 < MonadVM.Gas.base.
  Proof. vm_compute. reflexivity. Qed.

  Lemma very_low_positive : 0 < MonadVM.Gas.very_low.
  Proof. vm_compute. reflexivity. Qed.

  Lemma low_positive : 0 < MonadVM.Gas.low.
  Proof. vm_compute. reflexivity. Qed.

  Lemma mid_positive : 0 < MonadVM.Gas.mid.
  Proof. vm_compute. reflexivity. Qed.

  Lemma high_positive : 0 < MonadVM.Gas.high.
  Proof. vm_compute. reflexivity. Qed.

  Lemma jumpdest_positive : 0 < MonadVM.Gas.jumpdest.
  Proof. vm_compute. reflexivity. Qed.

  Lemma positive_charge_plus (base extra : N) :
    0 < base -> 0 < @MonadVM.Gas.op_plus U base extra.
  Proof.
    unfold MonadVM.Gas.op_plus, MonadVM.Support.UintN.op_plus.
    lia.
  Qed.

  Lemma keccak_base_positive :
    0 < MonadVM.Gas.keccak256_base_cost.
  Proof. vm_compute. reflexivity. Qed.

  Lemma block_hash_cost_positive :
    0 < MonadVM.Gas.block_hash_cost.
  Proof. vm_compute. reflexivity. Qed.

  Lemma log_cost_positive : 0 < MonadVM.Gas.log_cost.
  Proof. vm_compute. reflexivity. Qed.
End Spend.

Section PopOpcode.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
  Context `{U256 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.

  Let State := @MonadVM.Vm.Make.MachineState.t Host_t F.

  Lemma pop_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.pop_ Host_t F E U256 Ugas).
  Proof.
    unfold MonadVM.Vm.Make.Executor.pop_.
    eapply bind_decrease_after_preserve.
    - apply pop_nonincreasing.
    - intro popped.
      cbn.
      eapply spend_then_preserving_decreases.
      + apply base_positive.
      + intros []. apply increase_pc_nonincreasing.
  Qed.

  Lemma pop_opcode_success_decreases (state next : State) :
    @MonadVM.Vm.Make.Executor.pop_ Host_t F E U256 Ugas state =
      ((inl true : sum bool MonadVM.Evmc.Result.StatusCode.t), next) ->
    next.(MonadVM.Vm.Make.MachineState.t.gas) <
      state.(MonadVM.Vm.Make.MachineState.t.gas).
  Proof.
    apply pop_opcode_compositional_decreasing.
  Qed.
End PopOpcode.

Section GasOpcode.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
  Context `{U256 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
  Context `{Uconv : RocqOfOCaml.Basics.Unreachable
    (Z.t -> MonadVM.Numeric.U256.t)}.

  Let State := @MonadVM.Vm.Make.MachineState.t Host_t F.

  Lemma gas_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.gas_ Host_t F E U256 Ugas Uconv).
  Proof.
    unfold MonadVM.Vm.Make.Executor.gas_.
    eapply spend_then_preserving_decreases.
    - apply base_positive.
    - intros [].
      eapply bind_nonincreasing.
      + apply read_gas_nonincreasing.
      + intro current_gas.
        eapply bind_nonincreasing.
        * apply push_nonincreasing.
        * intros []. apply increase_pc_nonincreasing.
  Qed.

  Lemma gas_opcode_success_decreases (state next : State) :
    @MonadVM.Vm.Make.Executor.gas_ Host_t F E U256 Ugas Uconv state =
      ((inl true : sum bool MonadVM.Evmc.Result.StatusCode.t), next) ->
    next.(MonadVM.Vm.Make.MachineState.t.gas) <
      state.(MonadVM.Vm.Make.MachineState.t.gas).
  Proof.
    apply gas_opcode_compositional_decreasing.
  Qed.
End GasOpcode.

Section EnvironmentOpcode.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
  Context `{U256 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.

  Lemma environment_value_compositional_decreasing
      (value : MonadVM.Numeric.U256.t) :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.fetch_environment_variable_opcode_impl
        Host_t F E U256 Ugas value).
  Proof.
    unfold MonadVM.Vm.Make.Executor.fetch_environment_variable_opcode_impl.
    eapply spend_then_preserving_decreases.
    - apply base_positive.
    - intros [].
      eapply bind_nonincreasing.
      + apply push_nonincreasing.
      + intros []. apply increase_pc_nonincreasing.
  Qed.

  Lemma environment_action_compositional_decreasing
      (value : @MonadVM.Vm.Make.M.t Host_t F MonadVM.Numeric.U256.t) :
    gas_nonincreasing value ->
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.fetch_environment_variable_opcode_impl'
        Host_t F E U256 Ugas value).
  Proof.
    intro Hvalue.
    unfold MonadVM.Vm.Make.Executor.fetch_environment_variable_opcode_impl'.
    eapply spend_then_preserving_decreases.
    - apply base_positive.
    - intros [].
      eapply bind_nonincreasing.
      + exact Hvalue.
      + intro fetched.
        eapply bind_nonincreasing.
        * apply push_nonincreasing.
        * intros []. apply increase_pc_nonincreasing.
  Qed.

  Lemma callvalue_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.callvalue Host_t F E U256 Ugas).
  Proof.
    unfold MonadVM.Vm.Make.Executor.callvalue.
    apply environment_value_compositional_decreasing.
  Qed.

  Lemma calldatasize_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.calldatasize Host_t F E U256 Ugas).
  Proof.
    unfold MonadVM.Vm.Make.Executor.calldatasize.
    apply environment_value_compositional_decreasing.
  Qed.

  Lemma codesize_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.codesize Host_t F E U256 Ugas).
  Proof.
    unfold MonadVM.Vm.Make.Executor.codesize.
    apply environment_value_compositional_decreasing.
  Qed.

  Lemma gasprice_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.gasprice Host_t F E U256 Ugas).
  Proof.
    unfold MonadVM.Vm.Make.Executor.gasprice.
    apply environment_value_compositional_decreasing.
  Qed.

  Lemma timestamp_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.timestamp Host_t F E U256 Ugas).
  Proof.
    unfold MonadVM.Vm.Make.Executor.timestamp.
    apply environment_value_compositional_decreasing.
  Qed.

  Lemma number_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.number Host_t F E U256 Ugas).
  Proof.
    unfold MonadVM.Vm.Make.Executor.number.
    apply environment_value_compositional_decreasing.
  Qed.

  Lemma prevrandao_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.prevrandao Host_t F E U256 Ugas).
  Proof.
    unfold MonadVM.Vm.Make.Executor.prevrandao.
    apply environment_value_compositional_decreasing.
  Qed.

  Lemma gaslimit_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.gaslimit Host_t F E U256 Ugas).
  Proof.
    unfold MonadVM.Vm.Make.Executor.gaslimit.
    apply environment_value_compositional_decreasing.
  Qed.

  Lemma chainid_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.chainid Host_t F E U256 Ugas).
  Proof.
    unfold MonadVM.Vm.Make.Executor.chainid.
    apply environment_value_compositional_decreasing.
  Qed.

  Lemma basefee_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.basefee Host_t F E U256 Ugas).
  Proof.
    unfold MonadVM.Vm.Make.Executor.basefee.
    apply environment_value_compositional_decreasing.
  Qed.

  Lemma pc_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.pc_ Host_t F E U256 Ugas).
  Proof.
    unfold MonadVM.Vm.Make.Executor.pc_.
    apply environment_action_compositional_decreasing.
    apply read_lens_nonincreasing.
  Qed.

  Lemma returndatasize_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.returndatasize
        Host_t F E U256 Ugas).
  Proof.
    unfold MonadVM.Vm.Make.Executor.returndatasize.
    apply environment_action_compositional_decreasing.
    apply map_nonincreasing.
    apply map_nonincreasing.
    apply read_lens_nonincreasing.
  Qed.
End EnvironmentOpcode.

Section MemorySizeOpcode.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{Uuint :
    RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}.
  Context `{U256 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
  Context `{Uconvert : RocqOfOCaml.Basics.Unreachable
    (Z.t -> MonadVM.Numeric.U256.t)}.

  Lemma msize_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.msize
        Host_t F E Uuint U256 Ugas Uconvert).
  Proof.
    unfold MonadVM.Vm.Make.Executor.msize.
    apply environment_action_compositional_decreasing.
    eapply bind_nonincreasing.
    - apply read_lens_nonincreasing.
    - intro memory. apply return_nonincreasing.
  Qed.
End MemorySizeOpcode.

Section AddressEnvironmentOpcode.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
  Context `{U256 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
  Context `{Ustring : RocqOfOCaml.Basics.Unreachable string}.
  Context `{Uint : RocqOfOCaml.Basics.Unreachable int}.
  Context `{Uascii : RocqOfOCaml.Basics.Unreachable ascii}.

  Lemma address_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.address Host_t F E
        U256 Ugas Ustring Uint Uascii).
  Proof.
    unfold MonadVM.Vm.Make.Executor.address.
    apply environment_value_compositional_decreasing.
  Qed.

  Lemma origin_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.origin Host_t F E
        U256 Ugas Ustring Uint Uascii).
  Proof.
    unfold MonadVM.Vm.Make.Executor.origin.
    apply environment_value_compositional_decreasing.
  Qed.

  Lemma caller_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.caller Host_t F E
        U256 Ugas Ustring Uint Uascii).
  Proof.
    unfold MonadVM.Vm.Make.Executor.caller.
    apply environment_value_compositional_decreasing.
  Qed.

  Lemma coinbase_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.coinbase Host_t F E
        U256 Ugas Ustring Uint Uascii).
  Proof.
    unfold MonadVM.Vm.Make.Executor.coinbase.
    apply environment_value_compositional_decreasing.
  Qed.
End AddressEnvironmentOpcode.

Section StackArithmeticOpcode.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
  Context `{U256 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.

  Let Word := MonadVM.Numeric.U256.t.

  Lemma binary_stack_opcode_decreasing (amount : N)
      (calculate : Word -> Word -> Word) :
    0 < amount ->
    gas_decreasing
      (MonadVM.Vm.Make.M.op_letdollar
        MonadVM.Vm.Make.pop2
        (fun words =>
          let '(x_value, y_value) := words in
          MonadVM.Vm.Make.M.op_letdollar
            (MonadVM.Vm.Make.spend amount)
            (fun _ => MonadVM.Vm.Make.M.op_letdollar
              (MonadVM.Vm.Make.push (calculate x_value y_value))
              (fun _ => MonadVM.Vm.Make.increase_pc_and_continue)))).
  Proof.
    intros Hpositive.
    eapply bind_decrease_after_preserve.
    - apply pop2_nonincreasing.
    - intros [x_value y_value].
      eapply spend_then_preserving_decreases.
      + exact Hpositive.
      + intros [].
        eapply bind_nonincreasing.
        * apply push_nonincreasing.
        * intros []. apply increase_pc_nonincreasing.
  Qed.

  Lemma add_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.add Host_t F E U256 Ugas).
  Proof.
    unfold MonadVM.Vm.Make.Executor.add.
    apply binary_stack_opcode_decreasing.
    apply very_low_positive.
  Qed.

  Lemma mul_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.mul Host_t F E U256 Ugas).
  Proof.
    unfold MonadVM.Vm.Make.Executor.mul.
    apply binary_stack_opcode_decreasing.
    apply low_positive.
  Qed.

  Lemma sub_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.sub Host_t F E U256 Ugas).
  Proof.
    unfold MonadVM.Vm.Make.Executor.sub.
    apply binary_stack_opcode_decreasing.
    apply very_low_positive.
  Qed.

  Lemma udiv_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.udiv Host_t F E U256 Ugas).
  Proof.
    unfold MonadVM.Vm.Make.Executor.udiv.
    apply binary_stack_opcode_decreasing.
    apply low_positive.
  Qed.

  Lemma umod_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.umod Host_t F E U256 Ugas).
  Proof.
    unfold MonadVM.Vm.Make.Executor.umod.
    apply binary_stack_opcode_decreasing.
    apply low_positive.
  Qed.

  Lemma ternary_stack_opcode_decreasing (amount : N)
      (calculate : Word -> Word -> Word -> Word) :
    0 < amount ->
    gas_decreasing
      (MonadVM.Vm.Make.M.op_letdollar
        MonadVM.Vm.Make.pop3
        (fun words =>
          let '(x_value, y_value, z_value) := words in
          MonadVM.Vm.Make.M.op_letdollar
            (MonadVM.Vm.Make.spend amount)
            (fun _ => MonadVM.Vm.Make.M.op_letdollar
              (MonadVM.Vm.Make.push
                (calculate x_value y_value z_value))
              (fun _ => MonadVM.Vm.Make.increase_pc_and_continue)))).
  Proof.
    intros Hpositive.
    eapply bind_decrease_after_preserve.
    - apply pop3_nonincreasing.
    - intros [[x_value y_value] z_value].
      eapply spend_then_preserving_decreases.
      + exact Hpositive.
      + intros [].
        eapply bind_nonincreasing.
        * apply push_nonincreasing.
        * intros []. apply increase_pc_nonincreasing.
  Qed.

  Lemma addmod_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.addmod Host_t F E U256 Ugas).
  Proof.
    unfold MonadVM.Vm.Make.Executor.addmod.
    apply ternary_stack_opcode_decreasing.
    apply mid_positive.
  Qed.

  Lemma mulmod_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.mulmod Host_t F E U256 Ugas).
  Proof.
    unfold MonadVM.Vm.Make.Executor.mulmod.
    apply ternary_stack_opcode_decreasing.
    apply mid_positive.
  Qed.

  Lemma lt_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.lt Host_t F E U256 Ugas).
  Proof.
    unfold MonadVM.Vm.Make.Executor.lt.
    apply binary_stack_opcode_decreasing.
    apply very_low_positive.
  Qed.

  Lemma gt_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.gt Host_t F E U256 Ugas).
  Proof.
    unfold MonadVM.Vm.Make.Executor.gt.
    apply binary_stack_opcode_decreasing.
    apply very_low_positive.
  Qed.

  Lemma eq_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.eq Host_t F E U256 Ugas).
  Proof.
    unfold MonadVM.Vm.Make.Executor.eq.
    apply binary_stack_opcode_decreasing.
    apply very_low_positive.
  Qed.

  Lemma bitwise_and_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.bitwise_and Host_t F E U256 Ugas).
  Proof.
    unfold MonadVM.Vm.Make.Executor.bitwise_and.
    apply binary_stack_opcode_decreasing.
    apply very_low_positive.
  Qed.

  Lemma bitwise_or_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.bitwise_or Host_t F E U256 Ugas).
  Proof.
    unfold MonadVM.Vm.Make.Executor.bitwise_or.
    apply binary_stack_opcode_decreasing.
    apply very_low_positive.
  Qed.

  Lemma bitwise_xor_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.bitwise_xor Host_t F E U256 Ugas).
  Proof.
    unfold MonadVM.Vm.Make.Executor.bitwise_xor.
    apply binary_stack_opcode_decreasing.
    apply very_low_positive.
  Qed.

  Lemma unary_stack_opcode_decreasing (amount : N)
      (calculate : Word -> Word) :
    0 < amount ->
    gas_decreasing
      (MonadVM.Vm.Make.M.op_letdollar
        MonadVM.Vm.Make.pop
        (fun x_value =>
          MonadVM.Vm.Make.M.op_letdollar
            (MonadVM.Vm.Make.spend amount)
            (fun _ => MonadVM.Vm.Make.M.op_letdollar
              (MonadVM.Vm.Make.push (calculate x_value))
              (fun _ => MonadVM.Vm.Make.increase_pc_and_continue)))).
  Proof.
    intros Hpositive.
    eapply bind_decrease_after_preserve.
    - apply pop_nonincreasing.
    - intro x_value.
      eapply spend_then_preserving_decreases.
      + exact Hpositive.
      + intros [].
        eapply bind_nonincreasing.
        * apply push_nonincreasing.
        * intros []. apply increase_pc_nonincreasing.
  Qed.

  Lemma is_zero_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.is_zero Host_t F E U256 Ugas).
  Proof.
    unfold MonadVM.Vm.Make.Executor.is_zero.
    apply unary_stack_opcode_decreasing.
    apply very_low_positive.
  Qed.

  Lemma bitwise_not_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.bitwise_not Host_t F E U256 Ugas).
  Proof.
    unfold MonadVM.Vm.Make.Executor.bitwise_not.
    apply unary_stack_opcode_decreasing.
    apply very_low_positive.
  Qed.

  Lemma mapped_binary_stack_opcode_decreasing {A : Set}
      (amount : N)
      (convert : Word -> A)
      (calculate : A -> A -> Word) :
    0 < amount ->
    gas_decreasing
      (MonadVM.Vm.Make.M.op_letdollar
        (MonadVM.Vm.Make.M.op_ltdollargt convert MonadVM.Vm.Make.pop)
        (fun x_value =>
          MonadVM.Vm.Make.M.op_letdollar
            (MonadVM.Vm.Make.M.op_ltdollargt convert MonadVM.Vm.Make.pop)
            (fun y_value =>
              MonadVM.Vm.Make.M.op_letdollar
                (MonadVM.Vm.Make.spend amount)
                (fun _ => MonadVM.Vm.Make.M.op_letdollar
                  (MonadVM.Vm.Make.push (calculate x_value y_value))
                  (fun _ => MonadVM.Vm.Make.increase_pc_and_continue))))).
  Proof.
    intro Hpositive.
    eapply bind_decrease_after_preserve.
    - apply map_nonincreasing. apply pop_nonincreasing.
    - intro x_value.
      eapply bind_decrease_after_preserve.
      + apply map_nonincreasing. apply pop_nonincreasing.
      + intro y_value.
        eapply spend_then_preserving_decreases.
        * exact Hpositive.
        * intros [].
          eapply bind_nonincreasing.
          -- apply push_nonincreasing.
          -- intros []. apply increase_pc_nonincreasing.
  Qed.
End StackArithmeticOpcode.

Section SignedComparisonOpcode.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
  Context `{U256 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
  Context `{Usigned : RocqOfOCaml.Basics.Unreachable
    MonadVM.Numeric.Bits256.(
      MonadVM.Numeric.TwosComplement.TwosComplement_result.Signed_t)}.

  Lemma slt_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.slt Host_t F E U256 Ugas Usigned).
  Proof.
    unfold MonadVM.Vm.Make.Executor.slt.
    apply mapped_binary_stack_opcode_decreasing.
    apply very_low_positive.
  Qed.

  Lemma sgt_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.sgt Host_t F E U256 Ugas Usigned).
  Proof.
    unfold MonadVM.Vm.Make.Executor.sgt.
    apply mapped_binary_stack_opcode_decreasing.
    apply very_low_positive.
  Qed.
End SignedComparisonOpcode.

Section SignedArithmeticOpcode.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{U256 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
  Context `{UI256 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.I256.t}.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
  Context `{Uint : RocqOfOCaml.Basics.Unreachable int}.
  Context `{Uunsigned : RocqOfOCaml.Basics.Unreachable
    MonadVM.Numeric.Bits256.(
      MonadVM.Numeric.TwosComplement.TwosComplement_result.U).(
      MonadVM.Numeric.Make.Make_result.t)}.
  Context `{Usigned : RocqOfOCaml.Basics.Unreachable
    MonadVM.Numeric.Bits256.(
      MonadVM.Numeric.TwosComplement.TwosComplement_result.Signed_t)}.

  Lemma sdiv_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.sdiv Host_t F E
        U256 UI256 Ugas Uunsigned Usigned).
  Proof.
    unfold MonadVM.Vm.Make.Executor.sdiv.
    apply mapped_binary_stack_opcode_decreasing.
    apply low_positive.
  Qed.

  Lemma smod_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.smod Host_t F E
        U256 UI256 Ugas Uunsigned Usigned).
  Proof.
    unfold MonadVM.Vm.Make.Executor.smod.
    apply mapped_binary_stack_opcode_decreasing.
    apply low_positive.
  Qed.

  Lemma sar_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.sar Host_t F E
        U256 UI256 Ugas Uint Uunsigned Usigned).
  Proof.
    unfold MonadVM.Vm.Make.Executor.sar.
    eapply bind_decrease_after_preserve.
    - apply pop_nonincreasing.
    - intro shift_amount.
      eapply bind_decrease_after_preserve.
      + apply map_nonincreasing. apply pop_nonincreasing.
      + intro signed_value.
        eapply spend_then_preserving_decreases.
        * apply very_low_positive.
        * intros [].
          eapply bind_nonincreasing.
          -- apply push_nonincreasing.
          -- intros []. apply increase_pc_nonincreasing.
  Qed.
End SignedArithmeticOpcode.

Section SignExtendOpcode.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{UZ : RocqOfOCaml.Basics.Unreachable Z.t}.
  Context `{U256 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
  Context `{Uint : RocqOfOCaml.Basics.Unreachable int}.
  Context `{Uunsigned : RocqOfOCaml.Basics.Unreachable
    MonadVM.Numeric.Bits256.(
      MonadVM.Numeric.TwosComplement.TwosComplement_result.U).(
      MonadVM.Numeric.Make.Make_result.t)}.
  Context `{Usigned : RocqOfOCaml.Basics.Unreachable
    MonadVM.Numeric.Bits256.(
      MonadVM.Numeric.TwosComplement.TwosComplement_result.Signed_t)}.

  Lemma signextend_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.signextend Host_t F E
        UZ U256 Ugas Uint Uunsigned Usigned).
  Proof.
    unfold MonadVM.Vm.Make.Executor.signextend.
    apply binary_stack_opcode_decreasing.
    apply low_positive.
  Qed.
End SignExtendOpcode.

Section ByteAndShiftOpcode.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
  Context `{U256 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
  Context `{Uint : RocqOfOCaml.Basics.Unreachable int}.
  Context `{Uascii : RocqOfOCaml.Basics.Unreachable ascii}.

  Lemma byte_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.byte Host_t F E
        U256 Ugas Uint Uascii).
  Proof.
    unfold MonadVM.Vm.Make.Executor.byte.
    apply binary_stack_opcode_decreasing.
    apply very_low_positive.
  Qed.

  Lemma logical_shift_compositional_decreasing
      (shift_fn : MonadVM.Numeric.U256.t -> int ->
        MonadVM.Numeric.U256.t) :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.logical_shift_opcode_impl
        Host_t F E U256 Ugas Uint shift_fn).
  Proof.
    unfold MonadVM.Vm.Make.Executor.logical_shift_opcode_impl.
    apply binary_stack_opcode_decreasing.
    apply very_low_positive.
  Qed.

  Lemma shl_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.shl Host_t F E U256 Ugas Uint).
  Proof.
    unfold MonadVM.Vm.Make.Executor.shl.
    apply logical_shift_compositional_decreasing.
  Qed.

  Lemma shr_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.shr Host_t F E U256 Ugas Uint).
  Proof.
    unfold MonadVM.Vm.Make.Executor.shr.
    apply logical_shift_compositional_decreasing.
  Qed.
End ByteAndShiftOpcode.

Lemma decoded_push_width (byte : ascii) (width : int) :
  MonadVM.Opcode.of_byte byte = MonadVM.Opcode.Push width ->
  (0 <= width <= 32)%Z.
Proof.
  intro Hdecoded.
  destruct byte as [b0 b1 b2 b3 b4 b5 b6 b7].
  destruct b0, b1, b2, b3, b4, b5, b6, b7;
    cbn in Hdecoded; try discriminate Hdecoded;
    inversion Hdecoded; subst; lia.
Qed.

Lemma decoded_dup_index (byte : ascii) (index : int) :
  MonadVM.Opcode.of_byte byte = MonadVM.Opcode.Dup index ->
  (1 <= index <= 16)%Z.
Proof.
  intro Hdecoded.
  destruct byte as [b0 b1 b2 b3 b4 b5 b6 b7].
  destruct b0, b1, b2, b3, b4, b5, b6, b7;
    cbn in Hdecoded; try discriminate Hdecoded;
    inversion Hdecoded; subst; lia.
Qed.

Lemma decoded_swap_index (byte : ascii) (index : int) :
  MonadVM.Opcode.of_byte byte = MonadVM.Opcode.Swap index ->
  (1 <= index <= 16)%Z.
Proof.
  intro Hdecoded.
  destruct byte as [b0 b1 b2 b3 b4 b5 b6 b7].
  destruct b0, b1, b2, b3, b4, b5, b6, b7;
    cbn in Hdecoded; try discriminate Hdecoded;
    inversion Hdecoded; subst; lia.
Qed.

Lemma decoded_log_topics (byte : ascii) (n_topics : int) :
  MonadVM.Opcode.of_byte byte = MonadVM.Opcode.Log n_topics ->
  (0 <= n_topics <= 4)%Z.
Proof.
  intro Hdecoded.
  destruct byte as [b0 b1 b2 b3 b4 b5 b6 b7].
  destruct b0, b1, b2, b3, b4, b5, b6, b7;
    cbn in Hdecoded; try discriminate Hdecoded;
    inversion Hdecoded; subst; lia.
Qed.

Section PushOpcode.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{Uuint :
    RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}.
  Context `{U256 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
  Context `{Ubytes :
    RocqOfOCaml.Basics.Unreachable MonadVM.Byte_string.Bytes.t}.
  Context `{Uunit : RocqOfOCaml.Basics.Unreachable unit}.
  Context `{Uint : RocqOfOCaml.Basics.Unreachable int}.
  Context `{Uascii : RocqOfOCaml.Basics.Unreachable ascii}.

  Lemma push_opcode_compositional_decreasing (width : int) :
    (0 <= width <= 32)%Z ->
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.push_ Host_t F E
        Uuint U256 Ugas Ubytes Uunit Uint Uascii width).
  Proof.
    intro Hwidth.
    unfold MonadVM.Vm.Make.Executor.push_.
    eapply spend_then_preserving_decreases.
    - destruct (width ==b 0)%Z;
        [apply base_positive | apply very_low_positive].
    - intros [].
      eapply bind_nonincreasing.
      + apply map_nonincreasing. apply read_lens_nonincreasing.
      + intro here.
        eapply bind_nonincreasing.
        * apply push_nonincreasing.
        * intros []. apply update_pc_nonincreasing.
  Qed.

  Lemma decoded_push_opcode_decreasing (byte : ascii) (width : int) :
    MonadVM.Opcode.of_byte byte = MonadVM.Opcode.Push width ->
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.push_ Host_t F E
        Uuint U256 Ugas Ubytes Uunit Uint Uascii width).
  Proof.
    intro Hdecoded.
    apply push_opcode_compositional_decreasing.
    eapply decoded_push_width; exact Hdecoded.
  Qed.
End PushOpcode.

Section StackRearrangementOpcode.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
  Context `{U256 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
  Context `{Uoption_action : RocqOfOCaml.Basics.Unreachable
    (@MonadVM.Vm.Make.M.Option.t Host_t F MonadVM.Numeric.U256.t)}.
  Context `{Uunit : RocqOfOCaml.Basics.Unreachable unit}.
  Context `{Uoption : RocqOfOCaml.Basics.Unreachable
    (option MonadVM.Numeric.U256.t)}.

  Lemma dup_opcode_compositional_decreasing (index : int) :
    (1 <= index <= 16)%Z ->
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.dup Host_t F E
        U256 Ugas Uoption_action Uunit Uoption index).
  Proof.
    intro Hindex.
    unfold MonadVM.Vm.Make.Executor.dup.
    eapply bind_decrease_after_preserve.
    - eapply gtgteq_nonincreasing.
      + apply fmap_nonincreasing. apply read_lens_nonincreasing.
      + intro choice. apply option_or_fail_nonincreasing.
    - intro picked.
      eapply spend_then_preserving_decreases.
      + apply very_low_positive.
      + intros [].
        eapply bind_nonincreasing.
        * apply push_nonincreasing.
        * intros []. apply increase_pc_nonincreasing.
  Qed.

  Lemma swap_opcode_compositional_decreasing (index : int) :
    (1 <= index <= 16)%Z ->
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.swap Host_t F E
        U256 Ugas Uunit index).
  Proof.
    intro Hindex.
    unfold MonadVM.Vm.Make.Executor.swap.
    eapply bind_decrease_after_preserve.
    - apply pop_nonincreasing.
    - intro first.
      eapply bind_decrease_after_preserve.
      + eapply gtgteq_nonincreasing.
        * apply fmap_nonincreasing. apply read_lens_nonincreasing.
        * intro choice. apply option_or_fail_nonincreasing.
      + intros [picked stack'].
        eapply bind_decrease_after_preserve.
        * apply write_stack_nonincreasing.
        * intros [].
          eapply spend_then_preserving_decreases.
          -- apply very_low_positive.
          -- intros [].
             eapply bind_nonincreasing.
             ++ apply push_nonincreasing.
             ++ intros []. apply increase_pc_nonincreasing.
  Qed.

  Lemma decoded_dup_opcode_decreasing (byte : ascii) (index : int) :
    MonadVM.Opcode.of_byte byte = MonadVM.Opcode.Dup index ->
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.dup Host_t F E
        U256 Ugas Uoption_action Uunit Uoption index).
  Proof.
    intro Hdecoded.
    apply dup_opcode_compositional_decreasing.
    eapply decoded_dup_index; exact Hdecoded.
  Qed.

  Lemma decoded_swap_opcode_decreasing (byte : ascii) (index : int) :
    MonadVM.Opcode.of_byte byte = MonadVM.Opcode.Swap index ->
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.swap Host_t F E
        U256 Ugas Uunit index).
  Proof.
    intro Hdecoded.
    apply swap_opcode_compositional_decreasing.
    eapply decoded_swap_index; exact Hdecoded.
  Qed.
End StackRearrangementOpcode.

Lemma exponent_bytes_nonnegative (exponent : MonadVM.Numeric.U256.t) :
  (0 <= MonadVM.Numeric.U256.significant_bytes exponent)%Z.
Proof.
  change (0 <= Z.quot
    (RocqOfOCaml.OCamlZ.numbits exponent + 7) 8)%Z.
  apply Z.quot_pos; [|lia].
  unfold RocqOfOCaml.OCamlZ.numbits.
  destruct (Z.eqb exponent 0) eqn:Hzero; [lia|].
  pose proof (Z.log2_nonneg (Z.abs exponent)).
  lia.
Qed.

Section ExpCharge.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
  Context `{Uuint : RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}.

  Lemma exponent_bytes_as_nat (exponent : MonadVM.Numeric.U256.t) :
    @MonadVM.Support.UintN.of_int Uuint
      (MonadVM.Numeric.U256.significant_bytes exponent) =
    Z.to_N (MonadVM.Numeric.U256.significant_bytes exponent).
  Proof.
    pose proof (exponent_bytes_nonnegative exponent) as Hnonnegative.
    unfold MonadVM.Support.UintN.of_int,
      MonadVM.Support.UintN.of_z_exn,
      MonadVM.Support.UintN.of_z_opt,
      MonadVM.Support.UintN.in_range.
    apply Z.leb_le in Hnonnegative.
    rewrite Hnonnegative.
    reflexivity.
  Qed.

  Lemma exp_charge_positive (exponent : MonadVM.Numeric.U256.t) :
    0 < @MonadVM.Gas.op_plus Ugas (@MonadVM.Gas.exp_base_cost Ugas)
      (@MonadVM.Gas.op_star Ugas (@MonadVM.Gas.exp_cost_per_byte Ugas)
        (@MonadVM.Support.UintN.of_int Uuint
          (MonadVM.Numeric.U256.significant_bytes exponent))).
  Proof.
    rewrite exponent_bytes_as_nat.
    unfold MonadVM.Gas.op_plus, MonadVM.Gas.op_star,
      MonadVM.Support.UintN.op_plus, MonadVM.Support.UintN.op_star.
    change (0 < 10 + 50 *
      Z.to_N (MonadVM.Numeric.U256.significant_bytes exponent)).
    lia.
  Qed.
End ExpCharge.

Section ExpOpcode.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{UZ : RocqOfOCaml.Basics.Unreachable Z.t}.
  Context `{Uuint : RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}.
  Context `{U256 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
  Context `{Uunit : RocqOfOCaml.Basics.Unreachable unit}.
  Context `{UintPair : RocqOfOCaml.Basics.Unreachable (int * int)}.

  Lemma exp_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.exp Host_t F E
        UZ Uuint U256 Ugas Uunit UintPair).
  Proof.
    unfold MonadVM.Vm.Make.Executor.exp.
    eapply bind_decrease_after_preserve.
    - apply pop2_nonincreasing.
    - intros [base exponent].
      eapply spend_then_preserving_decreases.
      + apply (@exp_charge_positive Ugas Uuint exponent).
      + intros [].
        eapply bind_nonincreasing.
        * apply push_nonincreasing.
        * intros []. apply increase_pc_nonincreasing.
  Qed.
End ExpOpcode.

Section HostReadOpcode.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{U256 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.

  Lemma get_balance_nonincreasing
      (address : MonadVM.Vm.Make.Address.t) :
    gas_nonincreasing
      (@MonadVM.Vm.Make.M.HostAPI.get_balance Host_t F address).
  Proof.
    unfold MonadVM.Vm.Make.M.HostAPI.get_balance.
    apply host_lift_nonincreasing.
  Qed.

  Lemma access_account_nonincreasing
      (address : MonadVM.Vm.Make.Address.t) :
    gas_nonincreasing
      (@MonadVM.Vm.Make.M.HostAPI.access_account Host_t F address).
  Proof.
    unfold MonadVM.Vm.Make.M.HostAPI.access_account.
    apply host_lift_nonincreasing.
  Qed.

  Lemma get_code_size_nonincreasing
      (address : MonadVM.Vm.Make.Address.t) :
    gas_nonincreasing
      (@MonadVM.Vm.Make.M.HostAPI.get_code_size Host_t F address).
  Proof.
    unfold MonadVM.Vm.Make.M.HostAPI.get_code_size.
    apply host_lift_nonincreasing.
  Qed.

  Lemma get_code_hash_nonincreasing
      (address : MonadVM.Vm.Make.Address.t) :
    gas_nonincreasing
      (@MonadVM.Vm.Make.M.HostAPI.get_code_hash Host_t F address).
  Proof.
    unfold MonadVM.Vm.Make.M.HostAPI.get_code_hash.
    apply host_lift_nonincreasing.
  Qed.

  Lemma account_access_cost_positive
      (status : MonadVM.Support.Variants.AccessStatus.t) :
    0 < @MonadVM.Gas.account_access_cost Ugas status.
  Proof. destruct status; vm_compute; reflexivity. Qed.

  Lemma access_charge_success_positive
      (address : MonadVM.Vm.Make.Address.t)
      (state : @MonadVM.Vm.Make.MachineState.t Host_t F)
      (charge : N)
      (next : @MonadVM.Vm.Make.MachineState.t Host_t F) :
    MonadVM.Vm.Make.M.op_ltdollargt
      (@MonadVM.Gas.account_access_cost Ugas)
      (@MonadVM.Vm.Make.M.HostAPI.access_account Host_t F address) state =
      ((inl charge :
        sum N MonadVM.Evmc.Result.StatusCode.t), next) ->
    0 < charge.
  Proof.
    intro Hsuccess.
    apply map_success_value in Hsuccess.
    destruct Hsuccess as [status [_ Hcharge]].
    subst charge.
    apply account_access_cost_positive.
  Qed.

  Lemma selfbalance_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.selfbalance Host_t F E U256 Ugas).
  Proof.
    unfold MonadVM.Vm.Make.Executor.selfbalance.
    eapply spend_then_preserving_decreases.
    - apply low_positive.
    - intros [].
      eapply bind_nonincreasing.
      + apply get_balance_nonincreasing.
      + intro balance.
        eapply bind_nonincreasing.
        * apply push_nonincreasing.
        * intros []. apply increase_pc_nonincreasing.
  Qed.
End HostReadOpcode.

Section BalanceOpcode.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{Urepr :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.Repr.t}.
  Context `{U256 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
  Context `{Uaddress :
    RocqOfOCaml.Basics.Unreachable MonadVM.Vm.Make.Address.t}.
  Context `{Uunit : RocqOfOCaml.Basics.Unreachable unit}.
  Context `{Uint : RocqOfOCaml.Basics.Unreachable int}.
  Context `{Uascii : RocqOfOCaml.Basics.Unreachable ascii}.
  Context `{UintPair : RocqOfOCaml.Basics.Unreachable (int * int)}.

  Lemma balance_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.balance Host_t F E
        Urepr U256 Ugas Uaddress Uunit Uint Uascii UintPair).
  Proof.
    unfold MonadVM.Vm.Make.Executor.balance.
    eapply bind_decrease_after_preserve.
    - apply map_nonincreasing. apply pop_nonincreasing.
    - intro address.
      eapply (bind_decrease_after_preserve_if _ _
        (fun (amount : N) => 0 < amount)).
      + apply map_nonincreasing. apply access_account_nonincreasing.
      + intros state charge next Hsuccess.
        eapply access_charge_success_positive; exact Hsuccess.
      + intros charge Hpositive.
        eapply spend_then_preserving_decreases.
        * exact Hpositive.
        * intros [].
          eapply bind_nonincreasing.
          -- apply get_balance_nonincreasing.
          -- intro balance.
             eapply bind_nonincreasing.
             ++ apply push_nonincreasing.
             ++ intros []. apply increase_pc_nonincreasing.
  Qed.
End BalanceOpcode.

Section ExternalCodeReadOpcode.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{Urepr :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.Repr.t}.
  Context `{U256 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
  Context `{Uaddress :
    RocqOfOCaml.Basics.Unreachable MonadVM.Vm.Make.Address.t}.
  Context `{Uunit : RocqOfOCaml.Basics.Unreachable unit}.
  Context `{Uint : RocqOfOCaml.Basics.Unreachable int}.
  Context `{Uascii : RocqOfOCaml.Basics.Unreachable ascii}.
  Context `{UintPair : RocqOfOCaml.Basics.Unreachable (int * int)}.

  Lemma extcodesize_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.extcodesize Host_t F E
        Urepr U256 Ugas Uaddress Uunit Uint Uascii UintPair).
  Proof.
    unfold MonadVM.Vm.Make.Executor.extcodesize.
    eapply bind_decrease_after_preserve.
    - apply map_nonincreasing. apply pop_nonincreasing.
    - intro address.
      eapply (bind_decrease_after_preserve_if _ _
        (fun (amount : N) => 0 < amount)).
      + apply map_nonincreasing. apply access_account_nonincreasing.
      + intros state charge next Hsuccess.
        eapply access_charge_success_positive; exact Hsuccess.
      + intros charge Hpositive.
        eapply spend_then_preserving_decreases.
        * exact Hpositive.
        * intros [].
          eapply bind_nonincreasing.
          -- apply map_nonincreasing. apply get_code_size_nonincreasing.
          -- intro size.
             eapply bind_nonincreasing.
             ++ apply push_nonincreasing.
             ++ intros []. apply increase_pc_nonincreasing.
  Qed.
End ExternalCodeReadOpcode.

Section ExternalCodeHashOpcode.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{Urepr :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.Repr.t}.
  Context `{U256 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
  Context `{Uaddress :
    RocqOfOCaml.Basics.Unreachable MonadVM.Vm.Make.Address.t}.
  Context `{Uunit : RocqOfOCaml.Basics.Unreachable unit}.
  Context `{Uint : RocqOfOCaml.Basics.Unreachable int}.
  Context `{Uascii : RocqOfOCaml.Basics.Unreachable ascii}.
  Context `{UintPair : RocqOfOCaml.Basics.Unreachable (int * int)}.
  Context `{Ubytes32 :
    RocqOfOCaml.Basics.Unreachable
      MonadVM.Byte_string.B32.(MonadVM.Byte_string.Fixed.Fixed_result.t)}.

  Lemma extcodehash_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.extcodehash Host_t F E
        Urepr U256 Ugas Uaddress Uunit Uint Uascii UintPair Ubytes32).
  Proof.
    unfold MonadVM.Vm.Make.Executor.extcodehash.
    eapply bind_decrease_after_preserve.
    - apply map_nonincreasing. apply pop_nonincreasing.
    - intro address.
      eapply (bind_decrease_after_preserve_if _ _
        (fun (amount : N) => 0 < amount)).
      + apply map_nonincreasing. apply access_account_nonincreasing.
      + intros state charge next Hsuccess.
        eapply access_charge_success_positive; exact Hsuccess.
      + intros charge Hpositive.
        eapply spend_then_preserving_decreases.
        * exact Hpositive.
        * intros [].
          eapply bind_nonincreasing.
          -- apply map_nonincreasing. apply get_code_hash_nonincreasing.
          -- intro hash.
             eapply bind_nonincreasing.
             ++ apply push_nonincreasing.
             ++ intros []. apply increase_pc_nonincreasing.
  Qed.
End ExternalCodeHashOpcode.

Section StorageOpcode.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{Urepr :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.Repr.t}.
  Context `{U256 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
  Context `{Uinteger :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.Integer.t}.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
  Context `{Uunit : RocqOfOCaml.Basics.Unreachable unit}.
  Context `{Uint : RocqOfOCaml.Basics.Unreachable int}.
  Context `{Uascii : RocqOfOCaml.Basics.Unreachable ascii}.
  Context `{UintPair : RocqOfOCaml.Basics.Unreachable (int * int)}.
  Context `{UintegerBase :
    RocqOfOCaml.Basics.Unreachable
      MonadVM.Numeric.IntegerBase.(MonadVM.Numeric.Make.Make_result.t)}.

  Lemma warm_storage_charge_positive :
    0 < @MonadVM.Gas.warm_access_cost Ugas.
  Proof. vm_compute; reflexivity. Qed.

  Lemma storage_access_charge_positive
      (status : MonadVM.Support.Variants.AccessStatus.t) :
    0 < match status with
        | MonadVM.Support.Variants.AccessStatus.Cold =>
            @MonadVM.Gas.cold_sload_cost Ugas
        | MonadVM.Support.Variants.AccessStatus.Warm =>
            @MonadVM.Gas.warm_access_cost Ugas
        end.
  Proof. destruct status; vm_compute; reflexivity. Qed.

  Lemma sstore_charge_positive
      (access : MonadVM.Support.Variants.AccessStatus.t)
      (status : MonadVM.Evmc.StorageStatus.t) :
    0 < @MonadVM.Gas.op_plus Ugas
      (match access with
       | MonadVM.Support.Variants.AccessStatus.Warm =>
           @MonadVM.Gas.zero Ugas
       | MonadVM.Support.Variants.AccessStatus.Cold =>
           @MonadVM.Gas.cold_sload_cost Ugas
       end)
      (match status with
       | MonadVM.Evmc.StorageStatus.Added =>
           @MonadVM.Gas.sset_cost Ugas
       | MonadVM.Evmc.StorageStatus.Deleted
       | MonadVM.Evmc.StorageStatus.Modified =>
           @MonadVM.Gas.sreset_cost Ugas
       | _ => @MonadVM.Gas.warm_access_cost Ugas
       end).
  Proof. destruct access, status; vm_compute; reflexivity. Qed.

  Lemma access_storage_nonincreasing
      (address : MonadVM.Vm.Make.Address.t) (key : string) :
    gas_nonincreasing
      (@MonadVM.Vm.Make.M.HostAPI.access_storage Host_t F address key).
  Proof.
    unfold MonadVM.Vm.Make.M.HostAPI.access_storage.
    apply host_lift_nonincreasing.
  Qed.

  Lemma get_storage_nonincreasing
      (address : MonadVM.Vm.Make.Address.t) (key : string) :
    gas_nonincreasing
      (@MonadVM.Vm.Make.M.HostAPI.get_storage Host_t F address key).
  Proof.
    unfold MonadVM.Vm.Make.M.HostAPI.get_storage.
    apply host_lift_nonincreasing.
  Qed.

  Lemma set_storage_nonincreasing
      (address : MonadVM.Vm.Make.Address.t)
      (key value : string) :
    gas_nonincreasing
      (@MonadVM.Vm.Make.M.HostAPI.set_storage
        Host_t F address key value).
  Proof.
    unfold MonadVM.Vm.Make.M.HostAPI.set_storage.
    apply host_lift_nonincreasing.
  Qed.

  Lemma get_transient_storage_nonincreasing
      (address : MonadVM.Vm.Make.Address.t) (key : string) :
    gas_nonincreasing
      (@MonadVM.Vm.Make.M.HostAPI.get_transient_storage
        Host_t F address key).
  Proof.
    unfold MonadVM.Vm.Make.M.HostAPI.get_transient_storage.
    apply host_lift_nonincreasing.
  Qed.

  Lemma set_transient_storage_nonincreasing
      (address : MonadVM.Vm.Make.Address.t) (key value : string) :
    gas_nonincreasing
      (@MonadVM.Vm.Make.M.HostAPI.set_transient_storage
        Host_t F address key value).
  Proof.
    unfold MonadVM.Vm.Make.M.HostAPI.set_transient_storage.
    apply host_lift_nonincreasing.
  Qed.

  Lemma check_write_permissions_nonincreasing :
    gas_nonincreasing
      (@MonadVM.Vm.Make.Executor.check_write_permissions Host_t F E).
  Proof.
    intros state value next Hsuccess.
    unfold MonadVM.Vm.Make.Executor.check_write_permissions in Hsuccess.
    destruct (MonadVM.Vm.Make.Executor.C.(
      MonadVM.Vm.Make.Executor_C_signature.execution_environment).(
      MonadVM.Vm.Make.ExecutionEnvironment.t.write_permission))
      eqn:Hpermission; cbn in Hsuccess.
    - inversion Hsuccess; subst next; lia.
    - discriminate Hsuccess.
  Qed.

  Lemma stipend_guard_nonincreasing (condition : bool) :
    gas_nonincreasing
      (@MonadVM.Vm.Make.M.when_ Host_t F condition
        (@MonadVM.Vm.Make.M.fail Host_t F unit
          MonadVM.Evmc.Result.StatusCode.Out_of_gas)).
  Proof.
    destruct condition; intros state value next Hsuccess;
      cbn in Hsuccess.
    - discriminate Hsuccess.
    - inversion Hsuccess; subst next; lia.
  Qed.

  Lemma refund_update_preserves_gas
      (update : MonadVM.Numeric.Integer.t -> MonadVM.Numeric.Integer.t)
      (state : @MonadVM.Vm.Make.MachineState.t Host_t F) :
    (snd (@MonadVM.Vm.Make.M.update_field Host_t F
      MonadVM.Numeric.Integer.t
      MonadVM.Vm.Make.MachineState.gas_refund update state)).(
        MonadVM.Vm.Make.MachineState.t.gas) =
    state.(MonadVM.Vm.Make.MachineState.t.gas).
  Proof. reflexivity. Qed.

  Lemma refund_update_nonincreasing
      (update : MonadVM.Numeric.Integer.t -> MonadVM.Numeric.Integer.t) :
    gas_nonincreasing
      (@MonadVM.Vm.Make.M.update_field Host_t F
        MonadVM.Numeric.Integer.t
        MonadVM.Vm.Make.MachineState.gas_refund update).
  Proof.
    intros state value next Hsuccess.
    pose proof (refund_update_preserves_gas update state) as Hgas.
    rewrite Hsuccess in Hgas.
    cbn in Hgas.
    lia.
  Qed.

  Lemma sload_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.sload Host_t F E
        Urepr U256 Ugas Uunit Uint Uascii UintPair).
  Proof.
    unfold MonadVM.Vm.Make.Executor.sload.
    eapply bind_decrease_after_preserve.
    - apply pop_nonincreasing.
    - intro key.
      eapply bind_decrease_after_preserve.
      + apply access_storage_nonincreasing.
      + intro status.
        eapply spend_then_preserving_decreases.
        * apply storage_access_charge_positive.
        * intros [].
          eapply bind_nonincreasing.
          -- apply map_nonincreasing. apply get_storage_nonincreasing.
          -- intro value.
             eapply bind_nonincreasing.
             ++ apply push_nonincreasing.
             ++ intros []. apply increase_pc_nonincreasing.
  Qed.

  Lemma tload_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.tload Host_t F E
        Urepr U256 Ugas Uunit Uint Uascii UintPair).
  Proof.
    unfold MonadVM.Vm.Make.Executor.tload.
    eapply bind_decrease_after_preserve.
    - apply pop_nonincreasing.
    - intro key.
      eapply spend_then_preserving_decreases.
      + apply warm_storage_charge_positive.
      + intros [].
        eapply bind_nonincreasing.
        * apply map_nonincreasing.
          apply get_transient_storage_nonincreasing.
        * intro value.
          eapply bind_nonincreasing.
          -- apply push_nonincreasing.
          -- intros []. apply increase_pc_nonincreasing.
  Qed.

  Lemma tstore_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.tstore Host_t F E
        Urepr U256 Ugas Uunit Uint Uascii UintPair).
  Proof.
    unfold MonadVM.Vm.Make.Executor.tstore.
    eapply bind_decrease_after_preserve.
    - apply pop2_nonincreasing.
    - intros [key value].
      eapply spend_then_preserving_decreases.
      + apply warm_storage_charge_positive.
      + intros [].
        eapply bind_nonincreasing.
        * apply check_write_permissions_nonincreasing.
        * intros [].
          eapply bind_nonincreasing.
          -- apply set_transient_storage_nonincreasing.
          -- intros []. apply increase_pc_nonincreasing.
  Qed.

  Lemma sstore_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.sstore Host_t F E
        Urepr U256 Uinteger Ugas Uunit Uint Uascii UintPair UintegerBase).
  Proof.
    unfold MonadVM.Vm.Make.Executor.sstore.
    eapply bind_decrease_after_preserve.
    { apply pop2_nonincreasing. }
    intros [key value].
    eapply bind_decrease_after_preserve.
    { apply read_lens_nonincreasing. }
    intro current_gas.
    eapply bind_decrease_after_preserve.
    { apply stipend_guard_nonincreasing. }
    intros [].
    eapply bind_decrease_after_preserve.
    { apply check_write_permissions_nonincreasing. }
    intros [].
    eapply bind_decrease_after_preserve.
    { apply access_storage_nonincreasing. }
    intro access.
    eapply bind_decrease_after_preserve.
    { apply set_storage_nonincreasing. }
    intro status.
    eapply spend_then_preserving_decreases.
    { apply sstore_charge_positive. }
    intros [].
    eapply bind_nonincreasing.
    { apply refund_update_nonincreasing. }
    intros [].
    apply increase_pc_nonincreasing.
  Qed.
End StorageOpcode.

Section JumpOpcode.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{U256 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
  Context `{Uascii : RocqOfOCaml.Basics.Unreachable ascii}.

  Lemma check_jump_destination_nonincreasing
      (destination : MonadVM.Numeric.U256.t) :
    gas_nonincreasing
      (@MonadVM.Vm.Make.Executor.check_jump_destination
        Host_t F E U256 Uascii destination).
  Proof.
    intros state value next Hsuccess.
    unfold MonadVM.Vm.Make.Executor.check_jump_destination in Hsuccess.
    destruct (MonadVM.Numeric.U256._Set.(RocqOfOCaml.OCamlSet.S.mem)
      destination
      (@MonadVM.Vm.Make.Executor.jump_destinations
        Host_t F E U256 Uascii)); cbn in Hsuccess.
    - inversion Hsuccess; subst next; lia.
    - discriminate Hsuccess.
  Qed.

  Lemma jump_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.jump Host_t F E U256 Ugas Uascii).
  Proof.
    unfold MonadVM.Vm.Make.Executor.jump.
    eapply bind_decrease_after_preserve.
    { apply pop_nonincreasing. }
    intro destination.
    eapply spend_then_preserving_decreases.
    { apply mid_positive. }
    intros [].
    eapply bind_nonincreasing.
    { apply check_jump_destination_nonincreasing. }
    intros []. apply update_pc_nonincreasing.
  Qed.

  Lemma jumpi_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.jumpi Host_t F E U256 Ugas Uascii).
  Proof.
    unfold MonadVM.Vm.Make.Executor.jumpi.
    eapply bind_decrease_after_preserve.
    { apply pop2_nonincreasing. }
    intros [destination condition].
    eapply spend_then_preserving_decreases.
    { apply high_positive. }
    intros [].
    destruct (MonadVM.Numeric.U256.is_zero condition).
    - apply increase_pc_nonincreasing.
    - eapply bind_nonincreasing.
      + apply check_jump_destination_nonincreasing.
      + intros []. apply update_pc_nonincreasing.
  Qed.
End JumpOpcode.

Section JumpDestinationOpcode.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{Urepr :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.Repr.t}.
  Context `{U256 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
  Context `{Uunit : RocqOfOCaml.Basics.Unreachable unit}.
  Context `{Uint : RocqOfOCaml.Basics.Unreachable int}.
  Context `{Uascii : RocqOfOCaml.Basics.Unreachable ascii}.
  Context `{UintPair : RocqOfOCaml.Basics.Unreachable (int * int)}.

  Lemma debug_tstore_stack_nonincreasing :
    gas_nonincreasing
      (@MonadVM.Vm.Make.Executor.debug_tstore_stack Host_t F E
        Urepr U256 Uunit Uint Uascii UintPair true).
  Proof.
    unfold MonadVM.Vm.Make.Executor.debug_tstore_stack.
    destruct (negb ((@MonadVM.Vm.Make.Params Host_t F).(
      MonadVM.Vm.Make_Params_signature.debug_tstore))).
    - apply return_nonincreasing.
    - eapply bind_nonincreasing.
      { apply pure_read_nonincreasing. }
      intro pc.
      eapply bind_nonincreasing.
      { apply get_transient_storage_nonincreasing. }
      intro first_slot.
      cbv zeta.
      lazymatch goal with
      | |- gas_nonincreasing (if ?condition then _ else _) =>
          destruct condition
      end.
      + apply return_nonincreasing.
      + eapply bind_nonincreasing.
        { apply pure_read_nonincreasing. }
        intro stack.
        eapply bind_nonincreasing.
        { eapply list_fold_leftM_nonincreasing.
          intros index value.
          cbv zeta.
          eapply bind_nonincreasing.
          - apply set_transient_storage_nonincreasing.
          - intros []. apply return_nonincreasing. }
        intro final_index. apply return_nonincreasing.
  Qed.

  Lemma jumpdest_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.jumpdest Host_t F E
        Urepr U256 Ugas Uunit Uint Uascii UintPair).
  Proof.
    unfold MonadVM.Vm.Make.Executor.jumpdest.
    eapply bind_decrease_after_preserve.
    { apply debug_tstore_stack_nonincreasing. }
    intros [].
    eapply spend_then_preserving_decreases.
    { apply jumpdest_positive. }
    intros []. apply increase_pc_nonincreasing.
  Qed.
End JumpDestinationOpcode.

Section MemoryActions.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.

  Let Memory_t := @MonadVM.Vm.Make.Memory.t Host_t F.
  Let State := @MonadVM.Vm.Make.MachineState.t Host_t F.

  Lemma memory_assign_preserves_gas (memory : Memory_t) (state : State) :
    (snd (@MonadVM.Vm.Make.M.op_coloneq Host_t F Memory_t
      MonadVM.Vm.Make.MachineState.memory memory state)).(
        MonadVM.Vm.Make.MachineState.t.gas) =
    state.(MonadVM.Vm.Make.MachineState.t.gas).
  Proof. reflexivity. Qed.

  Lemma memory_assign_nonincreasing (memory : Memory_t) :
    gas_nonincreasing
      (@MonadVM.Vm.Make.M.op_coloneq Host_t F Memory_t
        MonadVM.Vm.Make.MachineState.memory memory).
  Proof.
    intros state value next Hsuccess.
    pose proof (memory_assign_preserves_gas memory state) as Hgas.
    rewrite Hsuccess in Hgas.
    cbn in Hgas.
    lia.
  Qed.

  Lemma memory_update_preserves_gas
      (update : Memory_t -> Memory_t) (state : State) :
    (snd (@MonadVM.Vm.Make.M.update_field Host_t F Memory_t
      MonadVM.Vm.Make.MachineState.memory update state)).(
        MonadVM.Vm.Make.MachineState.t.gas) =
    state.(MonadVM.Vm.Make.MachineState.t.gas).
  Proof. reflexivity. Qed.

  Lemma memory_update_nonincreasing
      (update : Memory_t -> Memory_t) :
    gas_nonincreasing
      (@MonadVM.Vm.Make.M.update_field Host_t F Memory_t
        MonadVM.Vm.Make.MachineState.memory update).
  Proof.
    intros state value next Hsuccess.
    pose proof (memory_update_preserves_gas update state) as Hgas.
    rewrite Hsuccess in Hgas.
    cbn in Hgas.
    lia.
  Qed.
End MemoryActions.

Section MemoryExtension.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{Uuint :
    RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}.
  Context `{U256 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
  Context `{UuintFunction :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Support.UintN.t -> MonadVM.Support.UintN.t)}.
  Context `{Uextend :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Numeric.U256.t -> MonadVM.Numeric.U256.t ->
        @MonadVM.Vm.Make.Memory.t Host_t F ->
        @MonadVM.Vm.Make.M.Option.t Host_t F
          (@MonadVM.Vm.Make.Memory.t Host_t F))}.

  Lemma extend_memory_to_nonincreasing
      (start size_bytes : MonadVM.Numeric.U256.t) :
    gas_nonincreasing
      (@MonadVM.Vm.Make.Executor.extend_memory_to
        Host_t F E Uuint U256 Ugas UuintFunction Uextend
        start size_bytes).
  Proof.
    unfold MonadVM.Vm.Make.Executor.extend_memory_to.
    destruct (MonadVM.Numeric.U256.op_eq size_bytes
      (@MonadVM.Numeric.U256.zero U256)).
    - apply return_nonincreasing.
    - eapply bind_nonincreasing.
      { apply read_lens_nonincreasing. }
      intro current.
      eapply bind_nonincreasing.
      { apply option_or_fail_nonincreasing. }
      intro extended.
      eapply bind_nonincreasing.
      { apply memory_assign_nonincreasing. }
      intros [].
      eapply bind_nonincreasing.
      { apply map_nonincreasing. apply read_lens_nonincreasing. }
      intro new_active_words.
      destruct (MonadVM.Support.UintN.op_gteq _ _);
        apply return_nonincreasing.
  Qed.
End MemoryExtension.

Section MemoryLoadOpcode.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{Uuint :
    RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}.
  Context `{Urepr :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.Repr.t}.
  Context `{U256 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
  Context `{Ubytes :
    RocqOfOCaml.Basics.Unreachable MonadVM.Byte_string.Bytes.t}.
  Context `{Uunit : RocqOfOCaml.Basics.Unreachable unit}.
  Context `{UlistBytes :
    RocqOfOCaml.Basics.Unreachable (list MonadVM.Byte_string.Bytes.t)}.
  Context `{Uint : RocqOfOCaml.Basics.Unreachable int}.
  Context `{Uascii : RocqOfOCaml.Basics.Unreachable ascii}.
  Context `{UuintFunction :
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

  Lemma mload_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.mload Host_t F E
        Uuint Urepr U256 Ugas Ubytes Uunit UlistBytes Uint Uascii
        UuintFunction Ub32 Uextend).
  Proof.
    unfold MonadVM.Vm.Make.Executor.mload.
    eapply bind_decrease_after_preserve.
    { apply pop_nonincreasing. }
    intro position.
    eapply bind_decrease_after_preserve.
    { apply extend_memory_to_nonincreasing. }
    intro memory_extension_gas.
    eapply spend_then_preserving_decreases.
    { apply positive_charge_plus. apply very_low_positive. }
    intros [].
    eapply bind_nonincreasing.
    { apply map_nonincreasing. apply read_lens_nonincreasing. }
    intro word.
    eapply bind_nonincreasing.
    { apply push_nonincreasing. }
    intros []. apply increase_pc_nonincreasing.
  Qed.
End MemoryLoadOpcode.

Section MemoryStoreOpcode.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{Uuint :
    RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}.
  Context `{Urepr :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.Repr.t}.
  Context `{U256 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
  Context `{Ubytes :
    RocqOfOCaml.Basics.Unreachable MonadVM.Byte_string.Bytes.t}.
  Context `{Uunit : RocqOfOCaml.Basics.Unreachable unit}.
  Context `{Ustring : RocqOfOCaml.Basics.Unreachable string}.
  Context `{UlistInt : RocqOfOCaml.Basics.Unreachable (list int)}.
  Context `{Uint : RocqOfOCaml.Basics.Unreachable int}.
  Context `{Uascii : RocqOfOCaml.Basics.Unreachable ascii}.
  Context `{UintPair : RocqOfOCaml.Basics.Unreachable (int * int)}.
  Context `{UuintFunction :
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

  Lemma mstore_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.mstore Host_t F E
        Uuint Urepr U256 Ugas Ubytes Uunit Ustring UlistInt Uint
        Uascii UintPair UuintFunction Ub32 Uextend).
  Proof.
    unfold MonadVM.Vm.Make.Executor.mstore.
    eapply bind_decrease_after_preserve.
    { apply pop2_nonincreasing. }
    intros [position word].
    eapply bind_decrease_after_preserve.
    { apply extend_memory_to_nonincreasing. }
    intro memory_extension_gas.
    eapply spend_then_preserving_decreases.
    { apply positive_charge_plus. apply very_low_positive. }
    intros [].
    eapply bind_nonincreasing.
    { apply memory_update_nonincreasing. }
    intros []. apply increase_pc_nonincreasing.
  Qed.

  Lemma mstore8_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.mstore8 Host_t F E
        Uuint U256 Ugas Ubytes Uunit Ustring UlistInt Uint Uascii
        UuintFunction Ub32 Uextend).
  Proof.
    unfold MonadVM.Vm.Make.Executor.mstore8.
    eapply bind_decrease_after_preserve.
    { apply pop2_nonincreasing. }
    intros [position word].
    eapply bind_decrease_after_preserve.
    { apply extend_memory_to_nonincreasing. }
    intro memory_extension_gas.
    eapply spend_then_preserving_decreases.
    { apply positive_charge_plus. apply very_low_positive. }
    intros [].
    eapply bind_nonincreasing.
    { apply memory_update_nonincreasing. }
    intros []. apply increase_pc_nonincreasing.
  Qed.
End MemoryStoreOpcode.

Section MemoryCopyOpcode.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{Uuint :
    RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}.
  Context `{U256 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
  Context `{Ubytes :
    RocqOfOCaml.Basics.Unreachable MonadVM.Byte_string.Bytes.t}.
  Context `{Uunit : RocqOfOCaml.Basics.Unreachable unit}.
  Context `{Ustring : RocqOfOCaml.Basics.Unreachable string}.
  Context `{UlistInt : RocqOfOCaml.Basics.Unreachable (list int)}.
  Context `{Uint : RocqOfOCaml.Basics.Unreachable int}.
  Context `{Uascii : RocqOfOCaml.Basics.Unreachable ascii}.
  Context `{UuintFunction :
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

  Lemma copy_input_data_opcode_impl_decreasing (data : string) :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.copy_input_data_opcode_impl Host_t F E
        Uuint U256 Ugas Ubytes Uunit Ustring UlistInt Uint Uascii
        UuintFunction Ub32 Uextend data).
  Proof.
    unfold MonadVM.Vm.Make.Executor.copy_input_data_opcode_impl.
    eapply bind_decrease_after_preserve.
    { apply pop3_nonincreasing. }
    intros [[dst_start src_start] size_bytes].
    eapply bind_decrease_after_preserve.
    { apply extend_memory_to_nonincreasing. }
    intro memory_extension_gas.
    eapply spend_then_preserving_decreases.
    { apply positive_charge_plus.
      apply positive_charge_plus.
      apply very_low_positive. }
    intros [].
    eapply bind_nonincreasing.
    { apply memory_update_nonincreasing. }
    intros []. apply increase_pc_nonincreasing.
  Qed.

End MemoryCopyOpcode.

Section MemoryCopyWrapperOpcode.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{Uuint :
    RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}.
  Context `{U256 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
  Context `{Ubytes :
    RocqOfOCaml.Basics.Unreachable MonadVM.Byte_string.Bytes.t}.
  Context `{Uunit : RocqOfOCaml.Basics.Unreachable unit}.
  Context `{UlistInt : RocqOfOCaml.Basics.Unreachable (list int)}.
  Context `{Uint : RocqOfOCaml.Basics.Unreachable int}.
  Context `{Uascii : RocqOfOCaml.Basics.Unreachable ascii}.
  Context `{UuintFunction :
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

  Lemma calldatacopy_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.calldatacopy Host_t F E
        Uuint U256 Ugas Ubytes Uunit UlistInt Uint Uascii
        UuintFunction Ub32 Uextend).
  Proof.
    unfold MonadVM.Vm.Make.Executor.calldatacopy.
    exact (@copy_input_data_opcode_impl_decreasing Host_t F E
      Uuint U256 Ugas Ubytes Uunit Ubytes UlistInt Uint Uascii
      UuintFunction Ub32 Uextend _).
  Qed.

  Lemma codecopy_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.codecopy Host_t F E
        Uuint U256 Ugas Ubytes Uunit UlistInt Uint Uascii
        UuintFunction Ub32 Uextend).
  Proof.
    unfold MonadVM.Vm.Make.Executor.codecopy.
    exact (@copy_input_data_opcode_impl_decreasing Host_t F E
      Uuint U256 Ugas Ubytes Uunit Ubytes UlistInt Uint Uascii
      UuintFunction Ub32 Uextend _).
  Qed.
End MemoryCopyWrapperOpcode.

Section KeccakOpcode.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{Uuint :
    RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}.
  Context `{U256 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
  Context `{Ubytes :
    RocqOfOCaml.Basics.Unreachable MonadVM.Byte_string.Bytes.t}.
  Context `{Uunit : RocqOfOCaml.Basics.Unreachable unit}.
  Context `{Ustring : RocqOfOCaml.Basics.Unreachable string}.
  Context `{UlistBytes :
    RocqOfOCaml.Basics.Unreachable (list MonadVM.Byte_string.Bytes.t)}.
  Context `{Uint : RocqOfOCaml.Basics.Unreachable int}.
  Context `{Uascii : RocqOfOCaml.Basics.Unreachable ascii}.
  Context `{UuintFunction :
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

  Lemma keccak_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.keccak Host_t F E
        Uuint U256 Ugas Ubytes Uunit Ustring UlistBytes Uint Uascii
        UuintFunction Ub32 Uextend).
  Proof.
    unfold MonadVM.Vm.Make.Executor.keccak.
    eapply bind_decrease_after_preserve.
    { apply pop2_nonincreasing. }
    intros [start size_bytes].
    eapply bind_decrease_after_preserve.
    { apply extend_memory_to_nonincreasing. }
    intro memory_extension_gas.
    eapply spend_then_preserving_decreases.
    { apply positive_charge_plus.
      apply positive_charge_plus.
      apply keccak_base_positive. }
    intros [].
    eapply bind_nonincreasing.
    { apply map_nonincreasing. apply read_lens_nonincreasing. }
    intro bytes_value.
    eapply bind_nonincreasing.
    { apply push_nonincreasing. }
    intros []. apply increase_pc_nonincreasing.
  Qed.
End KeccakOpcode.

Section MemoryCopyWithinOpcode.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{Uuint :
    RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}.
  Context `{U256 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
  Context `{Ubytes :
    RocqOfOCaml.Basics.Unreachable MonadVM.Byte_string.Bytes.t}.
  Context `{Uunit : RocqOfOCaml.Basics.Unreachable unit}.
  Context `{Ustring : RocqOfOCaml.Basics.Unreachable string}.
  Context `{UlistBytes :
    RocqOfOCaml.Basics.Unreachable (list MonadVM.Byte_string.Bytes.t)}.
  Context `{UlistInt : RocqOfOCaml.Basics.Unreachable (list int)}.
  Context `{Uint : RocqOfOCaml.Basics.Unreachable int}.
  Context `{UuintFunction :
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

  Lemma mcopy_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.mcopy Host_t F E
        Uuint U256 Ugas Ubytes Uunit Ustring UlistBytes UlistInt Uint
        UuintFunction Ub32 Uextend).
  Proof.
    unfold MonadVM.Vm.Make.Executor.mcopy.
    eapply bind_decrease_after_preserve.
    { apply pop3_nonincreasing. }
    intros [[dst_start src_start] size_bytes].
    eapply bind_decrease_after_preserve.
    { apply extend_memory_to_nonincreasing. }
    intro memory_extension_gas.
    eapply spend_then_preserving_decreases.
    { apply positive_charge_plus.
      apply positive_charge_plus.
      apply very_low_positive. }
    intros [].
    eapply bind_nonincreasing.
    { apply map_nonincreasing. apply read_lens_nonincreasing. }
    intro block.
    eapply bind_nonincreasing.
    { apply memory_update_nonincreasing. }
    intros []. apply increase_pc_nonincreasing.
  Qed.
End MemoryCopyWithinOpcode.

Section ReturnDataCopyOpcode.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{Uuint :
    RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}.
  Context `{U256 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
  Context `{Ubytes :
    RocqOfOCaml.Basics.Unreachable MonadVM.Byte_string.Bytes.t}.
  Context `{Uunit : RocqOfOCaml.Basics.Unreachable unit}.
  Context `{Ustring : RocqOfOCaml.Basics.Unreachable string}.
  Context `{UlistInt : RocqOfOCaml.Basics.Unreachable (list int)}.
  Context `{Uint : RocqOfOCaml.Basics.Unreachable int}.
  Context `{UuintFunction :
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

  Lemma returndatacopy_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.returndatacopy Host_t F E
        Uuint U256 Ugas Ubytes Uunit Ustring UlistInt Uint
        UuintFunction Ub32 Uextend).
  Proof.
    unfold MonadVM.Vm.Make.Executor.returndatacopy.
    eapply bind_decrease_after_preserve.
    { apply pop3_nonincreasing. }
    intros [[dst_start src_start] size_bytes].
    eapply bind_decrease_after_preserve.
    { apply read_lens_nonincreasing. }
    intro data.
    eapply bind_decrease_after_preserve.
    { destruct (MonadVM.Numeric.U256.to_int_opt src_start) as [start | ];
        destruct (MonadVM.Numeric.U256.to_int_opt size_bytes) as [sz | ];
        cbn; try apply fail_nonincreasing.
      destruct (orb (Z.gtb start (MonadVM.Byte_string.Bytes.length data))
        (Z.gtb sz (Z.sub (MonadVM.Byte_string.Bytes.length data) start)));
        [apply fail_nonincreasing | apply return_nonincreasing]. }
    intros [src_start_int size_int].
    eapply bind_decrease_after_preserve.
    { apply extend_memory_to_nonincreasing. }
    intro memory_extension_gas.
    eapply spend_then_preserving_decreases.
    { apply positive_charge_plus.
      apply positive_charge_plus.
      apply very_low_positive. }
    intros [].
    eapply bind_nonincreasing.
    { apply memory_update_nonincreasing. }
    intros []. apply increase_pc_nonincreasing.
  Qed.
End ReturnDataCopyOpcode.

Section AdditionalEnvironmentOpcodes.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{U256 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
  Context `{Ustring : RocqOfOCaml.Basics.Unreachable string}.
  Context `{UoptionString :
    RocqOfOCaml.Basics.Unreachable (option string)}.
  Context `{Uint : RocqOfOCaml.Basics.Unreachable int}.
  Context `{Uascii : RocqOfOCaml.Basics.Unreachable ascii}.

  Lemma calldataload_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.calldataload Host_t F E
        U256 Ugas Ustring Uint Uascii).
  Proof.
    unfold MonadVM.Vm.Make.Executor.calldataload.
    eapply bind_decrease_after_preserve.
    { apply pop_nonincreasing. }
    intro index.
    eapply spend_then_preserving_decreases.
    { apply very_low_positive. }
    intros [].
    eapply bind_nonincreasing.
    { apply push_nonincreasing. }
    intros []. apply increase_pc_nonincreasing.
  Qed.

  Lemma blobhash_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.blobhash Host_t F E
        U256 Ugas UoptionString Uint Uascii).
  Proof.
    unfold MonadVM.Vm.Make.Executor.blobhash.
    eapply bind_decrease_after_preserve.
    { apply pop_nonincreasing. }
    intro index.
    eapply spend_then_preserving_decreases.
    { apply very_low_positive. }
    intros [].
    eapply bind_nonincreasing.
    { apply push_nonincreasing. }
    intros []. apply increase_pc_nonincreasing.
  Qed.

  Lemma blobbasefee_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.blobbasefee Host_t F E U256 Ugas).
  Proof.
    unfold MonadVM.Vm.Make.Executor.blobbasefee.
    eapply spend_then_preserving_decreases.
    { apply base_positive. }
    intros [].
    eapply bind_nonincreasing.
    { apply push_nonincreasing. }
    intros []. apply increase_pc_nonincreasing.
  Qed.
End AdditionalEnvironmentOpcodes.

Section BlockHashOpcode.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{Uuint64 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Uint64.t}.
  Context `{Uuint :
    RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}.
  Context `{U256 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
  Context `{Uascii : RocqOfOCaml.Basics.Unreachable ascii}.

  Lemma get_block_hash_nonincreasing (id : MonadVM.Uint64.t) :
    gas_nonincreasing
      (@MonadVM.Vm.Make.M.HostAPI.get_block_hash Host_t F id).
  Proof.
    unfold MonadVM.Vm.Make.M.HostAPI.get_block_hash.
    apply host_lift_nonincreasing.
  Qed.

  Lemma blockhash_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.blockhash Host_t F E
        Uuint64 Uuint U256 Ugas Uascii).
  Proof.
    unfold MonadVM.Vm.Make.Executor.blockhash.
    eapply bind_decrease_after_preserve.
    { apply map_nonincreasing. apply pop_nonincreasing. }
    intro block_num.
    eapply spend_then_preserving_decreases.
    { apply block_hash_cost_positive. }
    intros [].
    eapply bind_nonincreasing.
    { cbn beta zeta.
      match goal with
      | |- gas_nonincreasing (if ?condition then _ else _) =>
          destruct condition
      end.
      - apply return_nonincreasing.
      - eapply bind_nonincreasing.
        { apply get_block_hash_nonincreasing. }
        intros [hash | ];
          [apply return_nonincreasing | apply fail_nonincreasing]. }
    intro hash.
    eapply bind_nonincreasing.
    { apply push_nonincreasing. }
    intros []. apply increase_pc_nonincreasing.
  Qed.
End BlockHashOpcode.

Section CountLeadingZerosOpcode.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{U256 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
  Context `{Uunit : RocqOfOCaml.Basics.Unreachable unit}.
  Context `{UintPair :
    RocqOfOCaml.Basics.Unreachable (int * int)}.
  Context `{Uimpl :
    RocqOfOCaml.Basics.Unreachable
      (@MonadVM.Vm.Make.opcode_impl Host_t F)}.

  Lemma clz_nine_opcode_compositional_decreasing :
    (@MonadVM.Vm.Make.Params Host_t F).(
      MonadVM.Vm.Make_Params_signature.revision) =
        MonadVM.Support.Variants.Revision.Nine ->
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.clz Host_t F E
        U256 Ugas Uunit UintPair Uimpl).
  Proof.
    intro Hrevision.
    unfold MonadVM.Vm.Make.Executor.clz.
    rewrite Hrevision.
    eapply bind_decrease_after_preserve.
    { apply pop_nonincreasing. }
    intro value.
    eapply spend_then_preserving_decreases.
    { apply low_positive. }
    intros [].
    eapply bind_nonincreasing.
    { apply push_nonincreasing. }
    intros []. apply increase_pc_nonincreasing.
  Qed.

  Lemma clz_eight_has_no_successful_result :
    (@MonadVM.Vm.Make.Params Host_t F).(
      MonadVM.Vm.Make_Params_signature.revision) =
        MonadVM.Support.Variants.Revision.Eight ->
    forall state value next,
      @MonadVM.Vm.Make.Executor.clz Host_t F E
        U256 Ugas Uunit UintPair Uimpl state =
          ((inl value : sum bool MonadVM.Evmc.Result.StatusCode.t), next) ->
      False.
  Proof.
    intros Hrevision state value next Hsuccess.
    unfold MonadVM.Vm.Make.Executor.clz in Hsuccess.
    rewrite Hrevision in Hsuccess.
    discriminate Hsuccess.
  Qed.
End CountLeadingZerosOpcode.

Section SequenceEquation.
  Context {M_t : Set -> Set}
    {F : @MonadVM.Monad.Make.FArgs M_t}.

  Lemma sequence_unfold {A : Set}
      (items : RocqOfOCaml.OCamlSeq.t (M_t A)) :
    @MonadVM.Monad.Make.Seq.sequence M_t F A items =
    match items with
    | RocqOfOCaml.OCamlSeq.Empty =>
        @MonadVM.Monad.Make._return M_t F
          (RocqOfOCaml.OCamlSeq.t A) RocqOfOCaml.OCamlSeq.Empty
    | RocqOfOCaml.OCamlSeq.More action rest =>
        @MonadVM.Monad.Make.op_letdollar M_t F A
          (RocqOfOCaml.OCamlSeq.t A) action
          (fun value =>
            @MonadVM.Monad.Make.op_letdollar M_t F
              (RocqOfOCaml.OCamlSeq.t A)
              (RocqOfOCaml.OCamlSeq.t A)
              (@MonadVM.Monad.Make.Seq.sequence M_t F A rest)
              (fun tail =>
                @MonadVM.Monad.Make._return M_t F
                  (RocqOfOCaml.OCamlSeq.t A)
                  (RocqOfOCaml.OCamlSeq.More value tail)))
    end.
  Proof.
    unfold MonadVM.Monad.Make.Seq.sequence at 1.
    rewrite Fix_eq.
    - destruct items; reflexivity.
    - intros seq f g Hfg.
      destruct seq as [| action rest]; cbn.
      + reflexivity.
      + rewrite (Hfg rest _). reflexivity.
  Qed.
End SequenceEquation.

Section SequenceGas.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.

  Lemma seq_mapM_nonincreasing {A B : Set}
      (step : A -> @MonadVM.Vm.Make.M.t Host_t F B)
      (items : RocqOfOCaml.OCamlSeq.t A) :
    (forall item, gas_nonincreasing (step item)) ->
    gas_nonincreasing
      (@MonadVM.Vm.Make.M.Seq.mapM Host_t F A B step items).
  Proof.
    intro Hstep.
    induction items as [| item rest IH].
    - unfold MonadVM.Vm.Make.M.Seq.mapM.
      cbn [MonadVM.Vm.Make.M.MonadVM_Monad_Result_state_include
        MonadVM.Monad.Result_state.functor
        MonadVM.Monad.Result_state.Result_state_result.Seq_mapM].
      unfold MonadVM.Monad.Result_state.Seq.mapM.
      cbn [MonadVM.Monad.Result_state.Trans_include
        MonadVM.Monad.Result_state.Trans.functor
        MonadVM.Monad.Result_state.Trans.Trans_result.Seq_mapM].
      unfold MonadVM.Monad.Result_state.Trans.Seq.mapM.
      cbn [MonadVM.Monad.Result_state.Trans.Make_include
        MonadVM.Monad.Result_state.Make.functor
        MonadVM.Monad.Result_state.Make.Make_result.Seq_mapM].
      unfold MonadVM.Monad.Result_state.Make.Seq.mapM.
      cbn [MonadVM.Monad.Result_state.Make.Result_Make_include
        MonadVM.Monad.Result.Make.functor
        MonadVM.Monad.Result.Make.Make_result.Seq_mapM].
      unfold MonadVM.Monad.Result.Make.Seq.mapM.
      cbn [MonadVM.Monad.Result.Make.Make_Monad_include
        MonadVM.Monad.Make.functor
        MonadVM.Monad.Make.Make_result.Seq_mapM].
      unfold MonadVM.Monad.Make.Seq.mapM.
      unfold MonadVM.Monad.Make_Monad.Seq.sequence at 1.
      rewrite Fix_eq.
      2: { intros seq f g Hfg.
           destruct seq as [| action rest]; cbn;
             [reflexivity | now rewrite (Hfg rest _)]. }
      apply return_nonincreasing.
    - unfold MonadVM.Vm.Make.M.Seq.mapM.
      cbn [MonadVM.Vm.Make.M.MonadVM_Monad_Result_state_include
        MonadVM.Monad.Result_state.functor
        MonadVM.Monad.Result_state.Result_state_result.Seq_mapM].
      unfold MonadVM.Monad.Result_state.Seq.mapM.
      cbn [MonadVM.Monad.Result_state.Trans_include
        MonadVM.Monad.Result_state.Trans.functor
        MonadVM.Monad.Result_state.Trans.Trans_result.Seq_mapM].
      unfold MonadVM.Monad.Result_state.Trans.Seq.mapM.
      cbn [MonadVM.Monad.Result_state.Trans.Make_include
        MonadVM.Monad.Result_state.Make.functor
        MonadVM.Monad.Result_state.Make.Make_result.Seq_mapM].
      unfold MonadVM.Monad.Result_state.Make.Seq.mapM.
      cbn [MonadVM.Monad.Result_state.Make.Result_Make_include
        MonadVM.Monad.Result.Make.functor
        MonadVM.Monad.Result.Make.Make_result.Seq_mapM].
      unfold MonadVM.Monad.Result.Make.Seq.mapM.
      cbn [MonadVM.Monad.Result.Make.Make_Monad_include
        MonadVM.Monad.Make.functor
        MonadVM.Monad.Make.Make_result.Seq_mapM].
      unfold MonadVM.Monad.Make.Seq.mapM.
      unfold MonadVM.Monad.Make_Monad.Seq.sequence at 1.
      rewrite Fix_eq.
      2: { intros seq f g Hfg.
           destruct seq as [| action tail]; cbn;
             [reflexivity | now rewrite (Hfg tail _)]. }
      change (gas_nonincreasing
        (@MonadVM.Vm.Make.M.op_letdollar Host_t F B
          (RocqOfOCaml.OCamlSeq.t B) (step item)
          (fun value =>
            @MonadVM.Vm.Make.M.op_letdollar Host_t F
              (RocqOfOCaml.OCamlSeq.t B)
              (RocqOfOCaml.OCamlSeq.t B)
              (@MonadVM.Vm.Make.M.Seq.mapM Host_t F A B step rest)
              (fun tail =>
                @MonadVM.Vm.Make.M._return Host_t F
                  (RocqOfOCaml.OCamlSeq.t B)
                  (RocqOfOCaml.OCamlSeq.More value tail))))).
      eapply bind_nonincreasing.
      + apply Hstep.
      + intro value.
        eapply bind_nonincreasing.
        * apply IH.
        * intro tail. apply return_nonincreasing.
  Qed.
End SequenceGas.

Section LogOpcode.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{UseqInt :
    RocqOfOCaml.Basics.Unreachable (RocqOfOCaml.OCamlSeq.t int)}.
  Context `{Uuint :
    RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}.
  Context `{Urepr :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.Repr.t}.
  Context `{U256 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
  Context `{Ubytes :
    RocqOfOCaml.Basics.Unreachable MonadVM.Byte_string.Bytes.t}.
  Context `{Uunit : RocqOfOCaml.Basics.Unreachable unit}.
  Context `{UlistBytes :
    RocqOfOCaml.Basics.Unreachable (list MonadVM.Byte_string.Bytes.t)}.
  Context `{Uint : RocqOfOCaml.Basics.Unreachable int}.
  Context `{Uascii : RocqOfOCaml.Basics.Unreachable ascii}.
  Context `{UintPair :
    RocqOfOCaml.Basics.Unreachable (int * int)}.
  Context `{UuintFunction :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Support.UintN.t -> MonadVM.Support.UintN.t)}.
  Context `{UseqNode :
    RocqOfOCaml.Basics.Unreachable
      (unit -> RocqOfOCaml.OCamlSeq.node int)}.
  Context `{Ub32 :
    RocqOfOCaml.Basics.Unreachable
      MonadVM.Byte_string.B32.(MonadVM.Byte_string.Fixed.Fixed_result.t)}.
  Context `{Uextend :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Numeric.U256.t -> MonadVM.Numeric.U256.t ->
        @MonadVM.Vm.Make.Memory.t Host_t F ->
        @MonadVM.Vm.Make.M.Option.t Host_t F
          (@MonadVM.Vm.Make.Memory.t Host_t F))}.

  Lemma emit_log_nonincreasing
      (addr : MonadVM.Vm.Make.Address.t)
      (data : MonadVM.Byte_string.Bytes.t)
      (topics : list MonadVM.Byte_string.Bytes.t) :
    gas_nonincreasing
      (@MonadVM.Vm.Make.M.HostAPI.emit_log
        Host_t F addr data topics).
  Proof.
    unfold MonadVM.Vm.Make.M.HostAPI.emit_log.
    apply host_lift_nonincreasing.
  Qed.

  Lemma log_opcode_compositional_decreasing (n_topics : int) :
    (0 <= n_topics <= 4)%Z ->
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.log Host_t F E
        UseqInt Uuint Urepr U256 Ugas Ubytes Uunit UlistBytes Uint
        Uascii UintPair UuintFunction UseqNode Ub32 Uextend n_topics).
  Proof.
    intro Hrange.
    unfold MonadVM.Vm.Make.Executor.log.
    eapply bind_decrease_after_preserve.
    { apply pop2_nonincreasing. }
    intros [start size_bytes].
    eapply bind_decrease_after_preserve.
    { apply map_nonincreasing.
      apply seq_mapM_nonincreasing.
      intro topic_index.
      apply map_nonincreasing.
      apply pop_nonincreasing. }
    intro topics.
    eapply bind_decrease_after_preserve.
    { apply extend_memory_to_nonincreasing. }
    intro memory_extension_gas.
    eapply spend_then_preserving_decreases.
    { apply positive_charge_plus.
      apply positive_charge_plus.
      apply positive_charge_plus.
      apply log_cost_positive. }
    intros [].
    eapply bind_nonincreasing.
    { apply check_write_permissions_nonincreasing. }
    intros [].
    eapply bind_nonincreasing.
    { apply map_nonincreasing. apply read_lens_nonincreasing. }
    intro data.
    eapply bind_nonincreasing.
    { apply emit_log_nonincreasing. }
    intros []. apply increase_pc_nonincreasing.
  Qed.

  Lemma decoded_log_opcode_decreasing (byte : ascii)
      (n_topics : int) :
    MonadVM.Opcode.of_byte byte = MonadVM.Opcode.Log n_topics ->
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.log Host_t F E
        UseqInt Uuint Urepr U256 Ugas Ubytes Uunit UlistBytes Uint
        Uascii UintPair UuintFunction UseqNode Ub32 Uextend n_topics).
  Proof.
    intro Hdecoded.
    apply log_opcode_compositional_decreasing.
    eapply decoded_log_topics; exact Hdecoded.
  Qed.
End LogOpcode.
