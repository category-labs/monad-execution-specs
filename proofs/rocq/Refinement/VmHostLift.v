(** The generated VM's host-state lift preserves return and bind.

    All equations are pointwise in machine state. No functional
    extensionality, host-behavior law, or convergence assumption is used.
    These are the action-mapping premises needed to lift host resumptions
    into the VM's result-and-state monad. *)

Require Import RocqOfOCaml.RocqOfOCaml.
Require MonadVM.Vm.

Section HostLift.
  Context {Host_t : Set} {F : @Vm.Make.FArgs Host_t}.

  Definition host_action (A : Set) := Host_t -> A * Host_t.

  Definition host_return {A : Set} (value : A) : host_action A :=
    fun state => (value, state).

  Definition host_bind {A B : Set} (action : host_action A)
      (next : A -> host_action B) : host_action B :=
    fun state => let '(value, state) := action state in next value state.

  Definition machine_equiv {A : Set}
      (left right : @Vm.Make.M.t Host_t F A) : Prop :=
    forall state, left state = right state.

  Lemma host_lift_return {A : Set} (value : A) :
    machine_equiv (@Vm.Make.M._return Host_t F A value)
      (@Vm.Make.M.HostAPI.lift Host_t F A (host_return value)).
  Proof. intro state. destruct state. reflexivity. Qed.

  Lemma host_lift_bind {A B : Set} (action : host_action A)
      (next : A -> host_action B) :
    machine_equiv
      (@Vm.Make.M.op_gtgteq Host_t F A B
        (@Vm.Make.M.HostAPI.lift Host_t F A action)
        (fun value => @Vm.Make.M.HostAPI.lift Host_t F B (next value)))
      (@Vm.Make.M.HostAPI.lift Host_t F B (host_bind action next)).
  Proof.
    intro state. unfold Vm.Make.M.HostAPI.lift, host_bind.
    unfold Vm.Make.M.op_gtgteq.
    cbn. destruct (action (Vm.Make.MachineState.t.host state)).
    reflexivity.
  Qed.

  Lemma machine_bind_respects {A B : Set}
      (left right : @Vm.Make.M.t Host_t F A)
      (next_left next_right : A -> @Vm.Make.M.t Host_t F B) :
    machine_equiv left right ->
    (forall value, machine_equiv (next_left value) (next_right value)) ->
    machine_equiv (@Vm.Make.M.op_gtgteq Host_t F A B left next_left)
      (@Vm.Make.M.op_gtgteq Host_t F A B right next_right).
  Proof.
    intros actions continuations state.
    change
      ((let '(value, next_state) := left state in
        match value with
        | inl value => next_left value next_state
        | inr error => (inr error, next_state)
        end) =
       (let '(value, next_state) := right state in
        match value with
        | inl value => next_right value next_state
        | inr error => (inr error, next_state)
        end)).
    rewrite (actions state).
    destruct (right state) as [[value | error] next_state].
    - apply continuations.
    - reflexivity.
  Qed.
End HostLift.
