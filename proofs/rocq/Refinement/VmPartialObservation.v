(** Instantiate the partial runtime laws with the generated VM operations.
    Convergence is an explicit premise. These statements do not prove that
    arbitrary VM executions terminate. *)

Require Import RocqOfOCaml.RocqOfOCaml.
Require Import MonadExecutionSpecs.Refinement.VmHostLift.
Require MonadVM.Vm.

Section Observation.
  Context {Host_t : Set} {F : @Vm.Make.FArgs Host_t}.

  Lemma run_host_lift {A : Set}
      (computation : Resumption.t (@host_action Host_t) A)
      (proof : Resumption.converges computation) :
    machine_equiv
      (@Resumption.run (@Vm.Make.M.t Host_t F)
        (@Vm.Make.M._return Host_t F) (@Vm.Make.M.op_gtgteq Host_t F)
        A (Resumption.hoist (@Vm.Make.M.HostAPI.lift Host_t F) computation)
        (Resumption.hoist_converges (@Vm.Make.M.HostAPI.lift Host_t F) proof))
      (@Vm.Make.M.HostAPI.lift Host_t F A
        (@Resumption.run (@host_action Host_t)
          (@host_return Host_t) (@host_bind Host_t) A computation proof)).
  Proof.
    eapply (@Resumption.run_hoist (@host_action Host_t)
      (@Vm.Make.M.t Host_t F) (@Vm.Make.M.HostAPI.lift Host_t F)
      (@host_return Host_t) (@host_bind Host_t)
      (@Vm.Make.M._return Host_t F) (@Vm.Make.M.op_gtgteq Host_t F)
      (@machine_equiv Host_t F)).
    - intros X value state. reflexivity.
    - intros X left middle right Hleft Hright state.
      rewrite Hleft, Hright. reflexivity.
    - intros. eapply machine_bind_respects; eassumption.
    - intros. apply host_lift_return.
    - intros. apply host_lift_bind.
  Qed.

  Lemma observe_machine_run {A : Set}
      (computation : Resumption.t (@Vm.Make.M.t Host_t F) A)
      (proof : Resumption.converges computation)
      (state : @Vm.Make.MachineState.t Host_t F) :
    @Delay.run _ (ResultState.observe computation state)
      (ResultState.observe_converges proof state) =
    @Resumption.run (@Vm.Make.M.t Host_t F)
      (@Vm.Make.M._return Host_t F) (@Vm.Make.M.op_gtgteq Host_t F)
      A computation proof state.
  Proof. apply ResultState.run_observe. Qed.
End Observation.
