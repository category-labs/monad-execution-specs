(** State-only host actions preserve result gas laws through bind. *)

From Stdlib Require Import ZArith.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import MonadExecutionSpecs.Termination.VmUnsignedGas.
Require Import MonadExecutionSpecs.Termination.VmHostPrecompileBranch.
Require MonadVM.Host.
Require MonadVM.Monad.
Require MonadVM.Evmc.

Section HostAction.
Context `{F : MonadVM.Host.Make.FArgs}.

Lemma host_state_bind_result_gas_bounded {A : Set}
    (msg : MonadVM.Evmc.Message.t)
    (first : (@MonadVM.Host.Make.M F)
      .(MonadVM.Monad.State.State_result.t) A)
    (next : A -> (@MonadVM.Host.Make.M F)
      .(MonadVM.Monad.State.State_result.t) MonadVM.Evmc.Result.t) :
  (forall value, @action_result_gas_bounded F msg (next value)) ->
  @action_result_gas_bounded F msg
    ((@MonadVM.Host.Make.M F)
      .(MonadVM.Monad.State.State_result.op_letdollar) first next).
Proof.
  intro Hnext.
  unfold action_result_gas_bounded in *.
  intros state Hvalid.
  cbn.
  destruct (first state) as [value state'].
  exact (Hnext value state' Hvalid).
Qed.

Lemma host_state_bind_result_gas_bounded_if {A : Set}
    (msg : MonadVM.Evmc.Message.t)
    (first : (@MonadVM.Host.Make.M F)
      .(MonadVM.Monad.State.State_result.t) A)
    (next : A -> (@MonadVM.Host.Make.M F)
      .(MonadVM.Monad.State.State_result.t) MonadVM.Evmc.Result.t)
    (property : A -> Prop) :
  (forall state, valid_int64_repr msg.(MonadVM.Evmc.Message.t.gas) ->
    property (fst (first state))) ->
  (forall value, property value ->
    @action_result_gas_bounded F msg (next value)) ->
  @action_result_gas_bounded F msg
    ((@MonadVM.Host.Make.M F)
      .(MonadVM.Monad.State.State_result.op_letdollar) first next).
Proof.
  intros Hfirst Hnext state Hvalid.
  cbn.
  destruct (first state) as [value next_state] eqn:Hrun.
  apply (Hnext value).
  - pose proof (Hfirst state Hvalid) as Hproperty.
    rewrite Hrun in Hproperty. exact Hproperty.
  - exact Hvalid.
Qed.

Lemma host_state_return_result_gas_bounded
    (msg : MonadVM.Evmc.Message.t)
    (result : MonadVM.Evmc.Result.t) :
  (forall valid : valid_int64_repr msg.(MonadVM.Evmc.Message.t.gas),
    (RocqOfOCaml.OCamlZ.of_int64_unsigned
      result.(MonadVM.Evmc.Result.t.gas_left)
      <= RocqOfOCaml.OCamlZ.of_int64_unsigned
        msg.(MonadVM.Evmc.Message.t.gas))%Z) ->
  @action_result_gas_bounded F msg
    ((@MonadVM.Host.Make.M F)
      .(MonadVM.Monad.State.State_result._return)
      (a := MonadVM.Evmc.Result.t) result).
Proof.
  intros Hbound state Hvalid.
  cbn.
  exact (Hbound Hvalid).
Qed.
End HostAction.
