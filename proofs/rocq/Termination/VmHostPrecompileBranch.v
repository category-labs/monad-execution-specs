(** Gas bounds for stateful host actions. *)

From Stdlib Require Import ZArith.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import MonadExecutionSpecs.Termination.VmUnsignedGas.
Require MonadVM.Host.
Require MonadVM.State.
Require MonadVM.Monad.

Section HostPrecompileBranch.
Context `{F : MonadVM.Host.Make.FArgs}.

Definition action_result_gas_bounded
    (msg : MonadVM.Evmc.Message.t)
    (action : (@MonadVM.Host.Make.M F).(MonadVM.Monad.State.State_result.t)
      MonadVM.Evmc.Result.t) : Prop :=
  forall state : MonadVM.State.TransactionState.t,
    valid_int64_repr msg.(MonadVM.Evmc.Message.t.gas) ->
    (RocqOfOCaml.OCamlZ.of_int64_unsigned
      (fst (action state)).(MonadVM.Evmc.Result.t.gas_left)
      <= RocqOfOCaml.OCamlZ.of_int64_unsigned
        msg.(MonadVM.Evmc.Message.t.gas))%Z.

End HostPrecompileBranch.
