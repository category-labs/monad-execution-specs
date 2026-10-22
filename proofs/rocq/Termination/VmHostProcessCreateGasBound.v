(** A generated CREATE call inherits gas bounds from VM execution. *)

From Stdlib Require Import ZArith NArith Lia.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import MonadExecutionSpecs.Termination.VmUnsignedGas.
Require Import MonadExecutionSpecs.Termination.VmHostPrecompileBranch.
Require Import MonadExecutionSpecs.Termination.VmHostActionGasInvariant.
Require Import MonadExecutionSpecs.Termination.VmHostCreateDepositGas.
Require Import MonadVM.Host.
Require MonadVM.Byte_string.
Require MonadVM.State.
Require MonadVM.Monad.
Require MonadVM.Gas.

Local Open Scope Z_scope.

Section HostProcessCreate.
Context `{F : MonadVM.Host.Make.FArgs}.
Context `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}.
Context `{_rocq_assumption_1 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U64.t}.
Context `{_rocq_assumption_2 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
Context `{_rocq_assumption_3 : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
Context `{_rocq_assumption_4 : RocqOfOCaml.Basics.Unreachable MonadVM.Chain.Ethereum.Address.t}.
Context `{_rocq_assumption_5 : RocqOfOCaml.Basics.Unreachable MonadVM.Byte_string.Bytes.t}.
Context `{_rocq_assumption_6 : RocqOfOCaml.Basics.Unreachable unit}.
Context `{_rocq_assumption_7 : RocqOfOCaml.Basics.Unreachable string}.
Context `{_rocq_assumption_8 : RocqOfOCaml.Basics.Unreachable int}.
Context `{_rocq_assumption_9 : RocqOfOCaml.Basics.Unreachable ascii}.
Context `{_rocq_assumption_10 : RocqOfOCaml.Basics.Unreachable int64}.
Context `{_rocq_assumption_11 : RocqOfOCaml.Basics.Unreachable
        MonadVM.Byte_string.B32.(MonadVM.Byte_string.Fixed.Fixed_result.t)}.

Lemma generated_host_process_create_gas_bounded_if_vm
    (msg : MonadVM.Evmc.Message.t) :
  (forall (child : MonadVM.Evmc.Message.t)
      (code : MonadVM.Byte_string.Bytes.t)
      (state : MonadVM.State.TransactionState.t),
    child.(MonadVM.Evmc.Message.t.gas) =
      msg.(MonadVM.Evmc.Message.t.gas) ->
    valid_int64_repr msg.(MonadVM.Evmc.Message.t.gas) ->
    let result := fst
      (((@MonadVM.Host.Make.Vm F).(MonadVM.Evmc.Vm.SIG.execute)
        child code) state) in
    valid_int64_repr result.(MonadVM.Evmc.Result.t.gas_left) /\
    (RocqOfOCaml.OCamlZ.of_int64_unsigned
      result.(MonadVM.Evmc.Result.t.gas_left)
      <= RocqOfOCaml.OCamlZ.of_int64_unsigned
        msg.(MonadVM.Evmc.Message.t.gas))%Z) ->
  @action_result_gas_bounded F msg
    (@MonadVM.Host.Make.process_create F
      _rocq_assumption_0 _rocq_assumption_1 _rocq_assumption_2 _rocq_assumption_3 _rocq_assumption_4
      _rocq_assumption_5 _rocq_assumption_6 _rocq_assumption_7 _rocq_assumption_8 _rocq_assumption_9
      _rocq_assumption_10 _rocq_assumption_11
      msg).
Proof.
  intro Hvm.
  unfold MonadVM.Host.Make.process_create.
  eapply host_state_bind_result_gas_bounded.
  intro create_address.
  eapply host_state_bind_result_gas_bounded.
  intro pre_existent_account.
  destruct (orb
    (MonadVM.Numeric.U64.op_ltgt
      pre_existent_account.(MonadVM.Chain.Ethereum.Account.t.nonce)
      (MonadVM.Numeric.U64.zero
        (_rocq_assumption_0 := _rocq_assumption_1)))
    (nequiv_decb
      pre_existent_account.(MonadVM.Chain.Ethereum.Account.t.code)
      MonadVM.Byte_string.Bytes.empty)) eqn:Hoccupied.
  - apply host_state_return_result_gas_bounded.
    intro Hvalid.
    pose proof (unsigned_repr_in_range _ Hvalid) as [Hnonnegative _].
    cbn. lia.
  - eapply host_state_bind_result_gas_bounded.
    intro ignored_access.
    eapply host_state_bind_result_gas_bounded.
    intro ignored_storage.
    eapply host_state_bind_result_gas_bounded.
    intro ignored_nonce.
    eapply host_state_bind_result_gas_bounded.
    intro transfer_ok.
    eapply host_state_bind_result_gas_bounded_if with
      (property := fun result =>
        valid_int64_repr result.(MonadVM.Evmc.Result.t.gas_left) /\
        (RocqOfOCaml.OCamlZ.of_int64_unsigned
          result.(MonadVM.Evmc.Result.t.gas_left)
          <= RocqOfOCaml.OCamlZ.of_int64_unsigned
            msg.(MonadVM.Evmc.Message.t.gas))%Z).
    + intros state Hvalid.
      destruct transfer_ok.
      * cbn zeta.
        eapply Hvm.
        -- reflexivity.
        -- exact Hvalid.
      * cbn.
        pose proof (unsigned_repr_in_range _ Hvalid)
          as [Hnonnegative _].
        split.
        -- unfold valid_int64_repr. lia.
        -- cbn. lia.
    + intros result_value [Hresult_valid Hresult_bound].
      destruct result_value.(MonadVM.Evmc.Result.t.status_code);
        try (apply host_state_return_result_gas_bounded;
          intro Hvalid; exact Hresult_bound).
      cbn zeta.
      lazymatch goal with
      | |- @action_result_gas_bounded _ _
          (match ?failure with _ => _ end) =>
          destruct failure as [error |] eqn:Hfailure
      end.
      * apply host_state_return_result_gas_bounded.
        intro Hvalid.
        pose proof (unsigned_repr_in_range _ Hvalid)
          as [Hnonnegative _].
        cbn. lia.
      * eapply host_state_bind_result_gas_bounded.
        intro ignored_write.
        apply host_state_return_result_gas_bounded.
        intro Hvalid.
        eapply host_create_code_deposit_bounded_by_message;
          [exact Hresult_valid | exact Hresult_bound |].
        repeat lazymatch type of Hfailure with
        | (if ?condition then _ else _) = None =>
            let H := fresh "Hcondition" in
            destruct condition eqn:H in Hfailure;
            cbn in Hfailure; try discriminate
        end.
        assumption.
Qed.
End HostProcessCreate.
