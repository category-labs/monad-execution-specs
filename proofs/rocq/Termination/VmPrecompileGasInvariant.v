(** A compositional gas invariant for generated precompile computations. *)

From Stdlib Require Import ZArith Lia.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import MonadExecutionSpecs.Termination.VmUnsignedGas.
Require Import MonadExecutionSpecs.Termination.VmPrecompileGasBound.
Require Import MonadExecutionSpecs.Termination.PrecompileList.
Require MonadVM.Precompiles.Utils.
Require MonadVM.Evmc.
Require MonadVM.Gas.
Require MonadVM.Uint64.
Require MonadVM.Chain.Ethereum.
Require MonadVM.Byte_string.
Require MonadVM.Support.UintN.

Local Open Scope Z_scope.

Definition precompile_gas_safe {A : Set}
    (impl : MonadVM.Precompiles.Utils.Precompile.t A) : Prop :=
  forall (msg next : MonadVM.Evmc.Message.t) (index next_index : Z)
      (result : A),
    valid_int64_repr msg.(MonadVM.Evmc.Message.t.gas) ->
    impl (msg, index) = (inl result, (next, next_index)) ->
    valid_int64_repr next.(MonadVM.Evmc.Message.t.gas) /\
    (RocqOfOCaml.OCamlZ.of_int64_unsigned
      next.(MonadVM.Evmc.Message.t.gas) <=
      RocqOfOCaml.OCamlZ.of_int64_unsigned
        msg.(MonadVM.Evmc.Message.t.gas))%Z.

Lemma precompile_gas_safe_of_unchanged {A : Set}
    (impl : MonadVM.Precompiles.Utils.Precompile.t A) :
  (forall msg next index next_index result,
    impl (msg, index) = (inl result, (next, next_index)) ->
    next.(MonadVM.Evmc.Message.t.gas) =
      msg.(MonadVM.Evmc.Message.t.gas)) ->
  precompile_gas_safe impl.
Proof.
  intros Hunchanged msg next index next_index result Hvalid Hrun.
  rewrite (Hunchanged msg next index next_index result Hrun).
  split; [exact Hvalid | lia].
Qed.

Lemma precompile_return_gas_safe {A : Set} (value : A) :
  precompile_gas_safe
    (MonadVM.Precompiles.Utils.Precompile._return value).
Proof.
  unfold precompile_gas_safe.
  intros msg next index next_index result Hvalid Hrun.
  unfold MonadVM.Precompiles.Utils.Precompile._return in Hrun.
  cbn in Hrun.
  inversion Hrun; subst.
  split; [exact Hvalid | lia].
Qed.

Lemma precompile_get_gas_safe :
  precompile_gas_safe MonadVM.Precompiles.Utils.Precompile.get.
Proof.
  apply precompile_gas_safe_of_unchanged.
  intros msg next index next_index result Hrun.
  cbn in Hrun.
  inversion Hrun; reflexivity.
Qed.

Lemma precompile_bind_gas_safe {A B : Set}
    (first : MonadVM.Precompiles.Utils.Precompile.t A)
    (next : A -> MonadVM.Precompiles.Utils.Precompile.t B) :
  precompile_gas_safe first ->
  (forall value, precompile_gas_safe (next value)) ->
  precompile_gas_safe
    (MonadVM.Precompiles.Utils.Precompile.op_letdollar first next).
Proof.
  unfold precompile_gas_safe.
  intros Hfirst Hnext msg final index final_index result Hvalid Hrun.
  unfold MonadVM.Precompiles.Utils.Precompile.op_letdollar in Hrun.
  cbn in Hrun.
  destruct (first (msg, index)) as [[intermediate | error]
    [middle middle_index]] eqn:Hstep.
  - cbn in Hrun.
    pose proof (Hfirst msg middle index middle_index intermediate
      Hvalid Hstep) as [Hmiddle_valid Hmiddle_gas].
    pose proof (Hnext intermediate middle final middle_index
      final_index result Hmiddle_valid Hrun)
      as [Hfinal_valid Hfinal_gas].
    split; [exact Hfinal_valid | lia].
  - cbn in Hrun. discriminate Hrun.
Qed.

Lemma precompile_fmap_gas_safe {A B : Set}
    (convert : A -> B) (impl : MonadVM.Precompiles.Utils.Precompile.t A) :
  precompile_gas_safe impl ->
  precompile_gas_safe
    (MonadVM.Precompiles.Utils.Precompile.op_ltdollargt convert impl).
Proof.
  intro Himpl.
  change (precompile_gas_safe
    (MonadVM.Precompiles.Utils.Precompile.op_letdollar impl
      (fun value => MonadVM.Precompiles.Utils.Precompile._return
        (convert value)))).
  apply precompile_bind_gas_safe.
  - exact Himpl.
  - intro value. apply precompile_return_gas_safe.
Qed.

Lemma precompile_input_data_gas_safe :
  precompile_gas_safe MonadVM.Precompiles.Utils.Precompile.input_data.
Proof.
  unfold MonadVM.Precompiles.Utils.Precompile.input_data.
  eapply precompile_bind_gas_safe.
  - exact precompile_get_gas_safe.
  - intro state.
    destruct state as [msg index].
    apply precompile_return_gas_safe.
Qed.

Lemma precompile_advance_gas_safe (amount : Z) :
  precompile_gas_safe
    (MonadVM.Precompiles.Utils.Precompile.advance amount).
Proof.
  apply precompile_gas_safe_of_unchanged.
  intros msg next index next_index result Hrun.
  unfold MonadVM.Precompiles.Utils.Precompile.advance in Hrun.
  cbn in Hrun.
  inversion Hrun; reflexivity.
Qed.

Lemma precompile_byte_reader_gas_safe {bs : Set}
    (reader : {_ : unit @ MonadVM.Precompiles.Utils.Precompile.BYTES
      (t := bs)}) :
  precompile_gas_safe
    (MonadVM.Precompiles.Utils.Precompile.byte_reader reader).
Proof.
  destruct reader as [[] reader].
  unfold MonadVM.Precompiles.Utils.Precompile.byte_reader.
  eapply precompile_bind_gas_safe.
  - apply precompile_advance_gas_safe.
  - intro index.
    eapply precompile_bind_gas_safe.
    + exact precompile_input_data_gas_safe.
    + intro data. apply precompile_return_gas_safe.
Qed.

Lemma precompile_numeric_reader_gas_safe {num : Set}
    (reader : {repr : Set @
      MonadVM.Precompiles.Utils.Precompile.NUMERIC
        (Repr_t := repr) (t := num)}) :
  precompile_gas_safe
    (MonadVM.Precompiles.Utils.Precompile.numeric_reader reader).
Proof.
  destruct reader as [repr reader].
  unfold MonadVM.Precompiles.Utils.Precompile.numeric_reader.
  apply precompile_fmap_gas_safe.
  apply precompile_byte_reader_gas_safe.
Qed.

Lemma precompile_numeric_reader_le_gas_safe {num : Set}
    (reader : {repr : Set @
      MonadVM.Precompiles.Utils.Precompile.NUMERIC
        (Repr_t := repr) (t := num)}) :
  precompile_gas_safe
    (MonadVM.Precompiles.Utils.Precompile.numeric_reader_le reader).
Proof.
  destruct reader as [repr reader].
  unfold MonadVM.Precompiles.Utils.Precompile.numeric_reader_le.
  eapply precompile_bind_gas_safe.
  - apply precompile_byte_reader_gas_safe.
  - intro data. apply precompile_return_gas_safe.
Qed.

Lemma precompile_byte_gas_safe
    `{UAscii : RocqOfOCaml.Basics.Unreachable ascii} :
  precompile_gas_safe
    (@MonadVM.Precompiles.Utils.Precompile.byte UAscii).
Proof.
  unfold MonadVM.Precompiles.Utils.Precompile.byte.
  eapply precompile_bind_gas_safe.
  - apply precompile_advance_gas_safe.
  - intro index.
    eapply precompile_bind_gas_safe.
    + exact precompile_input_data_gas_safe.
    + intro data. apply precompile_return_gas_safe.
Qed.

Lemma precompile_fail_gas_safe {A : Set}
    (error : MonadVM.Evmc.Result.StatusCode.t) :
  precompile_gas_safe
    (@MonadVM.Precompiles.Utils.Precompile.fail A error).
Proof.
  unfold precompile_gas_safe.
  intros msg next index next_index result _ Hrun.
  cbn in Hrun.
  discriminate Hrun.
Qed.

Lemma precompile_ensure_gas_safe (condition : bool) :
  precompile_gas_safe
    (MonadVM.Precompiles.Utils.Precompile.ensure condition).
Proof.
  destruct condition.
  - apply precompile_return_gas_safe.
  - apply precompile_fail_gas_safe.
Qed.

Lemma precompile_when_gas_safe (condition : bool)
    (action : MonadVM.Precompiles.Utils.Precompile.t unit) :
  precompile_gas_safe action ->
  precompile_gas_safe
    (MonadVM.Precompiles.Utils.Precompile.when_ condition action).
Proof.
  intro Haction.
  destruct condition; cbn.
  - exact Haction.
  - apply precompile_return_gas_safe.
Qed.

Lemma precompile_option_or_fail_gas_safe {A : Set}
    (value : option A) :
  precompile_gas_safe
    (MonadVM.Precompiles.Utils.Precompile.Option.or_fail value).
Proof.
  destruct value as [value |].
  - apply precompile_return_gas_safe.
  - apply precompile_fail_gas_safe.
Qed.

Lemma precompile_bytes_value_gas_safe
    `{UBytes : RocqOfOCaml.Basics.Unreachable
      MonadVM.Byte_string.Bytes.t}
    `{UAscii : RocqOfOCaml.Basics.Unreachable ascii}
    (length : Z) :
  precompile_gas_safe
    (@MonadVM.Precompiles.Utils.Precompile.bytes_value
      UBytes UAscii length).
Proof.
  unfold MonadVM.Precompiles.Utils.Precompile.bytes_value.
  eapply precompile_bind_gas_safe.
  - apply precompile_advance_gas_safe.
  - intro index.
    eapply precompile_bind_gas_safe.
    + exact precompile_input_data_gas_safe.
    + intro data. apply precompile_return_gas_safe.
Qed.

Lemma precompile_pair_value_gas_safe {A B : Set}
    (first : MonadVM.Precompiles.Utils.Precompile.t A)
    (second : MonadVM.Precompiles.Utils.Precompile.t B) :
  precompile_gas_safe first ->
  precompile_gas_safe second ->
  precompile_gas_safe
    (MonadVM.Precompiles.Utils.Precompile.pair_value first second).
Proof.
  intros Hfirst Hsecond.
  unfold MonadVM.Precompiles.Utils.Precompile.pair_value.
  eapply precompile_bind_gas_safe.
  - exact Hfirst.
  - intro value.
    eapply precompile_bind_gas_safe.
    + exact Hsecond.
    + intro other. apply precompile_return_gas_safe.
Qed.

Lemma precompile_list_value_unfold {A : Set}
    `{UCount : RocqOfOCaml.Basics.Unreachable
      MonadVM.Support.UintN.t}
    (count : MonadVM.Support.UintN.t)
    (element : MonadVM.Precompiles.Utils.Precompile.t A) :
  @MonadVM.Precompiles.Utils.Precompile.list_value A UCount count element =
  if MonadVM.Support.UintN.is_zero count then
    MonadVM.Precompiles.Utils.Precompile._return nil
  else
    MonadVM.Precompiles.Utils.Precompile.op_letdollar element
      (fun head => MonadVM.Precompiles.Utils.Precompile.op_letdollar
        (@MonadVM.Precompiles.Utils.Precompile.list_value A UCount
          (MonadVM.Support.UintN.op_minus count
            MonadVM.Support.UintN.one) element)
        (fun tail => MonadVM.Precompiles.Utils.Precompile._return
          (head :: tail))).
Proof.
  unfold MonadVM.Precompiles.Utils.Precompile.list_value at 1.
  rewrite Fix_eq.
  - destruct (MonadVM.Support.UintN.is_zero count); reflexivity.
  - intros n f g Hfg.
    destruct n as [|positive]; cbn.
    + reflexivity.
    + rewrite (Hfg (MonadVM.Support.UintN.op_minus (N.pos positive)
        MonadVM.Support.UintN.one) _).
      reflexivity.
Qed.

Lemma precompile_list_value_gas_safe {A : Set}
    `{UCount : RocqOfOCaml.Basics.Unreachable
      MonadVM.Support.UintN.t}
    (count : MonadVM.Support.UintN.t)
    (element : MonadVM.Precompiles.Utils.Precompile.t A) :
  precompile_gas_safe element ->
  precompile_gas_safe
    (@MonadVM.Precompiles.Utils.Precompile.list_value A UCount
      count element).
Proof.
  intro Helement.
  revert count.
  apply (well_founded_induction
    (well_founded_ltof MonadVM.Support.UintN.t precompile_list_rank)).
  intros count IH.
  rewrite precompile_list_value_unfold.
  destruct (MonadVM.Support.UintN.is_zero count) eqn:Hzero.
  - apply precompile_return_gas_safe.
  - eapply precompile_bind_gas_safe.
    + exact Helement.
    + intro head.
      eapply precompile_bind_gas_safe.
      * apply IH.
        apply precompile_list_step_decreases.
        exact Hzero.
      * intro tail. apply precompile_return_gas_safe.
Qed.

Section SpendGas.
Context `{U64 : RocqOfOCaml.Basics.Unreachable MonadVM.Uint64.t}.
Context `{UGas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.

Lemma precompile_spend_gas_safe (charge : MonadVM.Gas.t) :
  precompile_gas_safe
    (@MonadVM.Precompiles.Utils.Precompile.spend_gas U64 UGas charge).
Proof.
  unfold precompile_gas_safe.
  intros msg next index next_index result Hvalid Hrun.
  destruct result.
  split.
  - eapply generated_precompile_spend_success_valid; eauto.
  - eapply generated_precompile_spend_success_bounded; eauto.
Qed.
End SpendGas.

Section Run.
Context `{UAddress : RocqOfOCaml.Basics.Unreachable
  MonadVM.Chain.Ethereum.Address.t}.
Context `{UUnit : RocqOfOCaml.Basics.Unreachable unit}.
Context `{UInt : RocqOfOCaml.Basics.Unreachable int}.

Lemma precompile_run_gas_safe_bounded
    (msg : MonadVM.Evmc.Message.t)
    (impl : MonadVM.Precompiles.Utils.Precompile.t
      MonadVM.Byte_string.Bytes.t) :
  valid_int64_repr msg.(MonadVM.Evmc.Message.t.gas) ->
  precompile_gas_safe impl ->
  (RocqOfOCaml.OCamlZ.of_int64_unsigned
    (@MonadVM.Precompiles.Utils.Precompile.run
      UAddress UUnit UInt msg impl).(MonadVM.Evmc.Result.t.gas_left)
    <= RocqOfOCaml.OCamlZ.of_int64_unsigned
      msg.(MonadVM.Evmc.Message.t.gas))%Z.
Proof.
  intros Hvalid Hsafe.
  eapply generated_precompile_run_preserves_gas_bound.
  - exact Hvalid.
  - intros output next index Hrun.
    exact (proj2 (Hsafe msg next 0 index output Hvalid Hrun)).
Qed.
End Run.
