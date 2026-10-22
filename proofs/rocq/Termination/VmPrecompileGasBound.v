(** The precompile gas-spend primitive cannot increase remaining gas. *)

From Stdlib Require Import ZArith NArith Lia.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import MonadExecutionSpecs.Termination.VmUnsignedGas.
Require MonadVM.Precompiles.Utils.
Require MonadVM.Precompiles.
Require MonadVM.Evmc.
Require MonadVM.Gas.
Require MonadVM.Uint64.
Require MonadVM.Support.UintN.
Require MonadVM.Chain.Ethereum.
Require MonadVM.Byte_string.

Local Open Scope Z_scope.

Section PrecompileSpend.
Context `{U64 : RocqOfOCaml.Basics.Unreachable MonadVM.Uint64.t}.
Context `{UGas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.

Lemma precompile_numeric_spend_nonincreasing
    (raw : Z) (charge : N) :
  valid_int64_repr raw ->
  RocqOfOCaml.OCamlZ.of_int64_unsigned
    (MonadVM.Gas.to_uint64
      (_rocq_assumption_0 := U64)
      (MonadVM.Gas.of_uint64
        (_rocq_assumption_0 := UGas) raw - charge)%N)
  <= RocqOfOCaml.OCamlZ.of_int64_unsigned raw.
Proof.
  intro Hvalid.
  pose proof (unsigned_repr_in_range raw Hvalid)
    as [Hnonnegative Hupper].
  pose proof (@initial_gas_matches_unsigned UGas raw Hnonnegative)
    as Hinitial.
  unfold MonadVM.Gas.to_uint64.
  assert (Hremaining :
    (Z.of_N (MonadVM.Gas.of_uint64
      (_rocq_assumption_0 := UGas) raw - charge)%N < 2 ^ 64)%Z).
  { pose proof (N.le_sub_l
      (MonadVM.Gas.of_uint64 (_rocq_assumption_0 := UGas) raw)
      charge) as Hsub.
    apply N2Z.inj_le in Hsub.
    lia. }
  rewrite (@uintn_to_uint64_roundtrip U64 _ Hremaining).
  rewrite <- Hinitial.
  apply N2Z.inj_le.
  apply N.le_sub_l.
Qed.

Lemma generated_precompile_spend_success_bounded
    (charge : N) (msg msg' : MonadVM.Evmc.Message.t)
    (index index' : Z) :
  valid_int64_repr msg.(MonadVM.Evmc.Message.t.gas) ->
  @MonadVM.Precompiles.Utils.Precompile.spend_gas U64 UGas charge
    (msg, index) = (inl tt, (msg', index')) ->
  (RocqOfOCaml.OCamlZ.of_int64_unsigned
    msg'.(MonadVM.Evmc.Message.t.gas) <=
    RocqOfOCaml.OCamlZ.of_int64_unsigned
      msg.(MonadVM.Evmc.Message.t.gas))%Z.
Proof.
  intros Hvalid Hsuccess.
  unfold MonadVM.Precompiles.Utils.Precompile.spend_gas in Hsuccess.
  cbn in Hsuccess.
  destruct (MonadVM.Gas.op_lt
    (MonadVM.Gas.of_uint64 msg.(MonadVM.Evmc.Message.t.gas)) charge)
    eqn:Hout.
  - cbn in Hsuccess. discriminate Hsuccess.
  - cbn in Hsuccess.
    inversion Hsuccess; subst.
    cbn.
    unfold MonadVM.Gas.op_lt,
      MonadVM.Support.UintN.op_lt in Hout.
    apply N.ltb_ge in Hout.
    unfold MonadVM.Gas.op_minus,
      MonadVM.Support.UintN.op_minus.
    assert (Hguard :
      (charge <=? MonadVM.Gas.of_uint64
        msg.(MonadVM.Evmc.Message.t.gas))%N = true).
    { apply N.leb_le. exact Hout. }
    rewrite Hguard.
    apply precompile_numeric_spend_nonincreasing.
    exact Hvalid.
Qed.

Lemma generated_precompile_spend_success_valid
    (charge : N) (msg msg' : MonadVM.Evmc.Message.t)
    (index index' : Z) :
  valid_int64_repr msg.(MonadVM.Evmc.Message.t.gas) ->
  @MonadVM.Precompiles.Utils.Precompile.spend_gas U64 UGas charge
    (msg, index) = (inl tt, (msg', index')) ->
  valid_int64_repr msg'.(MonadVM.Evmc.Message.t.gas).
Proof.
  intros Hvalid Hsuccess.
  unfold MonadVM.Precompiles.Utils.Precompile.spend_gas in Hsuccess.
  cbn in Hsuccess.
  destruct (MonadVM.Gas.op_lt
    (MonadVM.Gas.of_uint64 msg.(MonadVM.Evmc.Message.t.gas)) charge)
    eqn:Hout.
  - cbn in Hsuccess. discriminate Hsuccess.
  - cbn in Hsuccess.
    inversion Hsuccess; subst.
    cbn.
    unfold MonadVM.Gas.op_lt,
      MonadVM.Support.UintN.op_lt in Hout.
    apply N.ltb_ge in Hout.
    unfold MonadVM.Gas.op_minus,
      MonadVM.Support.UintN.op_minus.
    assert (Hguard :
      (charge <=? MonadVM.Gas.of_uint64
        msg.(MonadVM.Evmc.Message.t.gas))%N = true).
    { apply N.leb_le. exact Hout. }
    rewrite Hguard.
    unfold MonadVM.Gas.to_uint64.
    apply (@uintn_to_uint64_valid U64).
    pose proof (unsigned_repr_in_range
      msg.(MonadVM.Evmc.Message.t.gas) Hvalid) as [_ Hupper].
    pose proof (@initial_gas_matches_unsigned UGas
      msg.(MonadVM.Evmc.Message.t.gas)) as Hinitial.
    assert (Hnonnegative :
      (0 <= RocqOfOCaml.OCamlZ.of_int64_unsigned
        msg.(MonadVM.Evmc.Message.t.gas))%Z).
    { pose proof (unsigned_repr_in_range
        msg.(MonadVM.Evmc.Message.t.gas) Hvalid) as [Hlower _].
      exact Hlower. }
    specialize (Hinitial Hnonnegative).
    pose proof (N.le_sub_l
      (MonadVM.Gas.of_uint64 msg.(MonadVM.Evmc.Message.t.gas))
      charge) as Hsub.
    apply N2Z.inj_le in Hsub.
    lia.
Qed.

Lemma generated_spend_then_return_bounded
    {A : Set} (output returned : A) (charge : N)
    (msg next : MonadVM.Evmc.Message.t) (index : Z) :
  valid_int64_repr msg.(MonadVM.Evmc.Message.t.gas) ->
  MonadVM.Precompiles.Utils.Precompile.op_letdollar
    (@MonadVM.Precompiles.Utils.Precompile.spend_gas U64 UGas charge)
    (fun _ : unit => MonadVM.Precompiles.Utils.Precompile._return output)
    (msg, 0) = (inl returned, (next, index)) ->
  (RocqOfOCaml.OCamlZ.of_int64_unsigned
    next.(MonadVM.Evmc.Message.t.gas) <=
    RocqOfOCaml.OCamlZ.of_int64_unsigned
      msg.(MonadVM.Evmc.Message.t.gas))%Z.
Proof.
  intros Hvalid Hsuccess.
  unfold MonadVM.Precompiles.Utils.Precompile.op_letdollar,
    MonadVM.Precompiles.Utils.Precompile.spend_gas,
    MonadVM.Precompiles.Utils.Precompile._return in Hsuccess.
  cbn in Hsuccess.
  destruct (MonadVM.Gas.op_lt
    (MonadVM.Gas.of_uint64 msg.(MonadVM.Evmc.Message.t.gas)) charge)
    eqn:Hout.
  - cbn in Hsuccess. discriminate Hsuccess.
  - cbn in Hsuccess.
    inversion Hsuccess; subst.
    cbn.
    unfold MonadVM.Gas.op_lt,
      MonadVM.Support.UintN.op_lt in Hout.
    apply N.ltb_ge in Hout.
    unfold MonadVM.Gas.op_minus,
      MonadVM.Support.UintN.op_minus.
    assert (Hguard :
      (charge <=? MonadVM.Gas.of_uint64
        msg.(MonadVM.Evmc.Message.t.gas))%N = true).
    { apply N.leb_le. exact Hout. }
    rewrite Hguard.
    apply precompile_numeric_spend_nonincreasing.
    exact Hvalid.
Qed.
End PrecompileSpend.

Section PrecompileRun.
Context `{UAddress :
  RocqOfOCaml.Basics.Unreachable MonadVM.Chain.Ethereum.Address.t}.
Context `{UUnit : RocqOfOCaml.Basics.Unreachable unit}.
Context `{UInt : RocqOfOCaml.Basics.Unreachable int}.

Lemma generated_precompile_run_preserves_gas_bound
    (msg : MonadVM.Evmc.Message.t)
    (impl : MonadVM.Precompiles.Utils.Precompile.t
      MonadVM.Byte_string.Bytes.t) :
  valid_int64_repr msg.(MonadVM.Evmc.Message.t.gas) ->
  (forall (output : MonadVM.Byte_string.Bytes.t)
      (next : MonadVM.Evmc.Message.t) (index : Z),
    impl (msg, 0) = (inl output, (next, index)) ->
    (RocqOfOCaml.OCamlZ.of_int64_unsigned
      next.(MonadVM.Evmc.Message.t.gas) <=
      RocqOfOCaml.OCamlZ.of_int64_unsigned
        msg.(MonadVM.Evmc.Message.t.gas))%Z) ->
  (RocqOfOCaml.OCamlZ.of_int64_unsigned
    (@MonadVM.Precompiles.Utils.Precompile.run
      UAddress UUnit UInt msg impl).(MonadVM.Evmc.Result.t.gas_left)
    <= RocqOfOCaml.OCamlZ.of_int64_unsigned
      msg.(MonadVM.Evmc.Message.t.gas))%Z.
Proof.
  intros Hvalid Himpl.
  unfold MonadVM.Precompiles.Utils.Precompile.run.
  destruct (impl (msg, 0)) as [[output | error] [next index]]
    eqn:Hresult.
  - cbn.
    eapply Himpl.
    reflexivity.
  - cbn.
    pose proof (unsigned_repr_in_range
      msg.(MonadVM.Evmc.Message.t.gas) Hvalid) as [Hnonnegative _].
    lia.
Qed.
End PrecompileRun.

Section IdentityPrecompile.
Context `{U64 : RocqOfOCaml.Basics.Unreachable MonadVM.Uint64.t}.
Context `{UGas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
Context `{UAddress :
  RocqOfOCaml.Basics.Unreachable MonadVM.Chain.Ethereum.Address.t}.
Context `{UUnit : RocqOfOCaml.Basics.Unreachable unit}.
Context `{UInt : RocqOfOCaml.Basics.Unreachable int}.

Lemma generated_identity_precompile_gas_bounded
    (msg : MonadVM.Evmc.Message.t) :
  valid_int64_repr msg.(MonadVM.Evmc.Message.t.gas) ->
  (RocqOfOCaml.OCamlZ.of_int64_unsigned
    (@MonadVM.Precompiles.identity
      U64 UGas UAddress UUnit UInt msg)
    .(MonadVM.Evmc.Result.t.gas_left)
    <= RocqOfOCaml.OCamlZ.of_int64_unsigned
      msg.(MonadVM.Evmc.Message.t.gas))%Z.
Proof.
  intro Hvalid.
  unfold MonadVM.Precompiles.identity.
  eapply (@generated_precompile_run_preserves_gas_bound
    UAddress UUnit UInt).
  - exact Hvalid.
  - intros output next index Himpl.
    cbn zeta in Himpl.
    eapply (@generated_spend_then_return_bounded U64 UGas);
      eauto.
Qed.
End IdentityPrecompile.

Section HashPrecompiles.
Context `{U64 : RocqOfOCaml.Basics.Unreachable MonadVM.Uint64.t}.
Context `{UGas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
Context `{UAddress :
  RocqOfOCaml.Basics.Unreachable MonadVM.Chain.Ethereum.Address.t}.
Context `{UUnit : RocqOfOCaml.Basics.Unreachable unit}.
Context `{UString : RocqOfOCaml.Basics.Unreachable string}.
Context `{UInt : RocqOfOCaml.Basics.Unreachable int}.

Lemma generated_sha256_precompile_gas_bounded
    (msg : MonadVM.Evmc.Message.t) :
  valid_int64_repr msg.(MonadVM.Evmc.Message.t.gas) ->
  (RocqOfOCaml.OCamlZ.of_int64_unsigned
    (@MonadVM.Precompiles.sha256
      U64 UGas UAddress UUnit UString UInt msg)
    .(MonadVM.Evmc.Result.t.gas_left)
    <= RocqOfOCaml.OCamlZ.of_int64_unsigned
      msg.(MonadVM.Evmc.Message.t.gas))%Z.
Proof.
  intro Hvalid.
  unfold MonadVM.Precompiles.sha256.
  eapply (@generated_precompile_run_preserves_gas_bound
    UAddress UUnit UInt).
  - exact Hvalid.
  - intros output next index Himpl.
    cbn zeta in Himpl.
    eapply (@generated_spend_then_return_bounded U64 UGas);
      eauto.
Qed.

Context `{UB20 :
  RocqOfOCaml.Basics.Unreachable MonadVM.Byte_string.B20.t}.
Context `{UAscii : RocqOfOCaml.Basics.Unreachable ascii}.

Lemma generated_ripemd160_precompile_gas_bounded
    (msg : MonadVM.Evmc.Message.t) :
  valid_int64_repr msg.(MonadVM.Evmc.Message.t.gas) ->
  (RocqOfOCaml.OCamlZ.of_int64_unsigned
    (@MonadVM.Precompiles.ripemd160
      U64 UGas UAddress UB20 UUnit UString UInt UAscii msg)
    .(MonadVM.Evmc.Result.t.gas_left)
    <= RocqOfOCaml.OCamlZ.of_int64_unsigned
      msg.(MonadVM.Evmc.Message.t.gas))%Z.
Proof.
  intro Hvalid.
  unfold MonadVM.Precompiles.ripemd160.
  eapply (@generated_precompile_run_preserves_gas_bound
    UAddress UUnit UInt).
  - exact Hvalid.
  - intros output next index Himpl.
    cbn zeta in Himpl.
    eapply (@generated_spend_then_return_bounded U64 UGas);
      eauto.
Qed.
End HashPrecompiles.
