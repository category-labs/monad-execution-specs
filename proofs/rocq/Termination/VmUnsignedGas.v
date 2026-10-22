(** The EVMC message gas field is an unsigned 64-bit quantity. *)

From Stdlib Require Import ZArith Lia.
Require Import RocqOfOCaml.RocqOfOCaml.
Require MonadVM.Gas.
Require MonadVM.Numeric.
Require MonadVM.Support.UintN.
Require MonadVM.Support.Variants.
Require MonadVM.Vm.
Require Import MonadExecutionSpecs.Termination.VmCallGas.

Local Open Scope Z_scope.

Section UnsignedInt64.
Context `{U64 : RocqOfOCaml.Basics.Unreachable int64}.

Lemma int64_unsigned_roundtrip (value : Z) :
  0 <= value < 2 ^ 64 ->
  RocqOfOCaml.OCamlZ.of_int64_unsigned
    (RocqOfOCaml.OCamlZ.to_int64_unsigned value) = value.
Proof.
  intro Hrange.
  unfold RocqOfOCaml.OCamlZ.to_int64_unsigned.
  assert (Hlower : (0 <=? value) = true) by
    (apply Z.leb_le; lia).
  assert (Hupper : (value <? 2 ^ 64) = true) by
    (apply Z.ltb_lt; lia).
  rewrite Hlower, Hupper.
  cbn [andb].
  unfold RocqOfOCaml.OCamlZ.signed_repr,
    RocqOfOCaml.OCamlZ.of_int64_unsigned.
  replace (Z.pred 64) with 63 by reflexivity.
  rewrite Z.mod_small by lia.
  destruct (Z.leb (2 ^ 63) value) eqn:Hsign.
  - apply Z.leb_le in Hsign.
    assert (Hnegative : (value - 2 ^ 64 <? 0) = true) by
      (apply Z.ltb_lt; lia).
    rewrite Hnegative. lia.
  - apply Z.leb_gt in Hsign.
    assert (Hnonnegative : (value <? 0) = false) by
      (apply Z.ltb_ge; lia).
    rewrite Hnonnegative. lia.
Qed.

Lemma uintn_to_uint64_roundtrip (value : MonadVM.Support.UintN.t) :
  (Z.of_N value < 2 ^ 64)%Z ->
  RocqOfOCaml.OCamlZ.of_int64_unsigned
    (MonadVM.Support.UintN.to_uint64 value) = Z.of_N value.
Proof.
  intro Hupper.
  unfold MonadVM.Support.UintN.to_uint64,
    MonadVM.Support.UintN.to_z.
  apply int64_unsigned_roundtrip.
  lia.
Qed.

Lemma int64_signed_unsigned_equal (value : Z) :
  0 <= value < 2 ^ 63 ->
  RocqOfOCaml.OCamlZ.to_int64 value =
    RocqOfOCaml.OCamlZ.to_int64_unsigned value.
Proof.
  intro Hrange.
  unfold RocqOfOCaml.OCamlZ.to_int64,
    RocqOfOCaml.OCamlZ.to_int64_unsigned,
    RocqOfOCaml.OCamlZ.checked_signed,
    RocqOfOCaml.OCamlZ.fits_signed,
    RocqOfOCaml.OCamlZ.signed_min,
    RocqOfOCaml.OCamlZ.signed_max.
  replace (Z.pred 64) with 63 by reflexivity.
  assert (Hmin : (- (2 ^ 63) <=? value) = true) by
    (apply Z.leb_le; lia).
  assert (Hmax : (value <=? Z.pred (2 ^ 63)) = true) by
    (apply Z.leb_le; lia).
  assert (Hnonnegative : (0 <=? value) = true) by
    (apply Z.leb_le; lia).
  assert (Hunsigned : (value <? 2 ^ 64) = true) by
    (apply Z.ltb_lt; lia).
  rewrite Hmin, Hmax, Hnonnegative, Hunsigned.
  cbn [andb].
  unfold RocqOfOCaml.OCamlZ.signed_repr.
  replace (Z.pred 64) with 63 by reflexivity.
  rewrite Z.mod_small by lia.
  assert (Hsign : (2 ^ 63 <=? value) = false) by
    (apply Z.leb_gt; lia).
  rewrite Hsign.
  reflexivity.
Qed.

Lemma int64_unsigned_small_identity (value : Z) :
  0 <= value < 2 ^ 63 ->
  RocqOfOCaml.OCamlZ.to_int64_unsigned value = value.
Proof.
  intro Hrange.
  unfold RocqOfOCaml.OCamlZ.to_int64_unsigned,
    RocqOfOCaml.OCamlZ.signed_repr.
  replace (Z.pred 64) with 63 by reflexivity.
  assert (Hnonnegative : (0 <=? value) = true) by
    (apply Z.leb_le; lia).
  assert (Hunsigned : (value <? 2 ^ 64) = true) by
    (apply Z.ltb_lt; lia).
  rewrite Hnonnegative, Hunsigned.
  cbn [andb].
  rewrite Z.mod_small by lia.
  assert (Hsign : (2 ^ 63 <=? value) = false) by
    (apply Z.leb_gt; lia).
  rewrite Hsign.
  reflexivity.
Qed.

Context `{UGas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.

Lemma uintn_to_int64_small_identity
    (value : MonadVM.Support.UintN.t) :
  (Z.of_N value < 2 ^ 63)%Z ->
  MonadVM.Support.UintN.to_int64 value = Z.of_N value.
Proof.
  intro Hbound.
  unfold MonadVM.Support.UintN.to_int64,
    MonadVM.Support.UintN.to_z.
  rewrite int64_signed_unsigned_equal by lia.
  apply int64_unsigned_small_identity.
  lia.
Qed.

Lemma uintn_signed_roundtrip (value : MonadVM.Support.UintN.t) :
  (Z.of_N value < 2 ^ 63)%Z ->
  RocqOfOCaml.OCamlZ.of_int64_unsigned
    (MonadVM.Support.UintN.to_int64 value) = Z.of_N value.
Proof.
  intro Hbound.
  unfold MonadVM.Support.UintN.to_int64,
    MonadVM.Support.UintN.to_z.
  rewrite int64_signed_unsigned_equal by lia.
  apply int64_unsigned_roundtrip.
  lia.
Qed.

Lemma create_message_signed_unsigned_equal
    (available : MonadVM.Support.UintN.t) :
  (Z.of_N available < 2 ^ 63)%Z ->
  MonadVM.Support.UintN.to_int64
    (MonadVM.Gas.minus_1_64th available) =
  MonadVM.Support.UintN.to_uint64
    (MonadVM.Gas.minus_1_64th available).
Proof.
  intro Havailable.
  unfold MonadVM.Support.UintN.to_int64,
    MonadVM.Support.UintN.to_uint64,
    MonadVM.Support.UintN.to_z.
  apply int64_signed_unsigned_equal.
  pose proof (create_forwarded_le available) as Hforwarded.
  lia.
Qed.

Lemma create_message_gas_roundtrip
    (available : MonadVM.Support.UintN.t) :
  (Z.of_N available < 2 ^ 64)%Z ->
  RocqOfOCaml.OCamlZ.of_int64_unsigned
    (MonadVM.Support.UintN.to_uint64
      (MonadVM.Gas.minus_1_64th available)) =
    Z.of_N (MonadVM.Gas.minus_1_64th available).
Proof.
  intro Havailable.
  apply uintn_to_uint64_roundtrip.
  pose proof (create_forwarded_le available) as Hforwarded.
  lia.
Qed.

Lemma create_message_signed_roundtrip
    (available : MonadVM.Support.UintN.t) :
  (Z.of_N available < 2 ^ 63)%Z ->
  RocqOfOCaml.OCamlZ.of_int64_unsigned
    (MonadVM.Support.UintN.to_int64
      (MonadVM.Gas.minus_1_64th available)) =
    Z.of_N (MonadVM.Gas.minus_1_64th available).
Proof.
  intro Havailable.
  rewrite create_message_signed_unsigned_equal by exact Havailable.
  apply create_message_gas_roundtrip.
  lia.
Qed.
End UnsignedInt64.

Section InitialGas.
Context `{UGas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.

Definition valid_int64_repr (raw : Z) : Prop :=
  (- (2 ^ 63) <= raw < 2 ^ 63)%Z.

Lemma int64_unsigned_conversion_valid
    `{U64 : RocqOfOCaml.Basics.Unreachable int64}
    (value : Z) :
  0 <= value < 2 ^ 64 ->
  valid_int64_repr (RocqOfOCaml.OCamlZ.to_int64_unsigned value).
Proof.
  intro Hrange.
  unfold valid_int64_repr,
    RocqOfOCaml.OCamlZ.to_int64_unsigned,
    RocqOfOCaml.OCamlZ.signed_repr.
  replace (Z.pred 64) with 63 by reflexivity.
  assert (Hnonnegative : (0 <=? value) = true) by
    (apply Z.leb_le; lia).
  assert (Hunsigned : (value <? 2 ^ 64) = true) by
    (apply Z.ltb_lt; lia).
  rewrite Hnonnegative, Hunsigned.
  cbn [andb].
  rewrite Z.mod_small by lia.
  destruct (2 ^ 63 <=? value) eqn:Hsign.
  - apply Z.leb_le in Hsign. split; lia.
  - apply Z.leb_gt in Hsign. split; lia.
Qed.

Lemma uintn_to_uint64_valid
    `{U64 : RocqOfOCaml.Basics.Unreachable int64}
    (value : MonadVM.Support.UintN.t) :
  (Z.of_N value < 2 ^ 64)%Z ->
  valid_int64_repr (MonadVM.Support.UintN.to_uint64
    (_rocq_assumption_0 := U64) value).
Proof.
  intro Hbound.
  unfold MonadVM.Support.UintN.to_uint64,
    MonadVM.Support.UintN.to_z.
  apply (@int64_unsigned_conversion_valid U64).
  lia.
Qed.

Lemma unsigned_repr_in_range (raw : Z) :
  valid_int64_repr raw ->
  (0 <= RocqOfOCaml.OCamlZ.of_int64_unsigned raw < 2 ^ 64)%Z.
Proof.
  unfold valid_int64_repr,
    RocqOfOCaml.OCamlZ.of_int64_unsigned.
  intro Hvalid.
  destruct (Z.ltb raw 0) eqn:Hnegative.
  - apply Z.ltb_lt in Hnegative. lia.
  - apply Z.ltb_ge in Hnegative. lia.
Qed.

Lemma initial_gas_matches_unsigned (raw : Z) :
  (0 <= RocqOfOCaml.OCamlZ.of_int64_unsigned raw)%Z ->
  Z.of_N (MonadVM.Gas.of_uint64 raw) =
    RocqOfOCaml.OCamlZ.of_int64_unsigned raw.
Proof.
  intro Hnonnegative.
  unfold MonadVM.Gas.of_uint64,
    MonadVM.Support.UintN.of_uint64,
    MonadVM.Support.UintN.of_z_exn,
    MonadVM.Support.UintN.of_z_opt,
    MonadVM.Support.UintN.in_range.
  assert (Hguard :
    Z.leb 0 (RocqOfOCaml.OCamlZ.of_int64_unsigned raw) = true).
  { apply Z.leb_le. exact Hnonnegative. }
  rewrite Hguard.
  apply Z2N.id.
  exact Hnonnegative.
Qed.

Lemma initial_gas_fits_uint64 (raw : Z) :
  valid_int64_repr raw ->
  (Z.of_N (MonadVM.Gas.of_uint64 raw) < 2 ^ 64)%Z.
Proof.
  intro Hvalid.
  pose proof (unsigned_repr_in_range raw Hvalid)
    as [Hnonnegative Hupper].
  unfold MonadVM.Gas.of_uint64,
    MonadVM.Support.UintN.of_uint64,
    MonadVM.Support.UintN.of_z_exn,
    MonadVM.Support.UintN.of_z_opt,
    MonadVM.Support.UintN.in_range.
  assert (Hguard :
    Z.leb 0 (RocqOfOCaml.OCamlZ.of_int64_unsigned raw) = true).
  { apply Z.leb_le. exact Hnonnegative. }
  rewrite Hguard.
  rewrite Z2N.id by exact Hnonnegative.
  exact Hupper.
Qed.

Lemma initial_gas_fits_signed_int64 (raw : Z) :
  0 <= raw < 2 ^ 63 ->
  (Z.of_N (MonadVM.Gas.of_uint64 raw) < 2 ^ 63)%Z.
Proof.
  intros [Hnonnegative Hupper].
  unfold MonadVM.Gas.of_uint64,
    MonadVM.Support.UintN.of_uint64,
    MonadVM.Support.UintN.of_z_exn,
    MonadVM.Support.UintN.of_z_opt,
    MonadVM.Support.UintN.in_range,
    RocqOfOCaml.OCamlZ.of_int64_unsigned.
  assert (Hsign : (raw <? 0) = false) by
    (apply Z.ltb_ge; lia).
  rewrite Hsign.
  assert (Hguard : (0 <=? raw) = true) by
    (apply Z.leb_le; lia).
  rewrite Hguard.
  rewrite Z2N.id by exact Hnonnegative.
  exact Hupper.
Qed.
End InitialGas.

Section InitialMachineState.
Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
Context `{U :
  RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}.
Context `{U256 :
  RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
Context `{I :
  RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.Integer.t}.
Context `{V : RocqOfOCaml.Basics.Unreachable unit}.

Lemma initial_machine_gas_matches_unsigned
    (host : Host_t) (raw : Z)
    (memory_capacity : MonadVM.Support.UintN.t) :
  (0 <= RocqOfOCaml.OCamlZ.of_int64_unsigned raw)%Z ->
  let state := MonadVM.Vm.Make.MachineState.initial host
    (MonadVM.Gas.of_uint64 raw) memory_capacity in
  Z.of_N state.(MonadVM.Vm.Make.MachineState.t.gas) =
    RocqOfOCaml.OCamlZ.of_int64_unsigned raw.
Proof.
  intro Hnonnegative.
  change (Z.of_N (MonadVM.Gas.of_uint64 raw) =
    RocqOfOCaml.OCamlZ.of_int64_unsigned raw).
  apply initial_gas_matches_unsigned.
  exact Hnonnegative.
Qed.

Lemma initial_machine_gas_fits_uint64
    (host : Host_t) (raw : Z)
    (memory_capacity : MonadVM.Support.UintN.t) :
  valid_int64_repr raw ->
  let state := MonadVM.Vm.Make.MachineState.initial host
    (MonadVM.Gas.of_uint64 raw) memory_capacity in
  (Z.of_N state.(MonadVM.Vm.Make.MachineState.t.gas) < 2 ^ 64)%Z.
Proof.
  intro Hvalid.
  change (Z.of_N (MonadVM.Gas.of_uint64 raw) < 2 ^ 64)%Z.
  apply initial_gas_fits_uint64.
  exact Hvalid.
Qed.

Lemma initial_machine_gas_fits_signed_int64
    (host : Host_t) (raw : Z)
    (memory_capacity : MonadVM.Support.UintN.t) :
  0 <= raw < 2 ^ 63 ->
  let state := MonadVM.Vm.Make.MachineState.initial host
    (MonadVM.Gas.of_uint64 raw) memory_capacity in
  (Z.of_N state.(MonadVM.Vm.Make.MachineState.t.gas) < 2 ^ 63)%Z.
Proof.
  intro Hvalid.
  change (Z.of_N (MonadVM.Gas.of_uint64 raw) < 2 ^ 63)%Z.
  apply initial_gas_fits_signed_int64.
  exact Hvalid.
Qed.
End InitialMachineState.

Section ForwardedCallGas.
Context `{U256 :
  RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
Context `{U64 : RocqOfOCaml.Basics.Unreachable int64}.
Context `{UGas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.

Lemma u256_forwarded_gas_roundtrip (value : N) :
  (Z.of_N value < 2 ^ 64)%Z ->
  RocqOfOCaml.OCamlZ.of_int64_unsigned
    (MonadVM.Numeric.U256.to_uint64
      (_rocq_assumption_0 := U64)
      (MonadVM.Numeric.U256.of_uint_exn
        (_rocq_assumption_0 := U256) value)) = Z.of_N value.
Proof.
  intro Hbound.
  unfold MonadVM.Numeric.U256.of_uint_exn,
    MonadVM.Numeric.U256.to_uint64.
  cbn.
  unfold MonadVM.Numeric.Make.to_uint64,
    MonadVM.Numeric.Make.of_z_exn,
    MonadVM.Numeric.Make.of_z_opt,
    MonadVM.Numeric.Make.to_z.
  cbn.
  unfold MonadVM.Numeric.Make.Impl.of_z_opt,
    MonadVM.Numeric.Make.Impl.to_z.
  cbn.
  unfold MonadVM.Numeric.Make.Impl.in_range,
    MonadVM.Support.UintN.to_z.
  cbn.
  pose proof (N2Z.is_nonneg value) as Hnonnegative.
  assert (Hlower : (Z.of_N value >=? Z.zero) = true).
  { apply Z.geb_le.
    exact Hnonnegative. }
  assert (Hupper :
    (Z.of_N value <=?
      115792089237316195423570985008687907853269984665640564039457584007913129639935)
      = true) by (apply Z.leb_le; lia).
  rewrite ?Hlower, ?Hupper.
  cbn.
  apply int64_unsigned_roundtrip.
  lia.
Qed.

Lemma u256_forwarded_gas_small_identity (value : N) :
  (Z.of_N value < 2 ^ 63)%Z ->
  MonadVM.Numeric.U256.to_uint64
    (_rocq_assumption_0 := U64)
    (MonadVM.Numeric.U256.of_uint_exn
      (_rocq_assumption_0 := U256) value) = Z.of_N value.
Proof.
  intro Hbound.
  unfold MonadVM.Numeric.U256.of_uint_exn,
    MonadVM.Numeric.U256.to_uint64.
  cbn.
  unfold MonadVM.Numeric.Make.to_uint64,
    MonadVM.Numeric.Make.of_z_exn,
    MonadVM.Numeric.Make.of_z_opt,
    MonadVM.Numeric.Make.to_z.
  cbn.
  unfold MonadVM.Numeric.Make.Impl.of_z_opt,
    MonadVM.Numeric.Make.Impl.to_z.
  cbn.
  unfold MonadVM.Numeric.Make.Impl.in_range,
    MonadVM.Support.UintN.to_z.
  cbn.
  pose proof (N2Z.is_nonneg value) as Hnonnegative.
  assert (Hlower : (Z.of_N value >=? Z.zero) = true).
  { apply Z.geb_le. exact Hnonnegative. }
  assert (Hupper :
    (Z.of_N value <=?
      115792089237316195423570985008687907853269984665640564039457584007913129639935)
      = true) by (apply Z.leb_le; lia).
  rewrite ?Hlower, ?Hupper.
  cbn.
  apply int64_unsigned_small_identity.
  lia.
Qed.

Lemma u256_forwarded_uint_roundtrip
    `{Uuint : RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}
    (value : N) :
  (Z.of_N value < 2 ^ 64)%Z ->
  MonadVM.Numeric.U256.to_uint
    (_rocq_assumption_0 := Uuint)
    (MonadVM.Numeric.U256.of_uint_exn
      (_rocq_assumption_0 := U256) value) = value.
Proof.
  intro Hbound.
  unfold MonadVM.Numeric.U256.of_uint_exn,
    MonadVM.Numeric.U256.to_uint.
  cbn.
  unfold MonadVM.Numeric.Make.of_z_exn,
    MonadVM.Numeric.Make.of_z_opt,
    MonadVM.Numeric.Make.to_z.
  cbn.
  unfold MonadVM.Numeric.Make.Impl.of_z_opt,
    MonadVM.Numeric.Make.Impl.to_z.
  cbn.
  unfold MonadVM.Numeric.Make.Impl.in_range,
    MonadVM.Support.UintN.to_z.
  cbn.
  pose proof (N2Z.is_nonneg value) as Hnonnegative.
  assert (Hlower : (Z.of_N value >=? Z.zero) = true).
  { apply Z.geb_le. exact Hnonnegative. }
  assert (Hupper :
    (Z.of_N value <=?
      115792089237316195423570985008687907853269984665640564039457584007913129639935)
      = true) by (apply Z.leb_le; lia).
  rewrite ?Hlower, ?Hupper.
  cbn.
  unfold MonadVM.Support.UintN.of_z_exn,
    MonadVM.Support.UintN.of_z_opt,
    MonadVM.Support.UintN.in_range.
  cbn.
  unfold MonadVM.Numeric.TwosComplement.Unsigned.to_uint.
  unfold MonadVM.Numeric.Make.to_z,
    MonadVM.Numeric.Make.Impl.to_z,
    MonadVM.Support.UintN.of_z_exn,
    MonadVM.Support.UintN.of_z_opt,
    MonadVM.Support.UintN.in_range.
  cbn.
  unfold MonadVM.Numeric.Make.to_z.
  assert (Huint_nonnegative : (0 <=? Z.of_N value) = true)
    by (apply Z.leb_le; lia).
  rewrite ?Huint_nonnegative.
  cbn.
  unfold MonadVM.Numeric.Make.to_z.
  unfold MonadVM.Numeric.Make.Impl.to_z.
  cbn.
  rewrite ?Huint_nonnegative.
  cbn.
  apply N2Z.id.
Qed.

Lemma call_forwarded_fits_uint64
    (transfer : bool)
    (status : MonadVM.Support.Variants.AccessStatus.t)
    (requested before memory access delegation new_account : N) :
  let transfer_cost := if transfer then MonadVM.Gas.call_value else 0%N in
  let extra := (access + delegation + transfer_cost + new_account)%N in
  let quote :=
    MonadVM.Gas.call_gas_value transfer requested before memory extra in
  (Z.of_N before < 2 ^ 64)%Z ->
  (MonadVM.Gas.account_access_cost status <= access)%N ->
  (quote.(MonadVM.Gas.call_gas.caller_spent_gas) + memory <= before)%N ->
  (Z.of_N quote.(MonadVM.Gas.call_gas.callee_available_gas) < 2 ^ 64)%Z.
Proof.
  cbn zeta.
  intros Hbefore Haccess Hspent.
  pose proof (call_not_made_decreases transfer status requested before
    memory access delegation new_account Haccess Hspent) as Hdecrease.
  cbn zeta in Hdecrease.
  lia.
Qed.

Lemma call_quote_message_gas_roundtrip
    (transfer : bool)
    (status : MonadVM.Support.Variants.AccessStatus.t)
    (requested before memory access delegation new_account : N) :
  let transfer_cost := if transfer then MonadVM.Gas.call_value else 0%N in
  let extra := (access + delegation + transfer_cost + new_account)%N in
  let quote :=
    MonadVM.Gas.call_gas_value transfer requested before memory extra in
  (Z.of_N before < 2 ^ 64)%Z ->
  (MonadVM.Gas.account_access_cost status <= access)%N ->
  (quote.(MonadVM.Gas.call_gas.caller_spent_gas) + memory <= before)%N ->
  RocqOfOCaml.OCamlZ.of_int64_unsigned
    (MonadVM.Numeric.U256.to_uint64
      (_rocq_assumption_0 := U64)
      (MonadVM.Numeric.U256.of_uint_exn
        (_rocq_assumption_0 := U256)
        quote.(MonadVM.Gas.call_gas.callee_available_gas))) =
    Z.of_N quote.(MonadVM.Gas.call_gas.callee_available_gas).
Proof.
  cbn zeta.
  intros Hbefore Haccess Hspent.
  apply u256_forwarded_gas_roundtrip.
  eapply call_forwarded_fits_uint64; eauto.
Qed.
End ForwardedCallGas.

Section ChildMessageInitialGas.
Context `{U256 :
  RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
Context `{U64 : RocqOfOCaml.Basics.Unreachable int64}.
Context `{UGas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.

Lemma call_message_initial_gas_preserves_transaction_cap
    (transfer : bool)
    (status : MonadVM.Support.Variants.AccessStatus.t)
    (requested before memory access delegation new_account : N) :
  let transfer_cost := if transfer then MonadVM.Gas.call_value else 0%N in
  let extra := (access + delegation + transfer_cost + new_account)%N in
  let quote :=
    MonadVM.Gas.call_gas_value transfer requested before memory extra in
  (MonadVM.Gas.account_access_cost status <= access)%N ->
  (quote.(MonadVM.Gas.call_gas.caller_spent_gas) + memory <= before)%N ->
  (Z.of_N before <= 30_000_000)%Z ->
  (Z.of_N (MonadVM.Gas.of_uint64
    (MonadVM.Numeric.U256.to_uint64
      (_rocq_assumption_0 := U64)
      (MonadVM.Numeric.U256.of_uint_exn
        (_rocq_assumption_0 := U256)
        quote.(MonadVM.Gas.call_gas.callee_available_gas))))
    <= 30_000_000)%Z.
Proof.
  cbn zeta.
  intros Haccess Hspent Hcap.
  assert (Hbefore : (Z.of_N before < 2 ^ 64)%Z) by lia.
  pose proof (@call_quote_message_gas_roundtrip U256 U64 UGas
    transfer status requested before memory access delegation new_account
    Hbefore Haccess Hspent)
    as Hroundtrip.
  cbn zeta in Hroundtrip.
  pose proof (call_child_gas_preserves_transaction_cap transfer status
    requested before memory access delegation new_account
    Haccess Hspent Hcap) as Hchild.
  cbn zeta in Hchild.
  rewrite initial_gas_matches_unsigned.
  - rewrite Hroundtrip. exact Hchild.
  - rewrite Hroundtrip. lia.
Qed.

Lemma create_message_initial_gas_preserves_transaction_cap
    (before memory initcode : N) :
  let charge := (memory + MonadVM.Gas.create_cost + initcode)%N in
  (charge <= before)%N ->
  (Z.of_N before <= 30_000_000)%Z ->
  (Z.of_N (MonadVM.Gas.of_uint64
    (MonadVM.Support.UintN.to_int64
      (MonadVM.Gas.minus_1_64th (before - charge)%N)))
    <= 30_000_000)%Z.
Proof.
  cbn zeta.
  intros Hcharge Hcap.
  assert (Havailable :
    (Z.of_N (before - (memory + MonadVM.Gas.create_cost + initcode))%N
      < 2 ^ 63)%Z) by lia.
  pose proof (create_message_signed_roundtrip
    (before - (memory + MonadVM.Gas.create_cost + initcode))%N Havailable)
    as Hroundtrip.
  pose proof (create_child_gas_preserves_transaction_cap
    before memory initcode Hcharge Hcap) as Hchild.
  cbn zeta in Hchild.
  rewrite initial_gas_matches_unsigned.
  - rewrite Hroundtrip. exact Hchild.
  - rewrite Hroundtrip. lia.
Qed.

Lemma call_message_signed_gas_range
    (transfer : bool)
    (status : MonadVM.Support.Variants.AccessStatus.t)
    (requested before memory access delegation new_account : N) :
  let transfer_cost := if transfer then MonadVM.Gas.call_value else 0%N in
  let extra := (access + delegation + transfer_cost + new_account)%N in
  let quote :=
    MonadVM.Gas.call_gas_value transfer requested before memory extra in
  let raw := MonadVM.Numeric.U256.to_uint64
    (_rocq_assumption_0 := U64)
    (MonadVM.Numeric.U256.of_uint_exn
      (_rocq_assumption_0 := U256)
      quote.(MonadVM.Gas.call_gas.callee_available_gas)) in
  (MonadVM.Gas.account_access_cost status <= access)%N ->
  (quote.(MonadVM.Gas.call_gas.caller_spent_gas) + memory <= before)%N ->
  (Z.of_N before <= 30_000_000)%Z ->
  (0 <= raw <= 30_000_000)%Z.
Proof.
  cbn zeta.
  intros Haccess Hspent Hcap.
  pose proof (call_child_gas_preserves_transaction_cap transfer status
    requested before memory access delegation new_account
    Haccess Hspent Hcap) as Hchild.
  cbn zeta in Hchild.
  set (child :=
    (MonadVM.Gas.call_gas_value transfer requested before memory
      (access + delegation +
        (if transfer then MonadVM.Gas.call_value else 0%N) +
        new_account)%N)
    .(MonadVM.Gas.call_gas.callee_available_gas)) in *.
  assert (HchildBound : (Z.of_N child <= 30_000_000)%Z)
    by exact Hchild.
  assert (Hsmall : (Z.of_N child < 2 ^ 63)%Z).
  { eapply Z.le_lt_trans.
    - exact HchildBound.
    - vm_compute. reflexivity. }
  pose proof (@u256_forwarded_gas_small_identity U256 U64 child Hsmall)
    as Hraw.
  change (0 <= MonadVM.Numeric.U256.to_uint64
    (_rocq_assumption_0 := U64)
    (MonadVM.Numeric.U256.of_uint_exn
      (_rocq_assumption_0 := U256) child) <= 30_000_000)%Z.
  rewrite Hraw.
  lia.
Qed.

Lemma create_message_signed_gas_range
    (before memory initcode : N) :
  let charge := (memory + MonadVM.Gas.create_cost + initcode)%N in
  let forwarded := MonadVM.Gas.minus_1_64th (before - charge)%N in
  let raw := MonadVM.Support.UintN.to_int64
    (_rocq_assumption_0 := U64) forwarded in
  (charge <= before)%N ->
  (Z.of_N before <= 30_000_000)%Z ->
  (0 <= raw <= 30_000_000)%Z.
Proof.
  cbn zeta.
  intros Hcharge Hcap.
  pose proof (create_child_gas_preserves_transaction_cap
    before memory initcode Hcharge Hcap) as Hchild.
  cbn zeta in Hchild.
  assert (Hsmall :
    (Z.of_N (MonadVM.Gas.minus_1_64th
      (before - (memory + MonadVM.Gas.create_cost + initcode)%N)%N)
      < 2 ^ 63)%Z) by lia.
  rewrite (@uintn_to_int64_small_identity U64 _ Hsmall).
  lia.
Qed.
End ChildMessageInitialGas.

Section ChildMachineEntries.
Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
Context `{U :
  RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}.
Context `{U256 :
  RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
Context `{U64 : RocqOfOCaml.Basics.Unreachable int64}.
Context `{I :
  RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.Integer.t}.
Context `{V : RocqOfOCaml.Basics.Unreachable unit}.

Lemma call_child_initial_machine_gas_preserves_transaction_cap
    (host : Host_t) (memory_capacity : MonadVM.Support.UintN.t)
    (transfer : bool)
    (status : MonadVM.Support.Variants.AccessStatus.t)
    (requested before memory access delegation new_account : N) :
  let transfer_cost := if transfer then MonadVM.Gas.call_value else 0%N in
  let extra := (access + delegation + transfer_cost + new_account)%N in
  let quote :=
    MonadVM.Gas.call_gas_value transfer requested before memory extra in
  let raw := MonadVM.Numeric.U256.to_uint64
    (_rocq_assumption_0 := U64)
    (MonadVM.Numeric.U256.of_uint_exn
      (_rocq_assumption_0 := U256)
      quote.(MonadVM.Gas.call_gas.callee_available_gas)) in
  let state := MonadVM.Vm.Make.MachineState.initial host
    (MonadVM.Gas.of_uint64 raw) memory_capacity in
  (MonadVM.Gas.account_access_cost status <= access)%N ->
  (quote.(MonadVM.Gas.call_gas.caller_spent_gas) + memory <= before)%N ->
  (Z.of_N before <= 30_000_000)%Z ->
  (Z.of_N state.(MonadVM.Vm.Make.MachineState.t.gas) <= 30_000_000)%Z.
Proof.
  cbn zeta.
  intros Haccess Hspent Hcap.
  change (Z.of_N (MonadVM.Gas.of_uint64
    (MonadVM.Numeric.U256.to_uint64
      (_rocq_assumption_0 := U64)
      (MonadVM.Numeric.U256.of_uint_exn
        (_rocq_assumption_0 := U256)
        (MonadVM.Gas.call_gas_value transfer requested before memory
          (access + delegation +
            (if transfer then MonadVM.Gas.call_value else 0%N) +
            new_account)%N)
        .(MonadVM.Gas.call_gas.callee_available_gas))))
    <= 30_000_000)%Z.
  exact (@call_message_initial_gas_preserves_transaction_cap
    U256 U64 U transfer status requested before memory access
    delegation new_account Haccess Hspent Hcap).
Qed.

Lemma create_child_initial_machine_gas_preserves_transaction_cap
    (host : Host_t) (memory_capacity : MonadVM.Support.UintN.t)
    (before memory initcode : N) :
  let charge := (memory + MonadVM.Gas.create_cost + initcode)%N in
  let raw := MonadVM.Support.UintN.to_int64
    (_rocq_assumption_0 := U64)
    (MonadVM.Gas.minus_1_64th (before - charge)%N) in
  let state := MonadVM.Vm.Make.MachineState.initial host
    (MonadVM.Gas.of_uint64 raw) memory_capacity in
  (charge <= before)%N ->
  (Z.of_N before <= 30_000_000)%Z ->
  (Z.of_N state.(MonadVM.Vm.Make.MachineState.t.gas) <= 30_000_000)%Z.
Proof.
  cbn zeta.
  intros Hcharge Hcap.
  change (Z.of_N (MonadVM.Gas.of_uint64
    (MonadVM.Support.UintN.to_int64
      (_rocq_assumption_0 := U64)
      (MonadVM.Gas.minus_1_64th
        (before - (memory + MonadVM.Gas.create_cost + initcode)%N)%N)))
    <= 30_000_000)%Z.
  exact (@create_message_initial_gas_preserves_transaction_cap
    U64 U before memory initcode Hcharge Hcap).
Qed.
End ChildMachineEntries.
