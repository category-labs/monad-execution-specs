(** A host-return gas contract at the generated VM boundary. *)

From Stdlib Require Import ZArith NArith Bool Lia.
Require Import RocqOfOCaml.RocqOfOCaml.
Require RocqOfOCaml.OCamlInt64.
Require MonadVM.Evmc.
Require MonadVM.Gas.
Require MonadVM.Int64.
Require MonadVM.Support.Variants.
Require MonadVM.Vm.
Require Import MonadExecutionSpecs.Termination.VmCallGas.
Require Import MonadExecutionSpecs.Termination.VmOpcodeProgress.

Local Open Scope N_scope.

Definition signed_int64_range (raw : Z) : Prop :=
  (-2 ^ 63 <= raw < 2 ^ 63)%Z.

Lemma int64_below_min_match_false (raw : Z) :
  (match MonadVM.Int64.compare raw MonadVM.Int64.min_int with
   | Z.neg xH => true
   | _ => false
   end) = false ->
  (-2 ^ 63 <= raw)%Z.
Proof.
  intro Hvalid.
  change ((match RocqOfOCaml.OCamlInt64.compare raw
    RocqOfOCaml.OCamlInt64.min_int with
    | Z.neg xH => true | _ => false end) = false) in Hvalid.
  unfold RocqOfOCaml.OCamlInt64.compare,
    RocqOfOCaml.OCamlInt64.min_int,
    RocqOfOCaml.OCamlInt64.sign_bit in Hvalid.
  destruct (Z.compare_spec raw (-2 ^ 63)); cbn in Hvalid; lia.
Qed.

Lemma int64_above_max_match_false (raw : Z) :
  (match MonadVM.Int64.compare raw MonadVM.Int64.max_int with
   | Z.pos xH => true
   | _ => false
   end) = false ->
  (raw < 2 ^ 63)%Z.
Proof.
  intro Hvalid.
  change ((match RocqOfOCaml.OCamlInt64.compare raw
    RocqOfOCaml.OCamlInt64.max_int with
    | Z.pos xH => true | _ => false end) = false) in Hvalid.
  unfold RocqOfOCaml.OCamlInt64.compare,
    RocqOfOCaml.OCamlInt64.max_int,
    RocqOfOCaml.OCamlInt64.sign_bit in Hvalid.
  destruct (Z.compare_spec raw (2 ^ 63 - 1)); cbn in Hvalid; lia.
Qed.

Lemma int64_range_checks_false (returned message : Z) :
  signed_int64_range returned ->
  signed_int64_range message ->
  (match MonadVM.Int64.compare message MonadVM.Int64.min_int with
   | Z.neg xH => true | _ => false end) = false /\
  (match MonadVM.Int64.compare message MonadVM.Int64.max_int with
   | Z.pos xH => true | _ => false end) = false /\
  (match MonadVM.Int64.compare returned MonadVM.Int64.max_int with
   | Z.pos xH => true | _ => false end) = false.
Proof.
  unfold signed_int64_range.
  intros Hreturned Hmessage.
  repeat split.
  - change ((match RocqOfOCaml.OCamlInt64.compare message
      RocqOfOCaml.OCamlInt64.min_int with
      | Z.neg xH => true | _ => false end) = false).
    unfold RocqOfOCaml.OCamlInt64.compare,
      RocqOfOCaml.OCamlInt64.min_int,
      RocqOfOCaml.OCamlInt64.sign_bit.
    destruct (Z.compare_spec message (-2 ^ 63)); cbn; lia.
  - change ((match RocqOfOCaml.OCamlInt64.compare message
      RocqOfOCaml.OCamlInt64.max_int with
      | Z.pos xH => true | _ => false end) = false).
    unfold RocqOfOCaml.OCamlInt64.compare,
      RocqOfOCaml.OCamlInt64.max_int,
      RocqOfOCaml.OCamlInt64.sign_bit.
    destruct (Z.compare_spec message (2 ^ 63 - 1)); cbn; lia.
  - change ((match RocqOfOCaml.OCamlInt64.compare returned
      RocqOfOCaml.OCamlInt64.max_int with
      | Z.pos xH => true | _ => false end) = false).
    unfold RocqOfOCaml.OCamlInt64.compare,
      RocqOfOCaml.OCamlInt64.max_int,
      RocqOfOCaml.OCamlInt64.sign_bit.
    destruct (Z.compare_spec returned (2 ^ 63 - 1)); cbn; lia.
Qed.

Lemma int64_unsigned_matches_z (raw : Z) :
  signed_int64_range raw ->
  RocqOfOCaml.OCamlInt64.unsigned raw =
    RocqOfOCaml.OCamlZ.of_int64_unsigned raw.
Proof.
  unfold signed_int64_range,
    RocqOfOCaml.OCamlInt64.unsigned,
    RocqOfOCaml.OCamlInt64.modulus,
    RocqOfOCaml.OCamlZ.of_int64_unsigned.
  intro Hrange.
  destruct (Z.ltb raw 0) eqn:Hnegative.
  - apply Z.ltb_lt in Hnegative.
    rewrite <- (Z.mod_add raw 1 (2 ^ 64)) by lia.
    replace (raw + 1 * 2 ^ 64)%Z with (raw + 2 ^ 64)%Z by lia.
    rewrite Z.mod_small by lia.
    reflexivity.
  - apply Z.ltb_ge in Hnegative.
    rewrite Z.mod_small by lia.
    reflexivity.
Qed.

Lemma signed_int64_unsigned_compare_bound (returned message : Z) :
  signed_int64_range returned ->
  signed_int64_range message ->
  (0 <= returned)%Z ->
  (RocqOfOCaml.OCamlInt64.unsigned_compare returned message <= 0)%Z ->
  (returned <= RocqOfOCaml.OCamlZ.of_int64_unsigned message)%Z.
Proof.
  intros Hreturned Hmessage Hnonnegative Hcompare.
  unfold RocqOfOCaml.OCamlInt64.unsigned_compare,
    RocqOfOCaml.OCamlInt64.compare in Hcompare.
  pose proof (int64_unsigned_matches_z returned Hreturned) as Hleft.
  pose proof (int64_unsigned_matches_z message Hmessage) as Hright.
  unfold RocqOfOCaml.OCamlZ.of_int64_unsigned in Hleft.
  assert (Hnotnegative : (returned <? 0)%Z = false)
    by (apply Z.ltb_ge; lia).
  rewrite Hnotnegative in Hleft.
  destruct (Z.compare_spec
    (RocqOfOCaml.OCamlInt64.unsigned returned)
    (RocqOfOCaml.OCamlInt64.unsigned message));
    rewrite Hleft, Hright in *; lia.
Qed.

Lemma int64_negative_match_false_nonnegative (raw : Z) :
  (match MonadVM.Int64.compare raw MonadVM.Int64.zero with
   | Z.neg xH => true
   | _ => false
   end) = false ->
  (0 <= raw)%Z.
Proof.
  intro Hnotnegative.
  change ((match RocqOfOCaml.OCamlInt64.compare raw 0%Z with
    | Z.neg xH => true | _ => false end) = false) in Hnotnegative.
  unfold RocqOfOCaml.OCamlInt64.compare in Hnotnegative.
  destruct (Z.compare_spec raw 0); cbn in Hnotnegative; lia.
Qed.

Lemma int64_excess_match_false_bounded (returned message : Z) :
  (match MonadVM.Int64.unsigned_compare returned message with
   | Z.pos xH => true
   | _ => false
   end) = false ->
  (RocqOfOCaml.OCamlInt64.unsigned_compare returned message <= 0)%Z.
Proof.
  intro Hnotexcess.
  change ((match RocqOfOCaml.OCamlInt64.unsigned_compare
    returned message with
    | Z.pos xH => true | _ => false end) = false) in Hnotexcess.
  unfold RocqOfOCaml.OCamlInt64.unsigned_compare,
    RocqOfOCaml.OCamlInt64.compare in *.
  destruct (Z.compare_spec
    (RocqOfOCaml.OCamlInt64.unsigned returned)
    (RocqOfOCaml.OCamlInt64.unsigned message));
    cbn in Hnotexcess; lia.
Qed.

Definition invalid_host_gas (returned message : Z) : bool :=
  orb
    (match MonadVM.Int64.compare message MonadVM.Int64.min_int with
     | Z.neg xH => true | _ => false end)
    (orb
      (match MonadVM.Int64.compare message MonadVM.Int64.max_int with
       | Z.pos xH => true | _ => false end)
      (orb
        (match MonadVM.Int64.compare returned MonadVM.Int64.max_int with
         | Z.pos xH => true | _ => false end)
        (orb
          (match MonadVM.Int64.compare returned MonadVM.Int64.zero with
           | Z.neg xH => true | _ => false end)
          (match MonadVM.Int64.unsigned_compare returned message with
           | Z.pos xH => true | _ => false end)))).

Lemma checked_host_gas_bound (returned message : Z) :
  invalid_host_gas returned message = false ->
  (0 <= returned <=
    RocqOfOCaml.OCamlZ.of_int64_unsigned message)%Z.
Proof.
  intro Hvalid.
  unfold invalid_host_gas in Hvalid.
  apply orb_false_iff in Hvalid as [Hmessage_min Htail].
  apply orb_false_iff in Htail as [Hmessage_max Htail].
  apply orb_false_iff in Htail as [Hreturned_max Htail].
  apply orb_false_iff in Htail as [Hnonnegative Hbounded].
  pose proof (int64_negative_match_false_nonnegative
    returned Hnonnegative) as Hzero.
  pose proof (int64_below_min_match_false message Hmessage_min)
    as Hmessage_lower.
  pose proof (int64_above_max_match_false message Hmessage_max)
    as Hmessage_upper.
  pose proof (int64_above_max_match_false returned Hreturned_max)
    as Hreturned_upper.
  assert (Hmessage : signed_int64_range message)
    by (unfold signed_int64_range; lia).
  assert (Hreturned : signed_int64_range returned)
    by (unfold signed_int64_range; lia).
  split; [exact Hzero |].
  eapply signed_int64_unsigned_compare_bound; eauto.
  eapply int64_excess_match_false_bounded; exact Hbounded.
Qed.

Section HostCallGasBound.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.

  Let State := @MonadVM.Vm.Make.MachineState.t Host_t F.
  Let host_call :=
    (@MonadVM.Vm.Make.Host Host_t F).(MonadVM.Evmc.HOST.call).

  Definition host_call_gas_bounded : Prop :=
    forall (msg : MonadVM.Evmc.Message.t) (host : Host_t),
      let result := fst (host_call msg host) in
      (0 <= result.(MonadVM.Evmc.Result.t.gas_left) <=
        RocqOfOCaml.OCamlZ.of_int64_unsigned
          msg.(MonadVM.Evmc.Message.t.gas))%Z.

  Lemma lift_call_gas_bounded
      (Hhost : host_call_gas_bounded)
      (msg : MonadVM.Evmc.Message.t)
      (state next : State) (result : MonadVM.Evmc.Result.t) :
    @MonadVM.Vm.Make.M.HostAPI.lift Host_t F MonadVM.Evmc.Result.t
      (host_call msg) state = (inl result, next) ->
    (0 <= result.(MonadVM.Evmc.Result.t.gas_left) <=
      RocqOfOCaml.OCamlZ.of_int64_unsigned
        msg.(MonadVM.Evmc.Message.t.gas))%Z.
  Proof.
    unfold MonadVM.Vm.Make.M.HostAPI.lift.
    destruct (host_call msg state.(MonadVM.Vm.Make.MachineState.t.host))
      as [actual_result actual_host] eqn:Hcall.
    cbn.
    intro Hsuccess.
    inversion Hsuccess; subst result.
    specialize (Hhost msg state.(MonadVM.Vm.Make.MachineState.t.host)).
    rewrite Hcall in Hhost.
    exact Hhost.
  Qed.

  Lemma host_api_call_gas_bounded
      (Hhost : host_call_gas_bounded)
      (msg : MonadVM.Evmc.Message.t)
      (state next : State) (result : MonadVM.Evmc.Result.t) :
    @MonadVM.Vm.Make.M.HostAPI.call Host_t F msg state =
      (inl result, next) ->
    (0 <= result.(MonadVM.Evmc.Result.t.gas_left) <=
      RocqOfOCaml.OCamlZ.of_int64_unsigned
        msg.(MonadVM.Evmc.Message.t.gas))%Z /\
    next.(MonadVM.Vm.Make.MachineState.t.gas) =
      state.(MonadVM.Vm.Make.MachineState.t.gas).
  Proof.
    intro Hsuccess.
    change (@MonadVM.Vm.Make.M.op_letdollar Host_t F
      MonadVM.Evmc.Result.t MonadVM.Evmc.Result.t
      (@MonadVM.Vm.Make.M.HostAPI.lift Host_t F MonadVM.Evmc.Result.t
        (host_call msg))
      (fun value =>
        if invalid_host_gas
          value.(MonadVM.Evmc.Result.t.gas_left)
          msg.(MonadVM.Evmc.Message.t.gas)
        then @MonadVM.Vm.Make.M.fail Host_t F
          MonadVM.Evmc.Result.t
          MonadVM.Evmc.Result.StatusCode.Internal_error
        else @MonadVM.Vm.Make.M._return Host_t F
          MonadVM.Evmc.Result.t value)
      state = (inl result, next))
      in Hsuccess.
    destruct (bind_success_decompose
      (@MonadVM.Vm.Make.M.HostAPI.lift Host_t F MonadVM.Evmc.Result.t
        (host_call msg))
      (fun value =>
        if invalid_host_gas
          value.(MonadVM.Evmc.Result.t.gas_left)
          msg.(MonadVM.Evmc.Message.t.gas)
        then @MonadVM.Vm.Make.M.fail Host_t F
          MonadVM.Evmc.Result.t
          MonadVM.Evmc.Result.StatusCode.Internal_error
        else @MonadVM.Vm.Make.M._return Host_t F
          MonadVM.Evmc.Result.t value)
      state result next Hsuccess)
      as [middle [intermediate [Hlift Hreturn]]].
    destruct (invalid_host_gas
      intermediate.(MonadVM.Evmc.Result.t.gas_left)
      msg.(MonadVM.Evmc.Message.t.gas)) eqn:Hvalid;
      cbn in Hreturn; try discriminate.
    cbn in Hreturn.
    inversion Hreturn; subst.
    split.
    - eapply lift_call_gas_bounded; eauto.
    - pose proof (host_lift_preserves_gas
        (host_call msg) state) as Hgas.
      rewrite Hlift in Hgas.
      cbn in Hgas.
      exact Hgas.
  Qed.

  Lemma host_api_call_checked_gas_bounded
      (msg : MonadVM.Evmc.Message.t)
      (state next : State) (result : MonadVM.Evmc.Result.t) :
    @MonadVM.Vm.Make.M.HostAPI.call Host_t F msg state =
      (inl result, next) ->
    (0 <= result.(MonadVM.Evmc.Result.t.gas_left) <=
      RocqOfOCaml.OCamlZ.of_int64_unsigned
        msg.(MonadVM.Evmc.Message.t.gas))%Z /\
    next.(MonadVM.Vm.Make.MachineState.t.gas) =
      state.(MonadVM.Vm.Make.MachineState.t.gas).
  Proof.
    intro Hsuccess.
    change (@MonadVM.Vm.Make.M.op_letdollar Host_t F
      MonadVM.Evmc.Result.t MonadVM.Evmc.Result.t
      (@MonadVM.Vm.Make.M.HostAPI.lift Host_t F MonadVM.Evmc.Result.t
        (host_call msg))
      (fun value =>
        if invalid_host_gas
          value.(MonadVM.Evmc.Result.t.gas_left)
          msg.(MonadVM.Evmc.Message.t.gas)
        then @MonadVM.Vm.Make.M.fail Host_t F
          MonadVM.Evmc.Result.t
          MonadVM.Evmc.Result.StatusCode.Internal_error
        else @MonadVM.Vm.Make.M._return Host_t F
          MonadVM.Evmc.Result.t value)
      state = (inl result, next))
      in Hsuccess.
    destruct (bind_success_decompose
      (@MonadVM.Vm.Make.M.HostAPI.lift Host_t F MonadVM.Evmc.Result.t
        (host_call msg))
      (fun value =>
        if invalid_host_gas
          value.(MonadVM.Evmc.Result.t.gas_left)
          msg.(MonadVM.Evmc.Message.t.gas)
        then @MonadVM.Vm.Make.M.fail Host_t F
          MonadVM.Evmc.Result.t
          MonadVM.Evmc.Result.StatusCode.Internal_error
        else @MonadVM.Vm.Make.M._return Host_t F
          MonadVM.Evmc.Result.t value)
      state result next Hsuccess)
      as [middle [intermediate [Hlift Hreturn]]].
    destruct (invalid_host_gas
      intermediate.(MonadVM.Evmc.Result.t.gas_left)
      msg.(MonadVM.Evmc.Message.t.gas)) eqn:Hvalid;
      cbn in Hreturn; try discriminate.
    inversion Hreturn; subst.
    split.
    - eapply checked_host_gas_bound; eauto.
    - pose proof (host_lift_preserves_gas
        (host_call msg) state) as Hgas.
      rewrite Hlift in Hgas.
      cbn in Hgas.
      exact Hgas.
  Qed.

  Lemma host_api_call_return_decreases_checked
      `{_rocq_assumption_0 :
        RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}
      (transfer : bool)
      (status : MonadVM.Support.Variants.AccessStatus.t)
      (requested before memory access delegation new_account : N)
      (msg : MonadVM.Evmc.Message.t)
      (state next : State) (result : MonadVM.Evmc.Result.t) :
    let transfer_cost := if transfer then MonadVM.Gas.call_value else 0 in
    let extra := access + delegation + transfer_cost + new_account in
    let quote :=
      MonadVM.Gas.call_gas_value transfer requested before memory extra in
    @MonadVM.Vm.Make.M.HostAPI.call Host_t F msg state =
      (inl result, next) ->
    RocqOfOCaml.OCamlZ.of_int64_unsigned
      msg.(MonadVM.Evmc.Message.t.gas) =
      Z.of_N quote.(MonadVM.Gas.call_gas.callee_available_gas) ->
    MonadVM.Gas.account_access_cost status <= access ->
    quote.(MonadVM.Gas.call_gas.caller_spent_gas) + memory <= before ->
    before - (quote.(MonadVM.Gas.call_gas.caller_spent_gas) + memory)
      + MonadVM.Gas.of_int64
        result.(MonadVM.Evmc.Result.t.gas_left) < before.
  Proof.
    cbn zeta.
    intros Hcall Hforwarded Haccess Hspent.
    pose proof (host_api_call_checked_gas_bounded msg state next result
      Hcall) as [[Hnonnegative Hbounded] _].
    rewrite Hforwarded in Hbounded.
    eapply call_host_result_decreases; eauto.
  Qed.

  Lemma host_api_call_return_decreases
      `{_rocq_assumption_0 :
        RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}
      (Hhost : host_call_gas_bounded)
      (transfer : bool)
      (status : MonadVM.Support.Variants.AccessStatus.t)
      (requested before memory access delegation new_account : N)
      (msg : MonadVM.Evmc.Message.t)
      (state next : State) (result : MonadVM.Evmc.Result.t) :
    let transfer_cost := if transfer then MonadVM.Gas.call_value else 0 in
    let extra := access + delegation + transfer_cost + new_account in
    let quote :=
      MonadVM.Gas.call_gas_value transfer requested before memory extra in
    @MonadVM.Vm.Make.M.HostAPI.call Host_t F msg state =
      (inl result, next) ->
    RocqOfOCaml.OCamlZ.of_int64_unsigned
      msg.(MonadVM.Evmc.Message.t.gas) =
      Z.of_N quote.(MonadVM.Gas.call_gas.callee_available_gas) ->
    MonadVM.Gas.account_access_cost status <= access ->
    quote.(MonadVM.Gas.call_gas.caller_spent_gas) + memory <= before ->
    before - (quote.(MonadVM.Gas.call_gas.caller_spent_gas) + memory)
      + MonadVM.Gas.of_int64
        result.(MonadVM.Evmc.Result.t.gas_left) < before.
  Proof.
    cbn zeta.
    intros Hcall Hforwarded Haccess Hspent.
    pose proof (host_api_call_gas_bounded Hhost msg state next result
      Hcall) as [[Hnonnegative Hbounded] _].
    rewrite Hforwarded in Hbounded.
    eapply call_host_result_decreases;
      eauto.
  Qed.
End HostCallGasBound.
