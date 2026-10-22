(** Gas decrease for the CALL-family return paths under the host gas bound.
    The proof uses the generated [Gas.call_gas_value] quote. It does not yet
    establish the bound for an arbitrary EVMC host or for every VM opcode. *)

From Stdlib Require Import NArith Lia.
Require Import RocqOfOCaml.RocqOfOCaml.
Require MonadVM.Gas.
Require MonadVM.Support.Variants.

Local Open Scope N_scope.

Section CallGas.
  Context `{_rocq_assumption_0 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.

  Lemma call_stipend_value : MonadVM.Gas.call_stipend = 2300.
  Proof. vm_compute. reflexivity. Qed.

  Lemma call_value_cost : MonadVM.Gas.call_value = 9000.
  Proof. vm_compute. reflexivity. Qed.

  Lemma account_access_min
      (status : MonadVM.Support.Variants.AccessStatus.t) :
    100 <= MonadVM.Gas.account_access_cost status.
  Proof. destruct status; vm_compute; discriminate. Qed.

  Lemma nonnegative_host_gas (raw : Z) :
    (0 <= raw)%Z ->
    MonadVM.Gas.of_int64 raw = Z.to_N raw.
  Proof.
    intro Hnonnegative.
    unfold MonadVM.Gas.of_int64, MonadVM.Support.UintN.of_int64,
      MonadVM.Support.UintN.of_z_exn,
      MonadVM.Support.UintN.of_z_opt,
      MonadVM.Support.UintN.in_range.
    apply Z.leb_le in Hnonnegative.
    rewrite Hnonnegative.
    reflexivity.
  Qed.

  Lemma call_gas_return_decreases
      (transfer : bool)
      (status : MonadVM.Support.Variants.AccessStatus.t)
      (requested before memory access delegation new_account returned : N) :
    let transfer_cost := if transfer then MonadVM.Gas.call_value else 0 in
    let extra := access + delegation + transfer_cost + new_account in
    let quote :=
      MonadVM.Gas.call_gas_value transfer requested before memory extra in
    MonadVM.Gas.account_access_cost status <= access ->
    quote.(MonadVM.Gas.call_gas.caller_spent_gas) + memory <= before ->
    returned <= quote.(MonadVM.Gas.call_gas.callee_available_gas) ->
    before - (quote.(MonadVM.Gas.call_gas.caller_spent_gas) + memory)
      + returned < before.
  Proof.
    cbn zeta.
    intros Haccess Hspent Hreturn.
    pose proof (account_access_min status) as Hmin.
    destruct transfer;
      unfold MonadVM.Gas.call_gas_value in *;
      cbn [MonadVM.Gas.call_gas.caller_spent_gas
           MonadVM.Gas.call_gas.callee_available_gas] in *;
      try rewrite call_value_cost in *;
      try rewrite call_stipend_value in *;
      unfold MonadVM.Support.UintN.op_plus in *;
      lia.
  Qed.

  Lemma call_not_made_decreases
      (transfer : bool)
      (status : MonadVM.Support.Variants.AccessStatus.t)
      (requested before memory access delegation new_account : N) :
    let transfer_cost := if transfer then MonadVM.Gas.call_value else 0 in
    let extra := access + delegation + transfer_cost + new_account in
    let quote :=
      MonadVM.Gas.call_gas_value transfer requested before memory extra in
    MonadVM.Gas.account_access_cost status <= access ->
    quote.(MonadVM.Gas.call_gas.caller_spent_gas) + memory <= before ->
    before - (quote.(MonadVM.Gas.call_gas.caller_spent_gas) + memory)
      + quote.(MonadVM.Gas.call_gas.callee_available_gas) < before.
  Proof.
    cbn zeta.
    intros Haccess Hspent.
    eapply call_gas_return_decreases; eauto using N.le_refl.
  Qed.

  Lemma call_child_gas_bounded_by_caller
      (transfer : bool)
      (status : MonadVM.Support.Variants.AccessStatus.t)
      (requested before memory access delegation new_account : N) :
    let transfer_cost := if transfer then MonadVM.Gas.call_value else 0 in
    let extra := access + delegation + transfer_cost + new_account in
    let quote :=
      MonadVM.Gas.call_gas_value transfer requested before memory extra in
    MonadVM.Gas.account_access_cost status <= access ->
    quote.(MonadVM.Gas.call_gas.caller_spent_gas) + memory <= before ->
    quote.(MonadVM.Gas.call_gas.callee_available_gas) <= before.
  Proof.
    cbn zeta.
    intros Haccess Hspent.
    pose proof (call_not_made_decreases transfer status requested before
      memory access delegation new_account Haccess Hspent) as Hstrict.
    cbn zeta in Hstrict.
    lia.
  Qed.

  Corollary call_child_gas_preserves_transaction_cap
      (transfer : bool)
      (status : MonadVM.Support.Variants.AccessStatus.t)
      (requested before memory access delegation new_account : N) :
    let transfer_cost := if transfer then MonadVM.Gas.call_value else 0 in
    let extra := access + delegation + transfer_cost + new_account in
    let quote :=
      MonadVM.Gas.call_gas_value transfer requested before memory extra in
    MonadVM.Gas.account_access_cost status <= access ->
    quote.(MonadVM.Gas.call_gas.caller_spent_gas) + memory <= before ->
    (Z.of_N before <= 30_000_000)%Z ->
    (Z.of_N quote.(MonadVM.Gas.call_gas.callee_available_gas)
      <= 30_000_000)%Z.
  Proof.
    cbn zeta.
    intros Haccess Hspent Hcap.
    pose proof (call_child_gas_bounded_by_caller transfer status requested
      before memory access delegation new_account Haccess Hspent) as Hchild.
    cbn zeta in Hchild.
    apply N2Z.inj_le in Hchild.
    lia.
  Qed.

  Lemma call_host_result_decreases
      (transfer : bool)
      (status : MonadVM.Support.Variants.AccessStatus.t)
      (requested before memory access delegation new_account : N)
      (raw_host_gas : Z) :
    let transfer_cost := if transfer then MonadVM.Gas.call_value else 0 in
    let extra := access + delegation + transfer_cost + new_account in
    let quote :=
      MonadVM.Gas.call_gas_value transfer requested before memory extra in
    MonadVM.Gas.account_access_cost status <= access ->
    quote.(MonadVM.Gas.call_gas.caller_spent_gas) + memory <= before ->
    (0 <= raw_host_gas)%Z ->
    (raw_host_gas <=
      Z.of_N quote.(MonadVM.Gas.call_gas.callee_available_gas))%Z ->
    before - (quote.(MonadVM.Gas.call_gas.caller_spent_gas) + memory)
      + MonadVM.Gas.of_int64 raw_host_gas < before.
  Proof.
    cbn zeta.
    intros Haccess Hspent Hnonnegative Hbounded.
    rewrite nonnegative_host_gas by exact Hnonnegative.
    eapply call_gas_return_decreases; eauto.
    lia.
  Qed.

  Lemma create_cost_value : MonadVM.Gas.create_cost = 32000.
  Proof. vm_compute. reflexivity. Qed.

  Lemma create_forwarded_le (available : N) :
    MonadVM.Gas.minus_1_64th available <= available.
  Proof.
    unfold MonadVM.Gas.minus_1_64th,
      MonadVM.Support.UintN.minus_1_64th.
    apply N.le_sub_l.
  Qed.

  Lemma create_child_gas_bounded_by_caller
      (before memory initcode : N) :
    let charge := memory + MonadVM.Gas.create_cost + initcode in
    let forwarded := MonadVM.Gas.minus_1_64th (before - charge) in
    charge <= before -> forwarded <= before.
  Proof.
    cbn zeta.
    intro Hcharge.
    pose proof (create_forwarded_le
      (before - (memory + MonadVM.Gas.create_cost + initcode)))
      as Hforwarded.
    lia.
  Qed.

  Corollary create_child_gas_preserves_transaction_cap
      (before memory initcode : N) :
    let charge := memory + MonadVM.Gas.create_cost + initcode in
    let forwarded := MonadVM.Gas.minus_1_64th (before - charge) in
    charge <= before ->
    (Z.of_N before <= 30_000_000)%Z ->
    (Z.of_N forwarded <= 30_000_000)%Z.
  Proof.
    cbn zeta.
    intros Hcharge Hcap.
    pose proof (create_child_gas_bounded_by_caller
      before memory initcode Hcharge) as Hchild.
    cbn zeta in Hchild.
    apply N2Z.inj_le in Hchild.
    lia.
  Qed.

  Lemma create_return_decreases
      (before memory initcode returned : N) :
    let charge := memory + MonadVM.Gas.create_cost + initcode in
    let available := before - charge in
    let forwarded := MonadVM.Gas.minus_1_64th available in
    charge <= before ->
    returned <= forwarded ->
    available - forwarded + returned < before.
  Proof.
    cbn zeta.
    intros Hcharge Hreturn.
    pose proof (create_forwarded_le
      (before - (memory + MonadVM.Gas.create_cost + initcode)))
      as Hforwarded.
    rewrite create_cost_value in *.
    lia.
  Qed.

  Lemma create_host_result_decreases
      (before memory initcode : N) (raw_host_gas : Z) :
    let charge := memory + MonadVM.Gas.create_cost + initcode in
    let available := before - charge in
    let forwarded := MonadVM.Gas.minus_1_64th available in
    charge <= before ->
    (0 <= raw_host_gas)%Z ->
    (raw_host_gas <= Z.of_N forwarded)%Z ->
    available - forwarded + MonadVM.Gas.of_int64 raw_host_gas < before.
  Proof.
    cbn zeta.
    intros Hcharge Hnonnegative Hbounded.
    rewrite nonnegative_host_gas by exact Hnonnegative.
    eapply create_return_decreases; eauto.
    lia.
  Qed.
End CallGas.
