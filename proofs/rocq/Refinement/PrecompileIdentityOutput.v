From Stdlib Require Import ZArith NArith Lia.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import MonadVM.Precompiles.
Require Import MonadVM.Precompiles.Utils.
Require Import MonadVM.Evmc.
Open Scope Z_scope.

Section IdentityOutput.
Context `{U64 : RocqOfOCaml.Basics.Unreachable MonadVM.Uint64.t}.
Context `{UGas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
Context `{UAddress :
  RocqOfOCaml.Basics.Unreachable MonadVM.Chain.Ethereum.Address.t}.
Context `{UUnit : RocqOfOCaml.Basics.Unreachable unit}.
Context `{UInt : RocqOfOCaml.Basics.Unreachable int}.

Lemma spend_then_return_success_output
    (msg : MonadVM.Evmc.Message.t) (charge : MonadVM.Gas.t)
    (output : MonadVM.Byte_string.Bytes.t) :
  let result :=
    MonadVM.Precompiles.Utils.Precompile.run msg
      (MonadVM.Precompiles.Utils.Precompile.op_letdollar
        (MonadVM.Precompiles.Utils.Precompile.spend_gas
          (_rocq_assumption_0 := U64) (_rocq_assumption_1 := UGas) charge)
        (fun _ : unit =>
          MonadVM.Precompiles.Utils.Precompile._return output)) in
  result.(MonadVM.Evmc.Result.t.status_code) =
    MonadVM.Evmc.Result.StatusCode.Success ->
  result.(MonadVM.Evmc.Result.t.output_data) = output.
Proof.
  cbn zeta.
  unfold MonadVM.Precompiles.Utils.Precompile.run,
    MonadVM.Precompiles.Utils.Precompile.op_letdollar,
    MonadVM.Precompiles.Utils.Precompile.spend_gas,
    MonadVM.Precompiles.Utils.Precompile._return.
  cbn.
  destruct (MonadVM.Gas.op_lt
    (MonadVM.Gas.of_uint64 msg.(MonadVM.Evmc.Message.t.gas)) charge)
    eqn:Hout; cbn.
  - discriminate.
  - intros _; reflexivity.
Qed.

Lemma spend_then_return_outcome
    (msg : MonadVM.Evmc.Message.t) (charge : MonadVM.Gas.t)
    (output : MonadVM.Byte_string.Bytes.t) :
  let result :=
    MonadVM.Precompiles.Utils.Precompile.run msg
      (MonadVM.Precompiles.Utils.Precompile.op_letdollar
        (MonadVM.Precompiles.Utils.Precompile.spend_gas
          (_rocq_assumption_0 := U64) (_rocq_assumption_1 := UGas) charge)
        (fun _ : unit =>
          MonadVM.Precompiles.Utils.Precompile._return output)) in
  if MonadVM.Gas.op_lt
       (MonadVM.Gas.of_uint64 msg.(MonadVM.Evmc.Message.t.gas)) charge
  then
    result.(MonadVM.Evmc.Result.t.status_code) =
      MonadVM.Evmc.Result.StatusCode.Out_of_gas /\
    result.(MonadVM.Evmc.Result.t.output_data) =
      MonadVM.Byte_string.Bytes.empty
  else
    result.(MonadVM.Evmc.Result.t.status_code) =
      MonadVM.Evmc.Result.StatusCode.Success /\
    result.(MonadVM.Evmc.Result.t.output_data) = output.
Proof.
  cbn zeta.
  unfold MonadVM.Precompiles.Utils.Precompile.run,
    MonadVM.Precompiles.Utils.Precompile.op_letdollar,
    MonadVM.Precompiles.Utils.Precompile.spend_gas,
    MonadVM.Precompiles.Utils.Precompile._return.
  cbn.
  destruct (MonadVM.Gas.op_lt
    (MonadVM.Gas.of_uint64 msg.(MonadVM.Evmc.Message.t.gas)) charge);
    cbn; split; reflexivity.
Qed.

Definition identity_charge (msg : MonadVM.Evmc.Message.t) : MonadVM.Gas.t :=
  MonadVM.Gas.op_plus
    (MonadVM.Gas.op_tildedollar (_rocq_assumption_0 := UGas) 15)
    (MonadVM.Gas.op_star
      (MonadVM.Gas.op_tildedollar (_rocq_assumption_0 := UGas) 3)
      (MonadVM.Gas.bytes_to_whole_words
        (MonadVM.Gas.op_tildedollar (_rocq_assumption_0 := UGas)
          (MonadVM.Byte_string.Bytes.length
            msg.(MonadVM.Evmc.Message.t.input_data))))).

Lemma identity_charge_exact (msg : MonadVM.Evmc.Message.t) :
  identity_charge msg =
    (15 + 3 *
      ((N.of_nat
          (Strings.String.length
            msg.(MonadVM.Evmc.Message.t.input_data)) + 31) / 32))%N.
Proof.
  unfold identity_charge, MonadVM.Gas.op_plus,
    MonadVM.Gas.op_star, MonadVM.Gas.bytes_to_whole_words,
    MonadVM.Gas.op_tildedollar,
    MonadVM.Support.UintN.op_tildedollar,
    MonadVM.Support.UintN.of_int,
    MonadVM.Support.UintN.of_z_exn,
    MonadVM.Support.UintN.of_z_opt,
    MonadVM.Support.UintN.in_range,
    MonadVM.Support.UintN.op_plus,
    MonadVM.Support.UintN.op_star,
    MonadVM.Support.UintN.bytes_to_whole_words,
    MonadVM.Byte_string.Bytes.length,
    MonadVM.String.length,
    RocqOfOCaml.OCamlString.length.
  assert (Hnonnegative :
    Z.leb 0
      (Z.of_nat
        (Strings.String.length msg.(MonadVM.Evmc.Message.t.input_data))) =
      true) by (apply Z.leb_le; lia).
  rewrite Hnonnegative.
  cbn [Z.leb Z.to_N].
  rewrite <- Z_nat_N.
  rewrite Nat2Z.id.
  reflexivity.
Qed.

Lemma identity_exact_outcome (msg : MonadVM.Evmc.Message.t) :
  let result := @MonadVM.Precompiles.identity
    U64 UGas UAddress UUnit UInt msg in
  if MonadVM.Gas.op_lt
       (MonadVM.Gas.of_uint64 msg.(MonadVM.Evmc.Message.t.gas))
       (identity_charge msg)
  then
    result.(MonadVM.Evmc.Result.t.status_code) =
      MonadVM.Evmc.Result.StatusCode.Out_of_gas /\
    result.(MonadVM.Evmc.Result.t.output_data) =
      MonadVM.Byte_string.Bytes.empty
  else
    result.(MonadVM.Evmc.Result.t.status_code) =
      MonadVM.Evmc.Result.StatusCode.Success /\
    result.(MonadVM.Evmc.Result.t.output_data) =
      msg.(MonadVM.Evmc.Message.t.input_data).
Proof.
  unfold identity_charge, MonadVM.Precompiles.identity.
  cbn zeta.
  apply spend_then_return_outcome.
Qed.

Lemma identity_success_returns_input (msg : MonadVM.Evmc.Message.t) :
  (@MonadVM.Precompiles.identity
    U64 UGas UAddress UUnit UInt msg).(MonadVM.Evmc.Result.t.status_code) =
    MonadVM.Evmc.Result.StatusCode.Success ->
  (@MonadVM.Precompiles.identity
    U64 UGas UAddress UUnit UInt msg).(MonadVM.Evmc.Result.t.output_data) =
    msg.(MonadVM.Evmc.Message.t.input_data).
Proof.
  unfold MonadVM.Precompiles.identity.
  cbn zeta.
  apply spend_then_return_success_output.
Qed.
End IdentityOutput.

Print Assumptions spend_then_return_success_output.
Print Assumptions spend_then_return_outcome.
Print Assumptions identity_charge_exact.
Print Assumptions identity_exact_outcome.
Print Assumptions identity_success_returns_input.
