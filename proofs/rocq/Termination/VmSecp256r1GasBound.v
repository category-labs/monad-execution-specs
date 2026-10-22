(** The generated P-256 verification precompile cannot return more gas. *)

From Stdlib Require Import ZArith.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import MonadExecutionSpecs.Termination.VmUnsignedGas.
Require Import MonadExecutionSpecs.Termination.VmPrecompileGasInvariant.
Require MonadVM.Precompiles.Secp256r1.
Require MonadVM.Precompiles.Utils.
Require MonadVM.Evmc.
Require MonadVM.Gas.
Require MonadVM.Uint64.
Require MonadVM.Numeric.
Require MonadVM.Support.UintN.
Require MonadVM.Chain.Ethereum.
Require MonadVM.Ec.Secp256r1.
Require MonadVM.Ec.Algebra.
Require MonadVM.Ec.Curve.

Local Open Scope Z_scope.

Section Secp256r1.
Context `{UZ : RocqOfOCaml.Basics.Unreachable Z.t}.
Context `{U64 : RocqOfOCaml.Basics.Unreachable MonadVM.Uint64.t}.
Context `{UCount : RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}.
Context `{UU256Repr : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.Repr.t}.
Context `{UU256 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
Context `{UInteger : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.Integer.t}.
Context `{UGas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
Context `{UAddress : RocqOfOCaml.Basics.Unreachable MonadVM.Chain.Ethereum.Address.t}.
Context `{UUnit : RocqOfOCaml.Basics.Unreachable unit}.
Context `{UString : RocqOfOCaml.Basics.Unreachable string}.
Context `{UInt : RocqOfOCaml.Basics.Unreachable int}.
Context `{UAscii : RocqOfOCaml.Basics.Unreachable ascii}.
Context `{UPair : RocqOfOCaml.Basics.Unreachable (int * int)}.
Context `{UIntegerBase : RocqOfOCaml.Basics.Unreachable
  MonadVM.Numeric.IntegerBase.(MonadVM.Numeric.Make.Make_result.t)}.
Context `{UFp : RocqOfOCaml.Basics.Unreachable
  (MonadVM.Ec.Secp256r1.F_p
    (_rocq_module_assumption_0 := UZ)
    (_rocq_module_assumption_1 := UCount)
    (_rocq_module_assumption_2 := UIntegerBase)).(MonadVM.Ec.Algebra.Prime_field.Prime_field_result.t)}.
Context `{UC1 : RocqOfOCaml.Basics.Unreachable
  (MonadVM.Ec.Secp256r1.C_1
    (_rocq_module_assumption_0 := UZ)
    (_rocq_module_assumption_1 := UCount)
    (_rocq_module_assumption_2 := UInteger)
    (_rocq_module_assumption_3 := UIntegerBase)
    (_rocq_module_assumption_4 := UFp)).(MonadVM.Ec.Curve.Make.Make_result.t)}.
Context `{UG1 : RocqOfOCaml.Basics.Unreachable
  (MonadVM.Ec.Secp256r1.G_1
    (_rocq_module_assumption_0 := UZ)
    (_rocq_module_assumption_1 := UCount)
    (_rocq_module_assumption_2 := UInteger)
    (_rocq_module_assumption_3 := UIntegerBase)
    (_rocq_module_assumption_4 := UFp)
    (_rocq_module_assumption_5 := UC1)).(MonadVM.Ec.Curve.Make.Subgroup.Subgroup_result.curve)}.
Context `{UFq : RocqOfOCaml.Basics.Unreachable
  (MonadVM.Ec.Secp256r1.F_q
    (_rocq_module_assumption_0 := UZ)
    (_rocq_module_assumption_1 := UCount)
    (_rocq_module_assumption_2 := UIntegerBase)).(MonadVM.Ec.Algebra.Prime_field.Prime_field_result.t)}.

Local Ltac gas_safe :=
  cbn zeta;
  lazymatch goal with
  | |- precompile_gas_safe
      (MonadVM.Precompiles.Utils.Precompile.op_letdollar _ _) =>
      eapply precompile_bind_gas_safe;
        [gas_safe | intro; gas_safe]
  | |- precompile_gas_safe
      (MonadVM.Precompiles.Utils.Precompile.op_ltdollargt _ _) =>
      apply precompile_fmap_gas_safe; gas_safe
  | |- precompile_gas_safe
      (MonadVM.Precompiles.Utils.Precompile.u256) =>
      unfold MonadVM.Precompiles.Utils.Precompile.u256;
        apply precompile_numeric_reader_gas_safe
  | |- precompile_gas_safe
      (MonadVM.Precompiles.Utils.Precompile.spend_gas _) =>
      apply precompile_spend_gas_safe
  | |- precompile_gas_safe
      (MonadVM.Precompiles.Utils.Precompile._return _) =>
      apply precompile_return_gas_safe
  | |- precompile_gas_safe ?other =>
      fail 1 "unhandled P-256 precompile step" other
  end.

Lemma generated_secp256r1_precompile_gas_bounded
    (msg : MonadVM.Evmc.Message.t) :
  valid_int64_repr msg.(MonadVM.Evmc.Message.t.gas) ->
  (RocqOfOCaml.OCamlZ.of_int64_unsigned
    (@MonadVM.Precompiles.Secp256r1.verify
      UZ U64 UCount UU256Repr UU256 UInteger UGas UAddress
      UUnit UString UInt UAscii UPair UIntegerBase UFp UC1 UG1 UFq
      msg).(MonadVM.Evmc.Result.t.gas_left)
    <= RocqOfOCaml.OCamlZ.of_int64_unsigned
      msg.(MonadVM.Evmc.Message.t.gas))%Z.
Proof.
  intro Hvalid.
  unfold MonadVM.Precompiles.Secp256r1.verify.
  eapply (@precompile_run_gas_safe_bounded UAddress UUnit UInt).
  - exact Hvalid.
  - gas_safe.
Qed.
End Secp256r1.
