(** The generated BLAKE2F precompile does not increase returned gas. *)

From Stdlib Require Import ZArith.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import MonadExecutionSpecs.Termination.VmUnsignedGas.
Require Import MonadExecutionSpecs.Termination.VmPrecompileGasInvariant.
Require MonadVM.Precompiles.
Require MonadVM.Evmc.
Require MonadVM.Gas.
Require MonadVM.Uint64.
Require MonadVM.Numeric.
Require MonadVM.Support.UintN.
Require MonadVM.Chain.Ethereum.

Local Open Scope Z_scope.

Section Blake2f.
Context `{U64 : RocqOfOCaml.Basics.Unreachable MonadVM.Uint64.t}.
Context `{UCount : RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}.
Context `{UU64Repr : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U64.Repr.t}.
Context `{UU64 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U64.t}.
Context `{UU32Repr : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U32.Repr.t}.
Context `{UU32 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U32.t}.
Context `{UGas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
Context `{UAddress : RocqOfOCaml.Basics.Unreachable MonadVM.Chain.Ethereum.Address.t}.
Context `{UUnit : RocqOfOCaml.Basics.Unreachable unit}.
Context `{UString : RocqOfOCaml.Basics.Unreachable string}.
Context `{UInt : RocqOfOCaml.Basics.Unreachable int}.
Context `{UAscii : RocqOfOCaml.Basics.Unreachable ascii}.
Context `{UPair : RocqOfOCaml.Basics.Unreachable (int * int)}.
Context `{UInt64 : RocqOfOCaml.Basics.Unreachable int64}.

Lemma blake2f_flag_gas_safe (flag : ascii) :
  precompile_gas_safe
    (match flag with
     | "000"%char => MonadVM.Precompiles.Utils.Precompile._return false
     | "001"%char => MonadVM.Precompiles.Utils.Precompile._return true
     | _ => MonadVM.Precompiles.Utils.Precompile.precompile_failure
     end).
Proof.
  destruct flag as [b0 b1 b2 b3 b4 b5 b6 b7].
  destruct b0; destruct b1; destruct b2; destruct b3;
    destruct b4; destruct b5; destruct b6; destruct b7;
    cbn; first
      [apply precompile_return_gas_safe
      |apply precompile_fail_gas_safe].
Qed.

Local Ltac gas_safe :=
  cbn zeta;
  lazymatch goal with
  | |- precompile_gas_safe
      (MonadVM.Precompiles.Utils.Precompile.op_letdollar _ _) =>
      eapply precompile_bind_gas_safe;
        [gas_safe | intro; gas_safe]
  | |- precompile_gas_safe
      (MonadVM.Precompiles.Utils.Precompile.op_gtgteq ?first ?next) =>
      change (precompile_gas_safe
        (MonadVM.Precompiles.Utils.Precompile.op_letdollar
          first next));
      gas_safe
  | |- precompile_gas_safe
      (MonadVM.Precompiles.Utils.Precompile.op_ltdollargt _ _) =>
      apply precompile_fmap_gas_safe; gas_safe
  | |- precompile_gas_safe
      (MonadVM.Precompiles.Utils.Precompile.list_value _ _) =>
      apply precompile_list_value_gas_safe; gas_safe
  | |- precompile_gas_safe
      (MonadVM.Precompiles.Utils.Precompile.u32) =>
      unfold MonadVM.Precompiles.Utils.Precompile.u32; gas_safe
  | |- precompile_gas_safe
      (MonadVM.Precompiles.Utils.Precompile.u64_le) =>
      unfold MonadVM.Precompiles.Utils.Precompile.u64_le; gas_safe
  | |- precompile_gas_safe
      (MonadVM.Precompiles.Utils.Precompile.uint64_le) =>
      unfold MonadVM.Precompiles.Utils.Precompile.uint64_le;
        gas_safe
  | |- precompile_gas_safe
      (MonadVM.Precompiles.Utils.Precompile.numeric_reader _) =>
      apply precompile_numeric_reader_gas_safe
  | |- precompile_gas_safe
      (MonadVM.Precompiles.Utils.Precompile.numeric_reader_le _) =>
      apply precompile_numeric_reader_le_gas_safe
  | |- precompile_gas_safe
      (MonadVM.Precompiles.Utils.Precompile.byte) =>
      apply precompile_byte_gas_safe
  | |- precompile_gas_safe
      (MonadVM.Precompiles.Utils.Precompile.spend_gas _) =>
      apply precompile_spend_gas_safe
  | |- precompile_gas_safe
      (MonadVM.Precompiles.Utils.Precompile.ensure _) =>
      apply precompile_ensure_gas_safe
  | |- precompile_gas_safe
      (MonadVM.Precompiles.Utils.Precompile.Option.or_fail _) =>
      apply precompile_option_or_fail_gas_safe
  | |- precompile_gas_safe
      (MonadVM.Precompiles.Utils.Precompile._return _) =>
      apply precompile_return_gas_safe
  | |- precompile_gas_safe
      (MonadVM.Precompiles.Utils.Precompile.precompile_failure) =>
      apply precompile_fail_gas_safe
  | |- precompile_gas_safe ?other =>
      first
        [apply blake2f_flag_gas_safe
        |fail 1 "unhandled precompile step" other]
  end.

Lemma generated_blake2f_precompile_gas_bounded
    (msg : MonadVM.Evmc.Message.t) :
  valid_int64_repr msg.(MonadVM.Evmc.Message.t.gas) ->
  (RocqOfOCaml.OCamlZ.of_int64_unsigned
    (@MonadVM.Precompiles.blake2f U64 UCount UU64Repr UU64
      UU32Repr UU32 UGas UAddress UUnit UString UInt UAscii
      UPair UInt64 msg).(MonadVM.Evmc.Result.t.gas_left)
    <= RocqOfOCaml.OCamlZ.of_int64_unsigned
      msg.(MonadVM.Evmc.Message.t.gas))%Z.
Proof.
  intro Hvalid.
  unfold MonadVM.Precompiles.blake2f.
  eapply (@precompile_run_gas_safe_bounded UAddress UUnit UInt).
  - exact Hvalid.
  - gas_safe.
Qed.
End Blake2f.
