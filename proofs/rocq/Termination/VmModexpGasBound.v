(** Modexp's generated parameter reader is gas-safe on Eight and Nine. *)

From Stdlib Require Import ZArith.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import MonadExecutionSpecs.Termination.VmUnsignedGas.
Require Import MonadExecutionSpecs.Termination.VmPrecompileGasInvariant.
Require MonadVM.Precompiles.Modexp.
Require MonadVM.Precompiles.Utils.
Require MonadVM.Numeric.
Require MonadVM.Support.UintN.
Require MonadVM.Support.Variants.
Require MonadVM.Chain.Monad.
Require MonadVM.Chain.Ethereum.
Require MonadVM.Byte_string.
Require MonadVM.Gas.
Require MonadVM.Uint64.
Require MonadVM.Evmc.

Section ParameterLength.
Context `{F : MonadVM.Precompiles.Modexp.Make.FArgs}.
Context `{UCount : RocqOfOCaml.Basics.Unreachable
  MonadVM.Support.UintN.t}.
Context `{UU256Repr : RocqOfOCaml.Basics.Unreachable
  MonadVM.Numeric.U256.Repr.t}.
Context `{UU256 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
Context `{UInt : RocqOfOCaml.Basics.Unreachable int}.
Context `{UAscii : RocqOfOCaml.Basics.Unreachable ascii}.
Context `{UFallback : RocqOfOCaml.Basics.Unreachable
  (MonadVM.Precompiles.Utils.Precompile.t MonadVM.Support.UintN.t)}.

Lemma modexp_parameter_length_gas_safe :
  (let revision :=
    (@MonadVM.Precompiles.Modexp.Make.Revision F).(MonadVM.Precompiles.Modexp.Make_Revision_signature.revision) in
   revision = MonadVM.Support.Variants.Revision.Eight \/
   revision = MonadVM.Support.Variants.Revision.Nine) ->
  precompile_gas_safe
    (@MonadVM.Precompiles.Modexp.Make.parameter_length
      F UCount UU256Repr UU256 UInt UAscii UFallback).
Proof.
  intros [HEight | HNine].
  - unfold MonadVM.Precompiles.Modexp.Make.parameter_length.
    rewrite HEight.
    apply precompile_fmap_gas_safe.
    unfold MonadVM.Precompiles.Utils.Precompile.u256.
    apply precompile_numeric_reader_gas_safe.
  - unfold MonadVM.Precompiles.Modexp.Make.parameter_length.
    rewrite HNine.
    eapply precompile_bind_gas_safe.
    + apply precompile_fmap_gas_safe.
      unfold MonadVM.Precompiles.Utils.Precompile.u256.
      apply precompile_numeric_reader_gas_safe.
    + intro length.
      eapply precompile_bind_gas_safe.
      * apply precompile_when_gas_safe.
        apply precompile_fail_gas_safe.
      * intro ignored. apply precompile_return_gas_safe.
Qed.

Context `{UZ : RocqOfOCaml.Basics.Unreachable Z.t}.
Context `{U64 : RocqOfOCaml.Basics.Unreachable MonadVM.Uint64.t}.
Context `{UGas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
Context `{UAddress : RocqOfOCaml.Basics.Unreachable
  MonadVM.Chain.Ethereum.Address.t}.
Context `{UBytes : RocqOfOCaml.Basics.Unreachable
  MonadVM.Byte_string.Bytes.t}.
Context `{UUnit : RocqOfOCaml.Basics.Unreachable unit}.
Context `{UString : RocqOfOCaml.Basics.Unreachable string}.
Context `{UPair : RocqOfOCaml.Basics.Unreachable (int * int)}.
Context `{UMul2 : RocqOfOCaml.Basics.Unreachable
  (MonadVM.Support.UintN.Impl.t -> MonadVM.Support.UintN.Impl.t ->
    MonadVM.Support.UintN.Impl.t)}.
Context `{UDiv2 : RocqOfOCaml.Basics.Unreachable
  (MonadVM.Support.UintN.Impl.t -> MonadVM.Support.UintN.Impl.t ->
    MonadVM.Support.UintN.t)}.
Context `{UMul4 : RocqOfOCaml.Basics.Unreachable
  (MonadVM.Support.UintN.Impl.t -> MonadVM.Support.UintN.Impl.t ->
    MonadVM.Support.UintN.Impl.t -> MonadVM.Support.UintN.Impl.t ->
    MonadVM.Support.UintN.Impl.t)}.

Local Ltac modexp_gas_safe Hrevision :=
  cbn zeta;
  lazymatch goal with
  | |- precompile_gas_safe
      (MonadVM.Precompiles.Utils.Precompile.op_letdollar _ _) =>
      eapply precompile_bind_gas_safe;
        [modexp_gas_safe Hrevision | intro; modexp_gas_safe Hrevision]
  | |- precompile_gas_safe
      (MonadVM.Precompiles.Utils.Precompile.op_ltdollargt _ _) =>
      apply precompile_fmap_gas_safe; modexp_gas_safe Hrevision
  | |- precompile_gas_safe
      (MonadVM.Precompiles.Modexp.Make.parameter_length) =>
      apply modexp_parameter_length_gas_safe; exact Hrevision
  | |- precompile_gas_safe
      (MonadVM.Precompiles.Utils.Precompile.spend_gas _) =>
      apply precompile_spend_gas_safe
  | |- precompile_gas_safe
      (MonadVM.Precompiles.Utils.Precompile.bytes_value _) =>
      apply precompile_bytes_value_gas_safe
  | |- precompile_gas_safe
      (MonadVM.Precompiles.Utils.Precompile._return _) =>
      apply precompile_return_gas_safe
  | |- precompile_gas_safe (if ?condition then _ else _) =>
      destruct condition; modexp_gas_safe Hrevision
  | |- precompile_gas_safe ?other =>
      fail 1 "unhandled Modexp precompile step" other
  end.

Lemma generated_modexp_precompile_gas_bounded
    (msg : MonadVM.Evmc.Message.t) :
  valid_int64_repr msg.(MonadVM.Evmc.Message.t.gas) ->
  (let revision :=
    (@MonadVM.Precompiles.Modexp.Make.Revision F).(MonadVM.Precompiles.Modexp.Make_Revision_signature.revision) in
   revision = MonadVM.Support.Variants.Revision.Eight \/
   revision = MonadVM.Support.Variants.Revision.Nine) ->
  (RocqOfOCaml.OCamlZ.of_int64_unsigned
    (@MonadVM.Precompiles.Modexp.Make.precompile
      F UZ U64 UCount UU256Repr UU256 UGas UAddress UBytes
      UUnit UString UInt UAscii UPair UMul2 UDiv2 UMul4 UFallback
      msg).(MonadVM.Evmc.Result.t.gas_left)
    <= RocqOfOCaml.OCamlZ.of_int64_unsigned
      msg.(MonadVM.Evmc.Message.t.gas))%Z.
Proof.
  intros Hvalid Hrevision.
  unfold MonadVM.Precompiles.Modexp.Make.precompile.
  eapply (@precompile_run_gas_safe_bounded UAddress UUnit UInt).
  - exact Hvalid.
  - modexp_gas_safe Hrevision.
Qed.
End ParameterLength.
