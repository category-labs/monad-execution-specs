(** ECRECOVER's generated precompile computation cannot add gas. *)

From Stdlib Require Import ZArith.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import MonadExecutionSpecs.Termination.VmUnsignedGas.
Require Import MonadExecutionSpecs.Termination.VmPrecompileGasInvariant.
Require MonadVM.Precompiles.
Require MonadVM.Evmc.
Require MonadVM.Gas.
Require MonadVM.Uint64.
Require MonadVM.Numeric.
Require MonadVM.Chain.Ethereum.
Require MonadVM.Byte_string.

Local Open Scope Z_scope.

Section Ecrecover.
Context `{UZ : RocqOfOCaml.Basics.Unreachable Z.t}.
Context `{U64 : RocqOfOCaml.Basics.Unreachable MonadVM.Uint64.t}.
Context `{UU8Repr : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U8.Repr.t}.
Context `{UU8 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U8.t}.
Context `{UU256Repr : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.Repr.t}.
Context `{UU256 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
Context `{UGas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
Context `{UAddress : RocqOfOCaml.Basics.Unreachable MonadVM.Chain.Ethereum.Address.t}.
Context `{UB20 : RocqOfOCaml.Basics.Unreachable MonadVM.Byte_string.B20.t}.
Context `{UUnit : RocqOfOCaml.Basics.Unreachable unit}.
Context `{UString : RocqOfOCaml.Basics.Unreachable string}.
Context `{UInt : RocqOfOCaml.Basics.Unreachable int}.
Context `{UAscii : RocqOfOCaml.Basics.Unreachable ascii}.
Context `{UPair : RocqOfOCaml.Basics.Unreachable (int * int)}.
Context `{UB32 : RocqOfOCaml.Basics.Unreachable
  MonadVM.Byte_string.B32.(MonadVM.Byte_string.Fixed.Fixed_result.t)}.

Lemma generated_ecrecover_precompile_gas_bounded
    (msg : MonadVM.Evmc.Message.t) :
  valid_int64_repr msg.(MonadVM.Evmc.Message.t.gas) ->
  (RocqOfOCaml.OCamlZ.of_int64_unsigned
    (@MonadVM.Precompiles.ecrecover UZ U64 UU8Repr UU8
      UU256Repr UU256 UGas UAddress UB20 UUnit UString
      UInt UAscii UPair UB32 msg).(MonadVM.Evmc.Result.t.gas_left)
    <= RocqOfOCaml.OCamlZ.of_int64_unsigned
      msg.(MonadVM.Evmc.Message.t.gas))%Z.
Proof.
  intro Hvalid.
  unfold MonadVM.Precompiles.ecrecover.
  eapply (@precompile_run_gas_safe_bounded UAddress UUnit UInt).
  - exact Hvalid.
  - cbn zeta.
    eapply precompile_bind_gas_safe.
    + apply precompile_spend_gas_safe.
    + intro ignored.
      eapply precompile_bind_gas_safe.
      * apply precompile_byte_reader_gas_safe.
      * intro hash.
        eapply precompile_bind_gas_safe.
        -- apply precompile_numeric_reader_gas_safe.
        -- intro v.
           eapply precompile_bind_gas_safe.
           ++ apply precompile_numeric_reader_gas_safe.
           ++ intro r.
              eapply precompile_bind_gas_safe.
              ** apply precompile_numeric_reader_gas_safe.
              ** intro s. apply precompile_return_gas_safe.
Qed.
End Ecrecover.
