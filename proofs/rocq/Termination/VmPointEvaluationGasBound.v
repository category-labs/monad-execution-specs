(** The generated point-evaluation precompile cannot return more gas. *)

From Stdlib Require Import ZArith.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import MonadExecutionSpecs.Termination.VmUnsignedGas.
Require Import MonadExecutionSpecs.Termination.VmPrecompileGasInvariant.
Require MonadVM.Precompiles.Point_evaluation.
Require MonadVM.Precompiles.Utils.
Require MonadVM.Evmc.
Require MonadVM.Gas.
Require MonadVM.Uint64.
Require MonadVM.Numeric.
Require MonadVM.Support.UintN.
Require MonadVM.Chain.Ethereum.
Require MonadVM.Byte_string.
Require MonadVM.Ec.Bls12_381.
Require MonadVM.Ec.Algebra.
Require MonadVM.Ec.Curve.

Local Open Scope Z_scope.

Section PointEvaluation.
Context `{UZ : RocqOfOCaml.Basics.Unreachable Z.t}.
Context `{UCount : RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}.
Context `{UIntegerBase : RocqOfOCaml.Basics.Unreachable
      MonadVM.Numeric.IntegerBase.(MonadVM.Numeric.Make.Make_result.t)}.
Context `{UArrayFp : RocqOfOCaml.Basics.Unreachable
      (RocqOfOCaml.OCamlIarray.t
        (MonadVM.Ec.Bls12_381.F_p.t
        (_rocq_assumption_0 := UZ)
        (_rocq_assumption_1 := UCount)
        (_rocq_assumption_2 := UIntegerBase)))}.
Context `{UInteger : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.Integer.t}.
Context `{UFp : RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Bls12_381.F_p.t
        (_rocq_assumption_0 := UZ)
        (_rocq_assumption_1 := UCount)
        (_rocq_assumption_2 := UIntegerBase))}.
Context `{UBool : RocqOfOCaml.Basics.Unreachable bool}.
Context `{UArrayFpPair : RocqOfOCaml.Basics.Unreachable
      (RocqOfOCaml.OCamlIarray.t
        (MonadVM.Ec.Bls12_381.F_p.t
          (_rocq_assumption_0 := UZ)
          (_rocq_assumption_1 := UCount)
          (_rocq_assumption_2 := UIntegerBase))
       * RocqOfOCaml.OCamlIarray.t
        (MonadVM.Ec.Bls12_381.F_p.t
          (_rocq_assumption_0 := UZ)
          (_rocq_assumption_1 := UCount)
          (_rocq_assumption_2 := UIntegerBase)))}.
Context `{USeqFp12 : RocqOfOCaml.Basics.Unreachable
      (RocqOfOCaml.OCamlSeq.t
        (MonadVM.Ec.Bls12_381.F_p12.t
        (_rocq_assumption_0 := UZ)
        (_rocq_assumption_1 := UCount)
        (_rocq_assumption_2 := UIntegerBase)
        (_rocq_assumption_3 := UArrayFp)
        (_rocq_assumption_4 := UInteger)
        (_rocq_assumption_5 := UFp)
        (_rocq_assumption_6 := UBool)
        (_rocq_assumption_7 := UArrayFpPair)))}.
Context `{UArrayInt : RocqOfOCaml.Basics.Unreachable (RocqOfOCaml.OCamlIarray.t int)}.
Context `{U64 : RocqOfOCaml.Basics.Unreachable MonadVM.Uint64.t}.
Context `{UU256 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
Context `{UGas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
Context `{UC2 : RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Bls12_381.C_2
        (_rocq_module_assumption_0 := UZ)
        (_rocq_module_assumption_1 := UCount)
        (_rocq_module_assumption_2 := UInteger)
        (_rocq_module_assumption_3 := UIntegerBase)
        (_rocq_module_assumption_4 := UFp)).(MonadVM.Ec.Curve.Make.Make_result.t)}.
Context `{UG2Point : RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Bls12_381.G_2
        (_rocq_module_assumption_0 := UZ)
        (_rocq_module_assumption_1 := UCount)
        (_rocq_module_assumption_2 := UInteger)
        (_rocq_module_assumption_3 := UIntegerBase)
        (_rocq_module_assumption_4 := UFp)
        (_rocq_module_assumption_5 := UC2)).(MonadVM.Ec.Curve.Make.Subgroup.Subgroup_result.t)}.
Context `{UAddress : RocqOfOCaml.Basics.Unreachable MonadVM.Chain.Ethereum.Address.t}.
Context `{UBytes : RocqOfOCaml.Basics.Unreachable MonadVM.Byte_string.Bytes.t}.
Context `{UUnit : RocqOfOCaml.Basics.Unreachable unit}.
Context `{UString : RocqOfOCaml.Basics.Unreachable string}.
Context `{UOptionFp : RocqOfOCaml.Basics.Unreachable
      (option
        (MonadVM.Ec.Bls12_381.F_p.t
        (_rocq_assumption_0 := UZ)
        (_rocq_assumption_1 := UCount)
        (_rocq_assumption_2 := UIntegerBase)))}.
Context `{UInt : RocqOfOCaml.Basics.Unreachable int}.
Context `{UAscii : RocqOfOCaml.Basics.Unreachable ascii}.
Context `{UPairFp12 : RocqOfOCaml.Basics.Unreachable
      ((MonadVM.Ec.Bls12_381.F_p12.t
        (_rocq_assumption_0 := UZ)
        (_rocq_assumption_1 := UCount)
        (_rocq_assumption_2 := UIntegerBase)
        (_rocq_assumption_3 := UArrayFp)
        (_rocq_assumption_4 := UInteger)
        (_rocq_assumption_5 := UFp)
        (_rocq_assumption_6 := UBool)
        (_rocq_assumption_7 := UArrayFpPair))
        *
        (MonadVM.Ec.Bls12_381.F_p12.t
        (_rocq_assumption_0 := UZ)
        (_rocq_assumption_1 := UCount)
        (_rocq_assumption_2 := UIntegerBase)
        (_rocq_assumption_3 := UArrayFp)
        (_rocq_assumption_4 := UInteger)
        (_rocq_assumption_5 := UFp)
        (_rocq_assumption_6 := UBool)
        (_rocq_assumption_7 := UArrayFpPair)))}.
Context `{UPairInt : RocqOfOCaml.Basics.Unreachable (int * int)}.
Context `{USeqEndo : RocqOfOCaml.Basics.Unreachable
      (RocqOfOCaml.OCamlSeq.t
        (MonadVM.Ec.Bls12_381.F_p12.t
        (_rocq_assumption_0 := UZ)
        (_rocq_assumption_1 := UCount)
        (_rocq_assumption_2 := UIntegerBase)
        (_rocq_assumption_3 := UArrayFp)
        (_rocq_assumption_4 := UInteger)
        (_rocq_assumption_5 := UFp)
        (_rocq_assumption_6 := UBool)
        (_rocq_assumption_7 := UArrayFpPair))
      ->
      RocqOfOCaml.OCamlSeq.t
        (MonadVM.Ec.Bls12_381.F_p12.t
        (_rocq_assumption_0 := UZ)
        (_rocq_assumption_1 := UCount)
        (_rocq_assumption_2 := UIntegerBase)
        (_rocq_assumption_3 := UArrayFp)
        (_rocq_assumption_4 := UInteger)
        (_rocq_assumption_5 := UFp)
        (_rocq_assumption_6 := UBool)
        (_rocq_assumption_7 := UArrayFpPair)))}.
Context `{UFpOption : RocqOfOCaml.Basics.Unreachable
      ((MonadVM.Ec.Bls12_381.F_p.t
        (_rocq_assumption_0 := UZ)
        (_rocq_assumption_1 := UCount)
        (_rocq_assumption_2 := UIntegerBase))
      ->
      option
        (MonadVM.Ec.Bls12_381.F_p.t
        (_rocq_assumption_0 := UZ)
        (_rocq_assumption_1 := UCount)
        (_rocq_assumption_2 := UIntegerBase)))}.
Context `{UUnderlyingRing : RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Bls12_381.F_p12.MonadVM_Ec_Algebra_Polynomial_extension_include
        (_rocq_module_assumption_0 := UZ)
        (_rocq_module_assumption_1 := UCount)
        (_rocq_module_assumption_2 := UIntegerBase)
        (_rocq_module_assumption_3 := UArrayFp)
        (_rocq_module_assumption_4 := UInteger)
        (_rocq_module_assumption_5 := UFp)
        (_rocq_module_assumption_6 := UBool)
        (_rocq_module_assumption_7 := UArrayFpPair)).(MonadVM.Ec.Algebra.Polynomial_extension.Polynomial_extension_result.Underlying_ring).(MonadVM.Ec.Algebra.Polynomial_ring.Polynomial_ring_result.t)}.
Context `{UG2Curve : RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Bls12_381.G_2
        (_rocq_module_assumption_0 := UZ)
        (_rocq_module_assumption_1 := UCount)
        (_rocq_module_assumption_2 := UInteger)
        (_rocq_module_assumption_3 := UIntegerBase)
        (_rocq_module_assumption_4 := UFp)
        (_rocq_module_assumption_5 := UC2)).(MonadVM.Ec.Curve.Make.Subgroup.Subgroup_result.curve)}.
Context `{UC1 : RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Bls12_381.C_1
        (_rocq_module_assumption_0 := UZ)
        (_rocq_module_assumption_1 := UCount)
        (_rocq_module_assumption_2 := UInteger)
        (_rocq_module_assumption_3 := UIntegerBase)
        (_rocq_module_assumption_4 := UFp)).(MonadVM.Ec.Curve.Make.Make_result.t)}.
Context `{UG1Curve : RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Bls12_381.G_1
        (_rocq_module_assumption_0 := UZ)
        (_rocq_module_assumption_1 := UCount)
        (_rocq_module_assumption_2 := UInteger)
        (_rocq_module_assumption_3 := UIntegerBase)
        (_rocq_module_assumption_4 := UFp)
        (_rocq_module_assumption_5 := UC1)).(MonadVM.Ec.Curve.Make.Subgroup.Subgroup_result.curve)}.
Context `{UB48 : RocqOfOCaml.Basics.Unreachable
      MonadVM.Byte_string.B48.(MonadVM.Byte_string.Fixed.Fixed_result.t)}.
Context `{UB32 : RocqOfOCaml.Basics.Unreachable
      MonadVM.Byte_string.B32.(MonadVM.Byte_string.Fixed.Fixed_result.t)}.

Lemma generated_point_evaluation_gas_bounded
    (msg : MonadVM.Evmc.Message.t) :
  valid_int64_repr msg.(MonadVM.Evmc.Message.t.gas) ->
  (RocqOfOCaml.OCamlZ.of_int64_unsigned
    (@MonadVM.Precompiles.Point_evaluation.precompile
      UZ UCount UIntegerBase UArrayFp UInteger UFp UBool UArrayFpPair
      USeqFp12
      UArrayInt U64 UU256 UGas UC2 UG2Point UAddress UBytes UUnit
      UString UOptionFp UInt UAscii UPairFp12 UPairInt USeqEndo
      UFpOption UUnderlyingRing UG2Curve UC1 UG1Curve UB48 UB32
      msg).(MonadVM.Evmc.Result.t.gas_left)
    <= RocqOfOCaml.OCamlZ.of_int64_unsigned
      msg.(MonadVM.Evmc.Message.t.gas))%Z.
Proof.
  intro Hvalid.
  unfold MonadVM.Precompiles.Point_evaluation.precompile.
  eapply (@precompile_run_gas_safe_bounded UAddress UUnit UInt).
  - exact Hvalid.
  - cbn zeta.
    eapply precompile_bind_gas_safe.
    + apply precompile_ensure_gas_safe.
    + intro ignored_length.
      eapply precompile_bind_gas_safe.
      * apply precompile_spend_gas_safe.
      * intro ignored_spend.
        eapply precompile_bind_gas_safe.
        -- unfold MonadVM.Precompiles.Utils.Precompile.b32.
           apply precompile_byte_reader_gas_safe.
        -- intro versioned_hash.
           eapply precompile_bind_gas_safe.
           ++ unfold MonadVM.Precompiles.Utils.Precompile.b32.
              apply precompile_byte_reader_gas_safe.
           ++ intro z_value.
              eapply precompile_bind_gas_safe.
              ** unfold MonadVM.Precompiles.Utils.Precompile.b32.
                 apply precompile_byte_reader_gas_safe.
              ** intro y_value.
                 eapply precompile_bind_gas_safe.
                 --- unfold MonadVM.Precompiles.Utils.Precompile.b48.
                     apply precompile_byte_reader_gas_safe.
                 --- intro commitment.
                     eapply precompile_bind_gas_safe.
                     +++ unfold MonadVM.Precompiles.Utils.Precompile.b48.
                         apply precompile_byte_reader_gas_safe.
                     +++ intro kzg_proof.
                         eapply precompile_bind_gas_safe.
                         *** apply precompile_ensure_gas_safe.
                         *** intro ignored_hash.
                             eapply precompile_bind_gas_safe.
                             ---- apply precompile_option_or_fail_gas_safe.
                             ---- intro ignored_verify.
                                  apply precompile_return_gas_safe.
Qed.
End PointEvaluation.
