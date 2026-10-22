(** Generated alt_bn128 add and multiply cannot return more gas. *)

From Stdlib Require Import ZArith.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import MonadExecutionSpecs.Termination.VmUnsignedGas.
Require Import MonadExecutionSpecs.Termination.VmPrecompileGasInvariant.
Require Import MonadExecutionSpecs.Termination.VmEcPrecompileGasInvariant.
Require MonadVM.Precompiles.Alt_bn128.
Require MonadVM.Precompiles.Utils.
Require MonadVM.Evmc.
Require MonadVM.Gas.
Require MonadVM.Uint64.
Require MonadVM.Numeric.
Require MonadVM.Support.UintN.
Require MonadVM.Chain.Ethereum.
Require MonadVM.Byte_string.
Require MonadVM.Ec.Alt_bn128.
Require MonadVM.Ec.Algebra.
Require MonadVM.Ec.Curve.

Local Open Scope Z_scope.

Section AltBn128.
Context `{UZ : RocqOfOCaml.Basics.Unreachable Z.t}.
Context `{U64 : RocqOfOCaml.Basics.Unreachable MonadVM.Uint64.t}.
Context `{UCount : RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}.
Context `{UInteger : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.Integer.t}.
Context `{UGas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
Context `{UAddress : RocqOfOCaml.Basics.Unreachable MonadVM.Chain.Ethereum.Address.t}.
Context `{UBytes : RocqOfOCaml.Basics.Unreachable MonadVM.Byte_string.Bytes.t}.
Context `{UUnit : RocqOfOCaml.Basics.Unreachable unit}.
Context `{UInt : RocqOfOCaml.Basics.Unreachable int}.
Context `{UAscii : RocqOfOCaml.Basics.Unreachable ascii}.
Context `{UIntegerBase : RocqOfOCaml.Basics.Unreachable
  MonadVM.Numeric.IntegerBase.(MonadVM.Numeric.Make.Make_result.t)}.
Context `{UFp : RocqOfOCaml.Basics.Unreachable
  (MonadVM.Ec.Alt_bn128.F_p
    (_rocq_module_assumption_0 := UZ)
    (_rocq_module_assumption_1 := UCount)
    (_rocq_module_assumption_2 := UIntegerBase)).(MonadVM.Ec.Algebra.Prime_field.Prime_field_result.t)}.
Context `{UC2 : RocqOfOCaml.Basics.Unreachable
  (MonadVM.Ec.Alt_bn128.C_2
    (_rocq_module_assumption_0 := UZ)
    (_rocq_module_assumption_1 := UCount)
    (_rocq_module_assumption_2 := UInteger)
    (_rocq_module_assumption_3 := UIntegerBase)
    (_rocq_module_assumption_4 := UFp)).(MonadVM.Ec.Curve.Make.Make_result.t)}.
Context `{UC1 : RocqOfOCaml.Basics.Unreachable
  (MonadVM.Ec.Alt_bn128.C_1
    (_rocq_module_assumption_0 := UZ)
    (_rocq_module_assumption_1 := UCount)
    (_rocq_module_assumption_2 := UInteger)
    (_rocq_module_assumption_3 := UIntegerBase)
    (_rocq_module_assumption_4 := UFp)).(MonadVM.Ec.Curve.Make.Make_result.t)}.
Context `{UB32 : RocqOfOCaml.Basics.Unreachable
  MonadVM.Byte_string.B32.(MonadVM.Byte_string.Fixed.Fixed_result.t)}.

Lemma generated_alt_bn128_add_precompile_gas_bounded
    (msg : MonadVM.Evmc.Message.t) :
  valid_int64_repr msg.(MonadVM.Evmc.Message.t.gas) ->
  (RocqOfOCaml.OCamlZ.of_int64_unsigned
    (@MonadVM.Precompiles.Alt_bn128.add
      UZ U64 UCount UInteger UGas UAddress UBytes UUnit UInt UAscii
      UIntegerBase UFp UC2 UC1 UB32 msg).(MonadVM.Evmc.Result.t.gas_left)
    <= RocqOfOCaml.OCamlZ.of_int64_unsigned
      msg.(MonadVM.Evmc.Message.t.gas))%Z.
Proof.
  intro Hvalid.
  unfold MonadVM.Precompiles.Alt_bn128.add.
  eapply (@precompile_run_gas_safe_bounded UAddress UUnit UInt).
  - exact Hvalid.
  - cbn zeta.
    eapply precompile_bind_gas_safe.
    + apply precompile_spend_gas_safe.
    + intro ignored.
      eapply precompile_bind_gas_safe.
      * apply ec_curve_point_gas_safe.
      * intro first.
        eapply precompile_bind_gas_safe.
        -- apply ec_curve_point_gas_safe.
        -- intro second. apply precompile_return_gas_safe.
Qed.

Context `{UU256Repr : RocqOfOCaml.Basics.Unreachable
  MonadVM.Numeric.U256.Repr.t}.
Context `{UU256 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.

Lemma generated_alt_bn128_mul_precompile_gas_bounded
    (msg : MonadVM.Evmc.Message.t) :
  valid_int64_repr msg.(MonadVM.Evmc.Message.t.gas) ->
  (RocqOfOCaml.OCamlZ.of_int64_unsigned
    (@MonadVM.Precompiles.Alt_bn128.mul
      UZ U64 UCount UU256Repr UU256 UInteger UGas UAddress UBytes
      UUnit UInt UAscii UIntegerBase UFp UC2 UC1 UB32
      msg).(MonadVM.Evmc.Result.t.gas_left)
    <= RocqOfOCaml.OCamlZ.of_int64_unsigned
      msg.(MonadVM.Evmc.Message.t.gas))%Z.
Proof.
  intro Hvalid.
  unfold MonadVM.Precompiles.Alt_bn128.mul.
  eapply (@precompile_run_gas_safe_bounded UAddress UUnit UInt).
  - exact Hvalid.
  - cbn zeta.
    eapply precompile_bind_gas_safe.
    + apply precompile_spend_gas_safe.
    + intro ignored.
      eapply precompile_bind_gas_safe.
      * apply ec_curve_point_gas_safe.
      * intro point.
        eapply precompile_bind_gas_safe.
        -- apply precompile_fmap_gas_safe.
           unfold MonadVM.Precompiles.Utils.Precompile.u256.
           apply precompile_numeric_reader_gas_safe.
        -- intro scalar. apply precompile_return_gas_safe.
Qed.

Context `{UBool : RocqOfOCaml.Basics.Unreachable bool}.
Context `{UArrayFp : RocqOfOCaml.Basics.Unreachable
  (RocqOfOCaml.OCamlIarray.t
    (MonadVM.Ec.Alt_bn128.F_p
      (_rocq_module_assumption_0 := UZ)
      (_rocq_module_assumption_1 := UCount)
      (_rocq_module_assumption_2 := UIntegerBase)).(MonadVM.Ec.Algebra.Prime_field.Prime_field_result.t))}.
Context `{UArrayFpPair : RocqOfOCaml.Basics.Unreachable
  ((RocqOfOCaml.OCamlIarray.t
    (MonadVM.Ec.Alt_bn128.F_p
      (_rocq_module_assumption_0 := UZ)
      (_rocq_module_assumption_1 := UCount)
      (_rocq_module_assumption_2 := UIntegerBase)).(MonadVM.Ec.Algebra.Prime_field.Prime_field_result.t))
   * (RocqOfOCaml.OCamlIarray.t
    (MonadVM.Ec.Alt_bn128.F_p
      (_rocq_module_assumption_0 := UZ)
      (_rocq_module_assumption_1 := UCount)
      (_rocq_module_assumption_2 := UIntegerBase)).(MonadVM.Ec.Algebra.Prime_field.Prime_field_result.t)))}.

Local Definition Fp12Type : Set :=
  MonadVM.Ec.Alt_bn128.F_p12.t
    (_rocq_assumption_0 := UZ)
    (_rocq_assumption_1 := UCount)
    (_rocq_assumption_2 := UInteger)
    (_rocq_assumption_3 := UBool)
    (_rocq_assumption_4 := UIntegerBase)
    (_rocq_assumption_5 := UArrayFp)
    (_rocq_assumption_6 := UFp)
    (_rocq_assumption_7 := UArrayFpPair).

Context `{USeqFp12 : RocqOfOCaml.Basics.Unreachable
  (RocqOfOCaml.OCamlSeq.t Fp12Type)}.
Context `{UPairFp12 : RocqOfOCaml.Basics.Unreachable
  (Fp12Type * Fp12Type)}.
Context `{UPairInt : RocqOfOCaml.Basics.Unreachable (int * int)}.
Context `{USeqEndo : RocqOfOCaml.Basics.Unreachable
  (RocqOfOCaml.OCamlSeq.t Fp12Type ->
    RocqOfOCaml.OCamlSeq.t Fp12Type)}.

Local Definition Fp12FieldType : Set :=
  (MonadVM.Ec.Alt_bn128.F_p12.MonadVM_Ec_Algebra_Polynomial_extension_include_fargs
    (_rocq_module_assumption_0 := UZ)
    (_rocq_module_assumption_1 := UCount)
    (_rocq_module_assumption_2 := UInteger)
    (_rocq_module_assumption_3 := UBool)
    (_rocq_module_assumption_4 := UIntegerBase)
    (_rocq_module_assumption_5 := UArrayFp)
    (_rocq_module_assumption_6 := UFp)
    (_rocq_module_assumption_7 := UArrayFpPair))
      .(MonadVM.Ec.Algebra.Polynomial_extension.F)
      .(MonadVM.Ec.Algebra.FIELD.t).

Context `{UArrayField : RocqOfOCaml.Basics.Unreachable
  (RocqOfOCaml.OCamlIarray.t Fp12FieldType)}.
Context `{UField : RocqOfOCaml.Basics.Unreachable Fp12FieldType}.

Local Definition UnderlyingRingType : Set :=
  (MonadVM.Ec.Alt_bn128.F_p12.MonadVM_Ec_Algebra_Polynomial_extension_include
    (_rocq_module_assumption_0 := UZ)
    (_rocq_module_assumption_1 := UCount)
    (_rocq_module_assumption_2 := UInteger)
    (_rocq_module_assumption_3 := UBool)
    (_rocq_module_assumption_4 := UIntegerBase)
    (_rocq_module_assumption_5 := UArrayFp)
    (_rocq_module_assumption_6 := UFp)
    (_rocq_module_assumption_7 := UArrayFpPair))
      .(MonadVM.Ec.Algebra.Polynomial_extension.Polynomial_extension_result.Underlying_ring)
      .(MonadVM.Ec.Algebra.Polynomial_ring.Polynomial_ring_result.t).

Context `{URing : RocqOfOCaml.Basics.Unreachable UnderlyingRingType}.
Context `{UFp2Fallback : RocqOfOCaml.Basics.Unreachable
  (MonadVM.Precompiles.Utils.Precompile.t
    (MonadVM.Precompiles.Alt_bn128.opened_module_165_fargs
      (_rocq_module_assumption_0 := UZ)
      (_rocq_module_assumption_1 := UCount)
      (_rocq_module_assumption_2 := UInteger)
      (_rocq_module_assumption_3 := UInt)
      (_rocq_module_assumption_4 := UAscii)
      (_rocq_module_assumption_5 := UIntegerBase)
      (_rocq_module_assumption_6 := UFp)
      (_rocq_module_assumption_7 := UC2)
      (_rocq_module_assumption_8 := UC1)
      (_rocq_module_assumption_9 := UB32))
      .(MonadVM.Precompiles.Utils.Ec_precompile_utils.M)
      .(MonadVM.Precompiles.Utils.Ec_precompile_utils_M_signature.F_p2_t))}.

Lemma generated_alt_bn128_pairing_precompile_gas_bounded
    (msg : MonadVM.Evmc.Message.t) :
  valid_int64_repr msg.(MonadVM.Evmc.Message.t.gas) ->
  (RocqOfOCaml.OCamlZ.of_int64_unsigned
    (@MonadVM.Precompiles.Alt_bn128.pairing_check
      UZ UCount UInteger UBool UIntegerBase UArrayFp UFp UArrayFpPair
      USeqFp12
      U64 UU256Repr UU256 UGas UAddress UUnit UInt UAscii
      UPairFp12 UPairInt USeqEndo UArrayField UField URing UC2 UC1
      UB32 UFp2Fallback msg).(MonadVM.Evmc.Result.t.gas_left)
    <= RocqOfOCaml.OCamlZ.of_int64_unsigned
      msg.(MonadVM.Evmc.Message.t.gas))%Z.
Proof.
  intro Hvalid.
  unfold MonadVM.Precompiles.Alt_bn128.pairing_check.
  eapply (@precompile_run_gas_safe_bounded UAddress UUnit UInt).
  - exact Hvalid.
  - cbn zeta.
    eapply precompile_bind_gas_safe.
    + apply precompile_ensure_gas_safe.
    + intro ignored.
      eapply precompile_bind_gas_safe.
      * apply precompile_spend_gas_safe.
      * intro ignored_spend.
        eapply precompile_bind_gas_safe.
        -- apply precompile_list_value_gas_safe.
           apply precompile_pair_value_gas_safe.
           ++ apply ec_subgroup_point_gas_safe.
           ++ apply ec_extension_subgroup_point_gas_safe.
              unfold supported_complex_encoding,
                complex_encoding_tag.
              cbn. right. reflexivity.
        -- intro pairs. apply precompile_return_gas_safe.
Qed.
End AltBn128.
