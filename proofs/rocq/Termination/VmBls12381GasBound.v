(** Generated BLS12-381 G1 operations cannot return more gas. *)

From Stdlib Require Import ZArith.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import MonadExecutionSpecs.Termination.VmUnsignedGas.
Require Import MonadExecutionSpecs.Termination.VmPrecompileGasInvariant.
Require Import MonadExecutionSpecs.Termination.VmEcPrecompileGasInvariant.
Require MonadVM.Precompiles.Bls12_381.
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

Section Bls12381G1.
Context `{UZ : RocqOfOCaml.Basics.Unreachable Z.t}.
Context `{U64 : RocqOfOCaml.Basics.Unreachable MonadVM.Uint64.t}.
Context `{UCount : RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}.
Context `{UInteger : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.Integer.t}.
Context `{UGas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
Context `{UIntegerBase : RocqOfOCaml.Basics.Unreachable
  MonadVM.Numeric.IntegerBase.(MonadVM.Numeric.Make.Make_result.t)}.
Context `{UFp : RocqOfOCaml.Basics.Unreachable
  (MonadVM.Ec.Bls12_381.F_p.t
    (_rocq_assumption_0 := UZ)
    (_rocq_assumption_1 := UCount)
    (_rocq_assumption_2 := UIntegerBase))}.
Context `{UAddress : RocqOfOCaml.Basics.Unreachable
  MonadVM.Chain.Ethereum.Address.t}.
Context `{UBytes : RocqOfOCaml.Basics.Unreachable
  MonadVM.Byte_string.Bytes.t}.
Context `{UUnit : RocqOfOCaml.Basics.Unreachable unit}.
Context `{UInt : RocqOfOCaml.Basics.Unreachable int}.
Context `{UAscii : RocqOfOCaml.Basics.Unreachable ascii}.
Context `{UC2 : RocqOfOCaml.Basics.Unreachable
  (MonadVM.Ec.Bls12_381.C_2
    (_rocq_module_assumption_0 := UZ)
    (_rocq_module_assumption_1 := UCount)
    (_rocq_module_assumption_2 := UInteger)
    (_rocq_module_assumption_3 := UIntegerBase)
    (_rocq_module_assumption_4 := UFp)).(MonadVM.Ec.Curve.Make.Make_result.t)}.
Context `{UC1 : RocqOfOCaml.Basics.Unreachable
  (MonadVM.Ec.Bls12_381.C_1
    (_rocq_module_assumption_0 := UZ)
    (_rocq_module_assumption_1 := UCount)
    (_rocq_module_assumption_2 := UInteger)
    (_rocq_module_assumption_3 := UIntegerBase)
    (_rocq_module_assumption_4 := UFp)).(MonadVM.Ec.Curve.Make.Make_result.t)}.
Context `{UB64 : RocqOfOCaml.Basics.Unreachable
  MonadVM.Byte_string.B64.(MonadVM.Byte_string.Fixed.Fixed_result.t)}.

Lemma generated_bls12381_g1_add_gas_bounded
    (msg : MonadVM.Evmc.Message.t) :
  valid_int64_repr msg.(MonadVM.Evmc.Message.t.gas) ->
  (RocqOfOCaml.OCamlZ.of_int64_unsigned
    (@MonadVM.Precompiles.Bls12_381.g1_add
      UZ U64 UCount UInteger UGas UIntegerBase UFp UAddress UBytes
      UUnit UInt UAscii UC2 UC1 UB64 msg)
      .(MonadVM.Evmc.Result.t.gas_left)
    <= RocqOfOCaml.OCamlZ.of_int64_unsigned
      msg.(MonadVM.Evmc.Message.t.gas))%Z.
Proof.
  intro Hvalid.
  unfold MonadVM.Precompiles.Bls12_381.g1_add.
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
        -- apply ec_curve_point_gas_safe.
        -- intro first.
           eapply precompile_bind_gas_safe.
           ++ apply ec_curve_point_gas_safe.
           ++ intro second. apply precompile_return_gas_safe.
Qed.

Context `{UU256Repr : RocqOfOCaml.Basics.Unreachable
  MonadVM.Numeric.U256.Repr.t}.
Context `{UU256 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.

Lemma generated_bls12381_g1_msm_gas_bounded
    (msg : MonadVM.Evmc.Message.t) :
  valid_int64_repr msg.(MonadVM.Evmc.Message.t.gas) ->
  (RocqOfOCaml.OCamlZ.of_int64_unsigned
    (@MonadVM.Precompiles.Bls12_381.g1_msm
      UZ U64 UCount UU256Repr UU256 UInteger UGas UIntegerBase UFp
      UAddress UBytes UUnit UInt UAscii UC2 UC1 UB64 msg)
      .(MonadVM.Evmc.Result.t.gas_left)
    <= RocqOfOCaml.OCamlZ.of_int64_unsigned
      msg.(MonadVM.Evmc.Message.t.gas))%Z.
Proof.
  intro Hvalid.
  unfold MonadVM.Precompiles.Bls12_381.g1_msm.
  eapply (@precompile_run_gas_safe_bounded UAddress UUnit UInt).
  - exact Hvalid.
  - cbn zeta.
    eapply precompile_bind_gas_safe.
    + apply precompile_ensure_gas_safe.
    + intro ignored_length.
      eapply precompile_bind_gas_safe.
      * apply precompile_ensure_gas_safe.
      * intro ignored_count.
        eapply precompile_bind_gas_safe.
        -- apply precompile_spend_gas_safe.
        -- intro ignored_spend.
           eapply precompile_bind_gas_safe.
           ++ apply precompile_list_value_gas_safe.
              apply precompile_pair_value_gas_safe.
              ** apply ec_subgroup_point_gas_safe.
              ** unfold MonadVM.Precompiles.Utils.Precompile.u256.
                 apply precompile_numeric_reader_gas_safe.
           ++ intro points. apply precompile_return_gas_safe.
Qed.

Context `{UCurve2Bytes : RocqOfOCaml.Basics.Unreachable
  ((MonadVM.Ec.Bls12_381.C_2
    (_rocq_module_assumption_0 := UZ)
    (_rocq_module_assumption_1 := UCount)
    (_rocq_module_assumption_2 := UInteger)
    (_rocq_module_assumption_3 := UIntegerBase)
    (_rocq_module_assumption_4 := UFp)).(MonadVM.Ec.Curve.Make.Make_result.t)
    -> MonadVM.Byte_string.Bytes.t)}.
Context `{UFp2Fallback : RocqOfOCaml.Basics.Unreachable
  (MonadVM.Precompiles.Utils.Precompile.t
    (MonadVM.Precompiles.Bls12_381.opened_module_143_fargs
      (_rocq_module_assumption_0 := UZ)
      (_rocq_module_assumption_1 := UCount)
      (_rocq_module_assumption_2 := UInteger)
      (_rocq_module_assumption_3 := UIntegerBase)
      (_rocq_module_assumption_4 := UFp)
      (_rocq_module_assumption_5 := UInt)
      (_rocq_module_assumption_6 := UAscii)
      (_rocq_module_assumption_7 := UC2)
      (_rocq_module_assumption_8 := UC1)
      (_rocq_module_assumption_9 := UB64))
      .(MonadVM.Precompiles.Utils.Ec_precompile_utils.M)
      .(MonadVM.Precompiles.Utils.Ec_precompile_utils_M_signature.F_p2_t))}.

Lemma generated_bls12381_g2_add_gas_bounded
    (msg : MonadVM.Evmc.Message.t) :
  valid_int64_repr msg.(MonadVM.Evmc.Message.t.gas) ->
  (RocqOfOCaml.OCamlZ.of_int64_unsigned
    (@MonadVM.Precompiles.Bls12_381.g2_add
      UZ U64 UCount UInteger UGas UIntegerBase UFp UAddress UBytes
      UUnit UInt UAscii UC2 UC1 UB64 UCurve2Bytes UFp2Fallback
      msg).(MonadVM.Evmc.Result.t.gas_left)
    <= RocqOfOCaml.OCamlZ.of_int64_unsigned
      msg.(MonadVM.Evmc.Message.t.gas))%Z.
Proof.
  intro Hvalid.
  unfold MonadVM.Precompiles.Bls12_381.g2_add.
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
        -- apply ec_extension_curve_point_gas_safe.
           unfold supported_complex_encoding, complex_encoding_tag.
           cbn. left. reflexivity.
        -- intro first.
           eapply precompile_bind_gas_safe.
           ++ apply ec_extension_curve_point_gas_safe.
              unfold supported_complex_encoding, complex_encoding_tag.
              cbn. left. reflexivity.
           ++ intro second. apply precompile_return_gas_safe.
Qed.

Lemma generated_bls12381_g2_msm_gas_bounded
    (msg : MonadVM.Evmc.Message.t) :
  valid_int64_repr msg.(MonadVM.Evmc.Message.t.gas) ->
  (RocqOfOCaml.OCamlZ.of_int64_unsigned
    (@MonadVM.Precompiles.Bls12_381.g2_msm
      UZ U64 UCount UU256Repr UU256 UInteger UGas UIntegerBase UFp
      UAddress UBytes UUnit UInt UAscii UC2 UC1 UB64
      UCurve2Bytes UFp2Fallback msg).(MonadVM.Evmc.Result.t.gas_left)
    <= RocqOfOCaml.OCamlZ.of_int64_unsigned
      msg.(MonadVM.Evmc.Message.t.gas))%Z.
Proof.
  intro Hvalid.
  unfold MonadVM.Precompiles.Bls12_381.g2_msm.
  eapply (@precompile_run_gas_safe_bounded UAddress UUnit UInt).
  - exact Hvalid.
  - cbn zeta.
    eapply precompile_bind_gas_safe.
    + apply precompile_ensure_gas_safe.
    + intro ignored_length.
      eapply precompile_bind_gas_safe.
      * apply precompile_ensure_gas_safe.
      * intro ignored_count.
        eapply precompile_bind_gas_safe.
        -- apply precompile_spend_gas_safe.
        -- intro ignored_spend.
           eapply precompile_bind_gas_safe.
           ++ apply precompile_list_value_gas_safe.
              apply precompile_pair_value_gas_safe.
              ** apply ec_extension_subgroup_point_gas_safe.
                 unfold supported_complex_encoding,
                   complex_encoding_tag.
                 cbn. left. reflexivity.
              ** unfold MonadVM.Precompiles.Utils.Precompile.u256.
                 apply precompile_numeric_reader_gas_safe.
           ++ intro points. apply precompile_return_gas_safe.
Qed.

Context `{UArrayFp : RocqOfOCaml.Basics.Unreachable
  (RocqOfOCaml.OCamlIarray.t
    (MonadVM.Ec.Bls12_381.F_p.t
      (_rocq_assumption_0 := UZ)
      (_rocq_assumption_1 := UCount)
      (_rocq_assumption_2 := UIntegerBase)))}.
Context `{UBool : RocqOfOCaml.Basics.Unreachable bool}.
Context `{UArrayFpPair : RocqOfOCaml.Basics.Unreachable
  ((RocqOfOCaml.OCamlIarray.t
    (MonadVM.Ec.Bls12_381.F_p.t
      (_rocq_assumption_0 := UZ)
      (_rocq_assumption_1 := UCount)
      (_rocq_assumption_2 := UIntegerBase)))
   * (RocqOfOCaml.OCamlIarray.t
    (MonadVM.Ec.Bls12_381.F_p.t
      (_rocq_assumption_0 := UZ)
      (_rocq_assumption_1 := UCount)
      (_rocq_assumption_2 := UIntegerBase))))}.

Local Definition Fp12Type : Set :=
  MonadVM.Ec.Bls12_381.F_p12.t
    (_rocq_assumption_0 := UZ)
    (_rocq_assumption_1 := UCount)
    (_rocq_assumption_2 := UIntegerBase)
    (_rocq_assumption_3 := UArrayFp)
    (_rocq_assumption_4 := UInteger)
    (_rocq_assumption_5 := UFp)
    (_rocq_assumption_6 := UBool)
    (_rocq_assumption_7 := UArrayFpPair).

Context `{USeqFp12 : RocqOfOCaml.Basics.Unreachable
  (RocqOfOCaml.OCamlSeq.t Fp12Type)}.
Context `{UPairFp12 : RocqOfOCaml.Basics.Unreachable
  (Fp12Type * Fp12Type)}.
Context `{UPairInt : RocqOfOCaml.Basics.Unreachable (int * int)}.
Context `{USeqEndo : RocqOfOCaml.Basics.Unreachable
  (RocqOfOCaml.OCamlSeq.t Fp12Type ->
    RocqOfOCaml.OCamlSeq.t Fp12Type)}.

Local Definition UnderlyingRingType : Set :=
  (MonadVM.Ec.Bls12_381.F_p12.MonadVM_Ec_Algebra_Polynomial_extension_include
    (_rocq_module_assumption_0 := UZ)
    (_rocq_module_assumption_1 := UCount)
    (_rocq_module_assumption_2 := UIntegerBase)
    (_rocq_module_assumption_3 := UArrayFp)
    (_rocq_module_assumption_4 := UInteger)
    (_rocq_module_assumption_5 := UFp)
    (_rocq_module_assumption_6 := UBool)
    (_rocq_module_assumption_7 := UArrayFpPair))
      .(MonadVM.Ec.Algebra.Polynomial_extension.Polynomial_extension_result.Underlying_ring)
      .(MonadVM.Ec.Algebra.Polynomial_ring.Polynomial_ring_result.t).

Context `{URing : RocqOfOCaml.Basics.Unreachable UnderlyingRingType}.
Context `{UString : RocqOfOCaml.Basics.Unreachable string}.

Lemma generated_bls12381_pairing_precompile_gas_bounded
    (msg : MonadVM.Evmc.Message.t) :
  valid_int64_repr msg.(MonadVM.Evmc.Message.t.gas) ->
  (RocqOfOCaml.OCamlZ.of_int64_unsigned
    (@MonadVM.Precompiles.Bls12_381.pairing_check
      UZ UCount UIntegerBase UArrayFp UInteger UFp UBool UArrayFpPair
      USeqFp12
      U64 UU256 UGas UAddress UUnit UString UInt UAscii
      UPairFp12 UPairInt USeqEndo URing UC2 UC1 UB64 UFp2Fallback
      msg).(MonadVM.Evmc.Result.t.gas_left)
    <= RocqOfOCaml.OCamlZ.of_int64_unsigned
      msg.(MonadVM.Evmc.Message.t.gas))%Z.
Proof.
  intro Hvalid.
  unfold MonadVM.Precompiles.Bls12_381.pairing_check.
  eapply (@precompile_run_gas_safe_bounded UAddress UUnit UInt).
  - exact Hvalid.
  - cbn zeta.
    eapply precompile_bind_gas_safe.
    + apply precompile_ensure_gas_safe.
    + intro ignored_length.
      eapply precompile_bind_gas_safe.
      * apply precompile_ensure_gas_safe.
      * intro ignored_count.
        eapply precompile_bind_gas_safe.
        -- apply precompile_spend_gas_safe.
        -- intro ignored_spend.
           eapply precompile_bind_gas_safe.
           ++ apply precompile_list_value_gas_safe.
              apply precompile_pair_value_gas_safe.
              ** apply ec_subgroup_point_gas_safe.
              ** apply ec_extension_subgroup_point_gas_safe.
                 unfold supported_complex_encoding,
                   complex_encoding_tag.
                 cbn. left. reflexivity.
           ++ intro pairs. apply precompile_return_gas_safe.
Qed.

Context `{UG1Point : RocqOfOCaml.Basics.Unreachable
  (MonadVM.Ec.Bls12_381.G_1
    (_rocq_module_assumption_0 := UZ)
    (_rocq_module_assumption_1 := UCount)
    (_rocq_module_assumption_2 := UInteger)
    (_rocq_module_assumption_3 := UIntegerBase)
    (_rocq_module_assumption_4 := UFp)
    (_rocq_module_assumption_5 := UC1)).(MonadVM.Ec.Curve.Make.Subgroup.Subgroup_result.t)}.
Context `{USWUCurve : RocqOfOCaml.Basics.Unreachable
  (MonadVM.Ec.Bls12_381.F_p_SWU_curve.t
    (_rocq_assumption_0 := UZ)
    (_rocq_assumption_1 := UCount)
    (_rocq_assumption_2 := UInteger)
    (_rocq_assumption_3 := UIntegerBase)
    (_rocq_assumption_4 := UFp))}.
Context `{UOptionFp : RocqOfOCaml.Basics.Unreachable
  (option (MonadVM.Ec.Bls12_381.F_p.t
    (_rocq_assumption_0 := UZ)
    (_rocq_assumption_1 := UCount)
    (_rocq_assumption_2 := UIntegerBase)))}.
Context `{UFpOption : RocqOfOCaml.Basics.Unreachable
  ((MonadVM.Ec.Bls12_381.F_p.t
    (_rocq_assumption_0 := UZ)
    (_rocq_assumption_1 := UCount)
    (_rocq_assumption_2 := UIntegerBase)) ->
    option (MonadVM.Ec.Bls12_381.F_p.t
      (_rocq_assumption_0 := UZ)
      (_rocq_assumption_1 := UCount)
      (_rocq_assumption_2 := UIntegerBase)))}.
Context `{USWUField : RocqOfOCaml.Basics.Unreachable
  (MonadVM.Ec.Bls12_381.F_p_SWU
    (_rocq_module_assumption_0 := UZ)
    (_rocq_module_assumption_1 := UCount)
    (_rocq_module_assumption_2 := UInteger)
    (_rocq_module_assumption_3 := UIntegerBase)
    (_rocq_module_assumption_4 := UFp)
    (_rocq_module_assumption_5 := UOptionFp)
    (_rocq_module_assumption_6 := UFpOption)).(MonadVM.Ec.Curve.SWU_method.SWU_method_result.F).(MonadVM.Ec.Algebra.FIELD.t)}.

Lemma generated_bls12381_map_fp_to_g1_gas_bounded
    (msg : MonadVM.Evmc.Message.t) :
  valid_int64_repr msg.(MonadVM.Evmc.Message.t.gas) ->
  (RocqOfOCaml.OCamlZ.of_int64_unsigned
    (@MonadVM.Precompiles.Bls12_381.map_fp_to_g1
      UZ UCount UIntegerBase UArrayFp U64 UInteger UGas UFp
      UC1 UG1Point USWUCurve UAddress UBytes UUnit UOptionFp
      UInt UAscii UFpOption USWUField UC2 UB64
      msg).(MonadVM.Evmc.Result.t.gas_left)
    <= RocqOfOCaml.OCamlZ.of_int64_unsigned
      msg.(MonadVM.Evmc.Message.t.gas))%Z.
Proof.
  intro Hvalid.
  unfold MonadVM.Precompiles.Bls12_381.map_fp_to_g1.
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
        -- apply ec_field_element_gas_safe.
        -- intro field_element. apply precompile_return_gas_safe.
Qed.

Context `{UArrayFp2 : RocqOfOCaml.Basics.Unreachable
  (RocqOfOCaml.OCamlIarray.t
    (MonadVM.Ec.Bls12_381.F_p2.t
      (_rocq_assumption_0 := UZ)
      (_rocq_assumption_1 := UCount)
      (_rocq_assumption_2 := UInteger)
      (_rocq_assumption_3 := UIntegerBase)
      (_rocq_assumption_4 := UFp)))}.
Context `{UG2Point : RocqOfOCaml.Basics.Unreachable
  (MonadVM.Ec.Bls12_381.G_2
    (_rocq_module_assumption_0 := UZ)
    (_rocq_module_assumption_1 := UCount)
    (_rocq_module_assumption_2 := UInteger)
    (_rocq_module_assumption_3 := UIntegerBase)
    (_rocq_module_assumption_4 := UFp)
    (_rocq_module_assumption_5 := UC2)).(MonadVM.Ec.Curve.Make.Subgroup.Subgroup_result.t)}.
Context `{USWUCurve2 : RocqOfOCaml.Basics.Unreachable
  (MonadVM.Ec.Bls12_381.F_p2_SWU_curve.t
    (_rocq_assumption_0 := UZ)
    (_rocq_assumption_1 := UCount)
    (_rocq_assumption_2 := UInteger)
    (_rocq_assumption_3 := UIntegerBase)
    (_rocq_assumption_4 := UFp))}.
Context `{UFp2 : RocqOfOCaml.Basics.Unreachable
  (MonadVM.Ec.Bls12_381.F_p2.t
    (_rocq_assumption_0 := UZ)
    (_rocq_assumption_1 := UCount)
    (_rocq_assumption_2 := UInteger)
    (_rocq_assumption_3 := UIntegerBase)
    (_rocq_assumption_4 := UFp))}.
Context `{USWUField2 : RocqOfOCaml.Basics.Unreachable
  (MonadVM.Ec.Bls12_381.F_p2_SWU
    (_rocq_module_assumption_0 := UZ)
    (_rocq_module_assumption_1 := UCount)
    (_rocq_module_assumption_2 := UInteger)
    (_rocq_module_assumption_3 := UIntegerBase)
    (_rocq_module_assumption_4 := UFp)
    (_rocq_module_assumption_5 := UOptionFp)
    (_rocq_module_assumption_6 := UFpOption)).(MonadVM.Ec.Curve.SWU_method.SWU_method_result.F).(MonadVM.Ec.Algebra.FIELD.t)}.

Lemma generated_bls12381_map_fp2_to_g2_gas_bounded
    (msg : MonadVM.Evmc.Message.t) :
  valid_int64_repr msg.(MonadVM.Evmc.Message.t.gas) ->
  (RocqOfOCaml.OCamlZ.of_int64_unsigned
    (@MonadVM.Precompiles.Bls12_381.map_fp2_to_g2
      UZ UCount UInteger UIntegerBase UFp UArrayFp2 U64 UGas
      UC2 UG2Point USWUCurve2 UFp2 UAddress UBytes UUnit UOptionFp
      UInt UAscii UFpOption USWUField2 UC1 UB64 UCurve2Bytes
      UFp2Fallback msg).(MonadVM.Evmc.Result.t.gas_left)
    <= RocqOfOCaml.OCamlZ.of_int64_unsigned
      msg.(MonadVM.Evmc.Message.t.gas))%Z.
Proof.
  intro Hvalid.
  unfold MonadVM.Precompiles.Bls12_381.map_fp2_to_g2.
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
        -- apply ec_extension_field_gas_safe.
           unfold supported_complex_encoding, complex_encoding_tag.
           cbn. left. reflexivity.
        -- intro field_element. apply precompile_return_gas_safe.
Qed.
End Bls12381G1.
