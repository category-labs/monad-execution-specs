(** Gas bounds for the concrete generated precompile address table. *)

From Stdlib Require Import List ZArith.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import MonadExecutionSpecs.Termination.VmPrecompileTableGasBound.
Require Import MonadExecutionSpecs.Termination.VmPrecompileGasBound.
Require Import MonadExecutionSpecs.Termination.VmEcrecoverGasBound.
Require Import MonadExecutionSpecs.Termination.VmBlake2fGasBound.
Require Import MonadExecutionSpecs.Termination.VmModexpGasBound.
Require Import MonadExecutionSpecs.Termination.VmSecp256r1GasBound.
Require Import MonadExecutionSpecs.Termination.VmAltBn128GasBound.
Require Import MonadExecutionSpecs.Termination.VmBls12381GasBound.
Require Import MonadExecutionSpecs.Termination.VmPointEvaluationGasBound.
Require Import MonadVM.Precompiles.
Require MonadVM.Chain.Monad.
Require MonadVM.Chain.Ethereum.
Require MonadVM.Support.Variants.

Local Open Scope Z_scope.

Section ConcreteTable.
Context `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable Z.t}.
Context `{_rocq_assumption_1 : RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}.
Context `{_rocq_assumption_2 : RocqOfOCaml.Basics.Unreachable
      MonadVM.Numeric.IntegerBase.(MonadVM.Numeric.Make.Make_result.t)}.
Context `{_rocq_assumption_3 : RocqOfOCaml.Basics.Unreachable
      (RocqOfOCaml.OCamlIarray.t
        (MonadVM.Ec.Bls12_381.F_p.t
        (_rocq_assumption_0 := _rocq_assumption_0)
        (_rocq_assumption_1 := _rocq_assumption_1)
        (_rocq_assumption_2 := _rocq_assumption_2)))}.
Context `{_rocq_assumption_4 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.Integer.t}.
Context `{_rocq_assumption_5 : RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Bls12_381.F_p.t
        (_rocq_assumption_0 := _rocq_assumption_0)
        (_rocq_assumption_1 := _rocq_assumption_1)
        (_rocq_assumption_2 := _rocq_assumption_2))}.
Context `{_rocq_assumption_6 : RocqOfOCaml.Basics.Unreachable bool}.
Context `{UBlsFpPair : RocqOfOCaml.Basics.Unreachable
      ((RocqOfOCaml.OCamlIarray.t
        (MonadVM.Ec.Bls12_381.F_p.t
          (_rocq_assumption_0 := _rocq_assumption_0)
          (_rocq_assumption_1 := _rocq_assumption_1)
          (_rocq_assumption_2 := _rocq_assumption_2)))
       * (RocqOfOCaml.OCamlIarray.t
        (MonadVM.Ec.Bls12_381.F_p.t
          (_rocq_assumption_0 := _rocq_assumption_0)
          (_rocq_assumption_1 := _rocq_assumption_1)
          (_rocq_assumption_2 := _rocq_assumption_2))))}.
Context `{_rocq_assumption_7 : RocqOfOCaml.Basics.Unreachable
      (RocqOfOCaml.OCamlSeq.t
        (MonadVM.Ec.Bls12_381.F_p12.t
        (_rocq_assumption_0 := _rocq_assumption_0)
        (_rocq_assumption_1 := _rocq_assumption_1)
        (_rocq_assumption_2 := _rocq_assumption_2)
        (_rocq_assumption_3 := _rocq_assumption_3)
        (_rocq_assumption_4 := _rocq_assumption_4)
        (_rocq_assumption_5 := _rocq_assumption_5)
        (_rocq_assumption_6 := _rocq_assumption_6)
        (_rocq_assumption_7 := UBlsFpPair)))}.
Context `{_rocq_assumption_8 : RocqOfOCaml.Basics.Unreachable
      (RocqOfOCaml.OCamlIarray.t
        (MonadVM.Ec.Alt_bn128.F_p
        (_rocq_module_assumption_0 := _rocq_assumption_0)
        (_rocq_module_assumption_1 := _rocq_assumption_1)
        (_rocq_module_assumption_2 := _rocq_assumption_2)).(MonadVM.Ec.Algebra.Prime_field.Prime_field_result.t))}.
Context `{_rocq_assumption_9 : RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Alt_bn128.F_p
        (_rocq_module_assumption_0 := _rocq_assumption_0)
        (_rocq_module_assumption_1 := _rocq_assumption_1)
        (_rocq_module_assumption_2 := _rocq_assumption_2)).(MonadVM.Ec.Algebra.Prime_field.Prime_field_result.t)}.
Context `{UAltFpPair : RocqOfOCaml.Basics.Unreachable
      ((RocqOfOCaml.OCamlIarray.t
        (MonadVM.Ec.Alt_bn128.F_p
          (_rocq_module_assumption_0 := _rocq_assumption_0)
          (_rocq_module_assumption_1 := _rocq_assumption_1)
          (_rocq_module_assumption_2 := _rocq_assumption_2)).(MonadVM.Ec.Algebra.Prime_field.Prime_field_result.t))
       * (RocqOfOCaml.OCamlIarray.t
        (MonadVM.Ec.Alt_bn128.F_p
          (_rocq_module_assumption_0 := _rocq_assumption_0)
          (_rocq_module_assumption_1 := _rocq_assumption_1)
          (_rocq_module_assumption_2 := _rocq_assumption_2)).(MonadVM.Ec.Algebra.Prime_field.Prime_field_result.t)))}.
Context `{_rocq_assumption_10 : RocqOfOCaml.Basics.Unreachable
      (RocqOfOCaml.OCamlSeq.t
        (MonadVM.Ec.Alt_bn128.F_p12.t
        (_rocq_assumption_0 := _rocq_assumption_0)
        (_rocq_assumption_1 := _rocq_assumption_1)
        (_rocq_assumption_2 := _rocq_assumption_4)
        (_rocq_assumption_3 := _rocq_assumption_6)
        (_rocq_assumption_4 := _rocq_assumption_2)
        (_rocq_assumption_5 := _rocq_assumption_8)
        (_rocq_assumption_6 := _rocq_assumption_9)
        (_rocq_assumption_7 := UAltFpPair)))}.
Context `{_rocq_assumption_11 : RocqOfOCaml.Basics.Unreachable
      (RocqOfOCaml.OCamlIarray.t
        (MonadVM.Ec.Bls12_381.F_p2.t
        (_rocq_assumption_0 := _rocq_assumption_0)
        (_rocq_assumption_1 := _rocq_assumption_1)
        (_rocq_assumption_2 := _rocq_assumption_4)
        (_rocq_assumption_3 := _rocq_assumption_2)
        (_rocq_assumption_4 := _rocq_assumption_5)))}.
Context `{_rocq_assumption_12 : RocqOfOCaml.Basics.Unreachable (RocqOfOCaml.OCamlIarray.t int)}.
Context `{_rocq_assumption_13 : RocqOfOCaml.Basics.Unreachable MonadVM.Uint64.t}.
Context `{_rocq_assumption_14 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U8.Repr.t}.
Context `{_rocq_assumption_15 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U8.t}.
Context `{_rocq_assumption_16 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U64.Repr.t}.
Context `{_rocq_assumption_17 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U64.t}.
Context `{_rocq_assumption_18 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U32.Repr.t}.
Context `{_rocq_assumption_19 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U32.t}.
Context `{_rocq_assumption_20 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.Repr.t}.
Context `{_rocq_assumption_21 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
Context `{_rocq_assumption_22 : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
Context `{_rocq_assumption_23 : RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Bls12_381.C_2
        (_rocq_module_assumption_0 := _rocq_assumption_0)
        (_rocq_module_assumption_1 := _rocq_assumption_1)
        (_rocq_module_assumption_2 := _rocq_assumption_4)
        (_rocq_module_assumption_3 := _rocq_assumption_2)
        (_rocq_module_assumption_4 := _rocq_assumption_5)).(MonadVM.Ec.Curve.Make.Make_result.t)}.
Context `{_rocq_assumption_24 : RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Bls12_381.G_2
        (_rocq_module_assumption_0 := _rocq_assumption_0)
        (_rocq_module_assumption_1 := _rocq_assumption_1)
        (_rocq_module_assumption_2 := _rocq_assumption_4)
        (_rocq_module_assumption_3 := _rocq_assumption_2)
        (_rocq_module_assumption_4 := _rocq_assumption_5)
        (_rocq_module_assumption_5 := _rocq_assumption_23)).(MonadVM.Ec.Curve.Make.Subgroup.Subgroup_result.t)}.
Context `{_rocq_assumption_25 : RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Bls12_381.C_1
        (_rocq_module_assumption_0 := _rocq_assumption_0)
        (_rocq_module_assumption_1 := _rocq_assumption_1)
        (_rocq_module_assumption_2 := _rocq_assumption_4)
        (_rocq_module_assumption_3 := _rocq_assumption_2)
        (_rocq_module_assumption_4 := _rocq_assumption_5)).(MonadVM.Ec.Curve.Make.Make_result.t)}.
Context `{_rocq_assumption_26 : RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Bls12_381.G_1
        (_rocq_module_assumption_0 := _rocq_assumption_0)
        (_rocq_module_assumption_1 := _rocq_assumption_1)
        (_rocq_module_assumption_2 := _rocq_assumption_4)
        (_rocq_module_assumption_3 := _rocq_assumption_2)
        (_rocq_module_assumption_4 := _rocq_assumption_5)
        (_rocq_module_assumption_5 := _rocq_assumption_25)).(MonadVM.Ec.Curve.Make.Subgroup.Subgroup_result.t)}.
Context `{_rocq_assumption_27 : RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Bls12_381.F_p_SWU_curve.t
        (_rocq_assumption_0 := _rocq_assumption_0)
        (_rocq_assumption_1 := _rocq_assumption_1)
        (_rocq_assumption_2 := _rocq_assumption_4)
        (_rocq_assumption_3 := _rocq_assumption_2)
        (_rocq_assumption_4 := _rocq_assumption_5))}.
Context `{_rocq_assumption_28 : RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Bls12_381.F_p2_SWU_curve.t
        (_rocq_assumption_0 := _rocq_assumption_0)
        (_rocq_assumption_1 := _rocq_assumption_1)
        (_rocq_assumption_2 := _rocq_assumption_4)
        (_rocq_assumption_3 := _rocq_assumption_2)
        (_rocq_assumption_4 := _rocq_assumption_5))}.
Context `{_rocq_assumption_29 : RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Bls12_381.F_p2.t
        (_rocq_assumption_0 := _rocq_assumption_0)
        (_rocq_assumption_1 := _rocq_assumption_1)
        (_rocq_assumption_2 := _rocq_assumption_4)
        (_rocq_assumption_3 := _rocq_assumption_2)
        (_rocq_assumption_4 := _rocq_assumption_5))}.
Context `{_rocq_assumption_30 : RocqOfOCaml.Basics.Unreachable MonadVM.Chain.Ethereum.Address.t}.
Context `{_rocq_assumption_31 : RocqOfOCaml.Basics.Unreachable MonadVM.Byte_string.Bytes.t}.
Context `{_rocq_assumption_32 : RocqOfOCaml.Basics.Unreachable MonadVM.Byte_string.B20.t}.
Context `{_rocq_assumption_33 : RocqOfOCaml.Basics.Unreachable unit}.
Context `{_rocq_assumption_34 : RocqOfOCaml.Basics.Unreachable string}.
Context `{_rocq_assumption_35 : RocqOfOCaml.Basics.Unreachable
      (option
        (MonadVM.Ec.Bls12_381.F_p.t
        (_rocq_assumption_0 := _rocq_assumption_0)
        (_rocq_assumption_1 := _rocq_assumption_1)
        (_rocq_assumption_2 := _rocq_assumption_2)))}.
Context `{_rocq_assumption_36 : RocqOfOCaml.Basics.Unreachable int}.
Context `{_rocq_assumption_37 : RocqOfOCaml.Basics.Unreachable ascii}.
Context `{_rocq_assumption_38 : RocqOfOCaml.Basics.Unreachable
      ((MonadVM.Ec.Bls12_381.F_p12.t
        (_rocq_assumption_0 := _rocq_assumption_0)
        (_rocq_assumption_1 := _rocq_assumption_1)
        (_rocq_assumption_2 := _rocq_assumption_2)
        (_rocq_assumption_3 := _rocq_assumption_3)
        (_rocq_assumption_4 := _rocq_assumption_4)
        (_rocq_assumption_5 := _rocq_assumption_5)
        (_rocq_assumption_6 := _rocq_assumption_6)
        (_rocq_assumption_7 := UBlsFpPair))
        *
        (MonadVM.Ec.Bls12_381.F_p12.t
        (_rocq_assumption_0 := _rocq_assumption_0)
        (_rocq_assumption_1 := _rocq_assumption_1)
        (_rocq_assumption_2 := _rocq_assumption_2)
        (_rocq_assumption_3 := _rocq_assumption_3)
        (_rocq_assumption_4 := _rocq_assumption_4)
        (_rocq_assumption_5 := _rocq_assumption_5)
        (_rocq_assumption_6 := _rocq_assumption_6)
        (_rocq_assumption_7 := UBlsFpPair)))}.
Context `{_rocq_assumption_39 : RocqOfOCaml.Basics.Unreachable
      ((MonadVM.Ec.Alt_bn128.F_p12.t
        (_rocq_assumption_0 := _rocq_assumption_0)
        (_rocq_assumption_1 := _rocq_assumption_1)
        (_rocq_assumption_2 := _rocq_assumption_4)
        (_rocq_assumption_3 := _rocq_assumption_6)
        (_rocq_assumption_4 := _rocq_assumption_2)
        (_rocq_assumption_5 := _rocq_assumption_8)
        (_rocq_assumption_6 := _rocq_assumption_9)
        (_rocq_assumption_7 := UAltFpPair))
        *
        (MonadVM.Ec.Alt_bn128.F_p12.t
        (_rocq_assumption_0 := _rocq_assumption_0)
        (_rocq_assumption_1 := _rocq_assumption_1)
        (_rocq_assumption_2 := _rocq_assumption_4)
        (_rocq_assumption_3 := _rocq_assumption_6)
        (_rocq_assumption_4 := _rocq_assumption_2)
        (_rocq_assumption_5 := _rocq_assumption_8)
        (_rocq_assumption_6 := _rocq_assumption_9)
        (_rocq_assumption_7 := UAltFpPair)))}.
Context `{_rocq_assumption_40 : RocqOfOCaml.Basics.Unreachable (int * int)}.
Context `{_rocq_assumption_41 : RocqOfOCaml.Basics.Unreachable
      (RocqOfOCaml.OCamlSeq.t
        (MonadVM.Ec.Bls12_381.F_p12.t
        (_rocq_assumption_0 := _rocq_assumption_0)
        (_rocq_assumption_1 := _rocq_assumption_1)
        (_rocq_assumption_2 := _rocq_assumption_2)
        (_rocq_assumption_3 := _rocq_assumption_3)
        (_rocq_assumption_4 := _rocq_assumption_4)
        (_rocq_assumption_5 := _rocq_assumption_5)
        (_rocq_assumption_6 := _rocq_assumption_6)
        (_rocq_assumption_7 := UBlsFpPair))
      ->
      RocqOfOCaml.OCamlSeq.t
        (MonadVM.Ec.Bls12_381.F_p12.t
        (_rocq_assumption_0 := _rocq_assumption_0)
        (_rocq_assumption_1 := _rocq_assumption_1)
        (_rocq_assumption_2 := _rocq_assumption_2)
        (_rocq_assumption_3 := _rocq_assumption_3)
        (_rocq_assumption_4 := _rocq_assumption_4)
        (_rocq_assumption_5 := _rocq_assumption_5)
        (_rocq_assumption_6 := _rocq_assumption_6)
        (_rocq_assumption_7 := UBlsFpPair)))}.
Context `{_rocq_assumption_42 : RocqOfOCaml.Basics.Unreachable
      (RocqOfOCaml.OCamlSeq.t
        (MonadVM.Ec.Alt_bn128.F_p12.t
        (_rocq_assumption_0 := _rocq_assumption_0)
        (_rocq_assumption_1 := _rocq_assumption_1)
        (_rocq_assumption_2 := _rocq_assumption_4)
        (_rocq_assumption_3 := _rocq_assumption_6)
        (_rocq_assumption_4 := _rocq_assumption_2)
        (_rocq_assumption_5 := _rocq_assumption_8)
        (_rocq_assumption_6 := _rocq_assumption_9)
        (_rocq_assumption_7 := UAltFpPair))
      ->
      RocqOfOCaml.OCamlSeq.t
        (MonadVM.Ec.Alt_bn128.F_p12.t
        (_rocq_assumption_0 := _rocq_assumption_0)
        (_rocq_assumption_1 := _rocq_assumption_1)
        (_rocq_assumption_2 := _rocq_assumption_4)
        (_rocq_assumption_3 := _rocq_assumption_6)
        (_rocq_assumption_4 := _rocq_assumption_2)
        (_rocq_assumption_5 := _rocq_assumption_8)
        (_rocq_assumption_6 := _rocq_assumption_9)
        (_rocq_assumption_7 := UAltFpPair)))}.
Context `{_rocq_assumption_43 : RocqOfOCaml.Basics.Unreachable
      (MonadVM.Support.UintN.Impl.t -> MonadVM.Support.UintN.Impl.t ->
      MonadVM.Support.UintN.Impl.t)}.
Context `{_rocq_assumption_44 : RocqOfOCaml.Basics.Unreachable
      (MonadVM.Support.UintN.Impl.t -> MonadVM.Support.UintN.Impl.t ->
      MonadVM.Support.UintN.t)}.
Context `{_rocq_assumption_45 : RocqOfOCaml.Basics.Unreachable
      (MonadVM.Support.UintN.Impl.t -> MonadVM.Support.UintN.Impl.t ->
      MonadVM.Support.UintN.Impl.t -> MonadVM.Support.UintN.Impl.t ->
      MonadVM.Support.UintN.Impl.t)}.
Context `{_rocq_assumption_46 : RocqOfOCaml.Basics.Unreachable
      ((MonadVM.Ec.Bls12_381.F_p.t
        (_rocq_assumption_0 := _rocq_assumption_0)
        (_rocq_assumption_1 := _rocq_assumption_1)
        (_rocq_assumption_2 := _rocq_assumption_2))
      ->
      option
        (MonadVM.Ec.Bls12_381.F_p.t
        (_rocq_assumption_0 := _rocq_assumption_0)
        (_rocq_assumption_1 := _rocq_assumption_1)
        (_rocq_assumption_2 := _rocq_assumption_2)))}.
Context `{_rocq_assumption_47 : RocqOfOCaml.Basics.Unreachable
      (RocqOfOCaml.OCamlIarray.t
        (MonadVM.Ec.Alt_bn128.F_p12.MonadVM_Ec_Algebra_Polynomial_extension_include_fargs
        (_rocq_module_assumption_0 := _rocq_assumption_0)
        (_rocq_module_assumption_1 := _rocq_assumption_1)
        (_rocq_module_assumption_2 := _rocq_assumption_4)
        (_rocq_module_assumption_3 := _rocq_assumption_6)
        (_rocq_module_assumption_4 := _rocq_assumption_2)
        (_rocq_module_assumption_5 := _rocq_assumption_8)
        (_rocq_module_assumption_6 := _rocq_assumption_9)
        (_rocq_module_assumption_7 := UAltFpPair)).(MonadVM.Ec.Algebra.Polynomial_extension.F).(MonadVM.Ec.Algebra.FIELD.t))}.
Context `{_rocq_assumption_48 : RocqOfOCaml.Basics.Unreachable int64}.
Context `{_rocq_assumption_49 : RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Secp256r1.F_p
        (_rocq_module_assumption_0 := _rocq_assumption_0)
        (_rocq_module_assumption_1 := _rocq_assumption_1)
        (_rocq_module_assumption_2 := _rocq_assumption_2)).(MonadVM.Ec.Algebra.Prime_field.Prime_field_result.t)}.
Context `{_rocq_assumption_50 : RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Secp256r1.C_1
        (_rocq_module_assumption_0 := _rocq_assumption_0)
        (_rocq_module_assumption_1 := _rocq_assumption_1)
        (_rocq_module_assumption_2 := _rocq_assumption_4)
        (_rocq_module_assumption_3 := _rocq_assumption_2)
        (_rocq_module_assumption_4 := _rocq_assumption_49)).(MonadVM.Ec.Curve.Make.Make_result.t)}.
Context `{_rocq_assumption_51 : RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Secp256r1.G_1
        (_rocq_module_assumption_0 := _rocq_assumption_0)
        (_rocq_module_assumption_1 := _rocq_assumption_1)
        (_rocq_module_assumption_2 := _rocq_assumption_4)
        (_rocq_module_assumption_3 := _rocq_assumption_2)
        (_rocq_module_assumption_4 := _rocq_assumption_49)
        (_rocq_module_assumption_5 := _rocq_assumption_50)).(MonadVM.Ec.Curve.Make.Subgroup.Subgroup_result.curve)}.
Context `{_rocq_assumption_52 : RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Secp256r1.F_q
        (_rocq_module_assumption_0 := _rocq_assumption_0)
        (_rocq_module_assumption_1 := _rocq_assumption_1)
        (_rocq_module_assumption_2 := _rocq_assumption_2)).(MonadVM.Ec.Algebra.Prime_field.Prime_field_result.t)}.
Context `{_rocq_assumption_53 : RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Bls12_381.F_p12.MonadVM_Ec_Algebra_Polynomial_extension_include
        (_rocq_module_assumption_0 := _rocq_assumption_0)
        (_rocq_module_assumption_1 := _rocq_assumption_1)
        (_rocq_module_assumption_2 := _rocq_assumption_2)
        (_rocq_module_assumption_3 := _rocq_assumption_3)
        (_rocq_module_assumption_4 := _rocq_assumption_4)
        (_rocq_module_assumption_5 := _rocq_assumption_5)
        (_rocq_module_assumption_6 := _rocq_assumption_6)
        (_rocq_module_assumption_7 := UBlsFpPair)).(MonadVM.Ec.Algebra.Polynomial_extension.Polynomial_extension_result.Underlying_ring).(MonadVM.Ec.Algebra.Polynomial_ring.Polynomial_ring_result.t)}.
Context `{_rocq_assumption_54 : RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Bls12_381.G_2
        (_rocq_module_assumption_0 := _rocq_assumption_0)
        (_rocq_module_assumption_1 := _rocq_assumption_1)
        (_rocq_module_assumption_2 := _rocq_assumption_4)
        (_rocq_module_assumption_3 := _rocq_assumption_2)
        (_rocq_module_assumption_4 := _rocq_assumption_5)
        (_rocq_module_assumption_5 := _rocq_assumption_23)).(MonadVM.Ec.Curve.Make.Subgroup.Subgroup_result.curve)}.
Context `{_rocq_assumption_55 : RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Bls12_381.G_1
        (_rocq_module_assumption_0 := _rocq_assumption_0)
        (_rocq_module_assumption_1 := _rocq_assumption_1)
        (_rocq_module_assumption_2 := _rocq_assumption_4)
        (_rocq_module_assumption_3 := _rocq_assumption_2)
        (_rocq_module_assumption_4 := _rocq_assumption_5)
        (_rocq_module_assumption_5 := _rocq_assumption_25)).(MonadVM.Ec.Curve.Make.Subgroup.Subgroup_result.curve)}.
Context `{_rocq_assumption_56 : RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Bls12_381.F_p_SWU
        (_rocq_module_assumption_0 := _rocq_assumption_0)
        (_rocq_module_assumption_1 := _rocq_assumption_1)
        (_rocq_module_assumption_2 := _rocq_assumption_4)
        (_rocq_module_assumption_3 := _rocq_assumption_2)
        (_rocq_module_assumption_4 := _rocq_assumption_5)
        (_rocq_module_assumption_5 := _rocq_assumption_35)
        (_rocq_module_assumption_6 := _rocq_assumption_46)).(MonadVM.Ec.Curve.SWU_method.SWU_method_result.F).(MonadVM.Ec.Algebra.FIELD.t)}.
Context `{_rocq_assumption_57 : RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Bls12_381.F_p2_SWU
        (_rocq_module_assumption_0 := _rocq_assumption_0)
        (_rocq_module_assumption_1 := _rocq_assumption_1)
        (_rocq_module_assumption_2 := _rocq_assumption_4)
        (_rocq_module_assumption_3 := _rocq_assumption_2)
        (_rocq_module_assumption_4 := _rocq_assumption_5)
        (_rocq_module_assumption_5 := _rocq_assumption_35)
        (_rocq_module_assumption_6 := _rocq_assumption_46)).(MonadVM.Ec.Curve.SWU_method.SWU_method_result.F).(MonadVM.Ec.Algebra.FIELD.t)}.
Context `{_rocq_assumption_58 : RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Alt_bn128.F_p12.MonadVM_Ec_Algebra_Polynomial_extension_include_fargs
        (_rocq_module_assumption_0 := _rocq_assumption_0)
        (_rocq_module_assumption_1 := _rocq_assumption_1)
        (_rocq_module_assumption_2 := _rocq_assumption_4)
        (_rocq_module_assumption_3 := _rocq_assumption_6)
        (_rocq_module_assumption_4 := _rocq_assumption_2)
        (_rocq_module_assumption_5 := _rocq_assumption_8)
        (_rocq_module_assumption_6 := _rocq_assumption_9)
        (_rocq_module_assumption_7 := UAltFpPair)).(MonadVM.Ec.Algebra.Polynomial_extension.F).(MonadVM.Ec.Algebra.FIELD.t)}.
Context `{_rocq_assumption_59 : RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Alt_bn128.F_p12.MonadVM_Ec_Algebra_Polynomial_extension_include
        (_rocq_module_assumption_0 := _rocq_assumption_0)
        (_rocq_module_assumption_1 := _rocq_assumption_1)
        (_rocq_module_assumption_2 := _rocq_assumption_4)
        (_rocq_module_assumption_3 := _rocq_assumption_6)
        (_rocq_module_assumption_4 := _rocq_assumption_2)
        (_rocq_module_assumption_5 := _rocq_assumption_8)
        (_rocq_module_assumption_6 := _rocq_assumption_9)
        (_rocq_module_assumption_7 := UAltFpPair)).(MonadVM.Ec.Algebra.Polynomial_extension.Polynomial_extension_result.Underlying_ring).(MonadVM.Ec.Algebra.Polynomial_ring.Polynomial_ring_result.t)}.
Context `{_rocq_assumption_60 : RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Alt_bn128.C_2
        (_rocq_module_assumption_0 := _rocq_assumption_0)
        (_rocq_module_assumption_1 := _rocq_assumption_1)
        (_rocq_module_assumption_2 := _rocq_assumption_4)
        (_rocq_module_assumption_3 := _rocq_assumption_2)
        (_rocq_module_assumption_4 := _rocq_assumption_9)).(MonadVM.Ec.Curve.Make.Make_result.t)}.
Context `{_rocq_assumption_61 : RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Alt_bn128.C_1
        (_rocq_module_assumption_0 := _rocq_assumption_0)
        (_rocq_module_assumption_1 := _rocq_assumption_1)
        (_rocq_module_assumption_2 := _rocq_assumption_4)
        (_rocq_module_assumption_3 := _rocq_assumption_2)
        (_rocq_module_assumption_4 := _rocq_assumption_9)).(MonadVM.Ec.Curve.Make.Make_result.t)}.
Context `{_rocq_assumption_62 : RocqOfOCaml.Basics.Unreachable
      MonadVM.Byte_string.B64.(MonadVM.Byte_string.Fixed.Fixed_result.t)}.
Context `{_rocq_assumption_63 : RocqOfOCaml.Basics.Unreachable
      MonadVM.Byte_string.B48.(MonadVM.Byte_string.Fixed.Fixed_result.t)}.
Context `{_rocq_assumption_64 : RocqOfOCaml.Basics.Unreachable
      MonadVM.Byte_string.B32.(MonadVM.Byte_string.Fixed.Fixed_result.t)}.
Context `{_rocq_assumption_65 : RocqOfOCaml.Basics.Unreachable
      ((MonadVM.Ec.Bls12_381.C_2
        (_rocq_module_assumption_0 := _rocq_assumption_0)
        (_rocq_module_assumption_1 := _rocq_assumption_1)
        (_rocq_module_assumption_2 := _rocq_assumption_4)
        (_rocq_module_assumption_3 := _rocq_assumption_2)
        (_rocq_module_assumption_4 := _rocq_assumption_5)).(MonadVM.Ec.Curve.Make.Make_result.t)
      -> MonadVM.Byte_string.Bytes.t)}.
Context `{_rocq_assumption_66 : RocqOfOCaml.Basics.Unreachable
      (MonadVM.Evmc.Message.t * int ->
      MonadVM.Precompiles.Utils.Precompile.Inner.t
        (sum MonadVM.Support.UintN.t MonadVM.Evmc.Result.StatusCode.t *
          (MonadVM.Evmc.Message.t * int)))}.
Context `{_rocq_assumption_67 : RocqOfOCaml.Basics.Unreachable
      (MonadVM.Evmc.Message.t * int ->
      MonadVM.Precompiles.Utils.Precompile.Inner.t
        (sum
          (MonadVM.Precompiles.Bls12_381.opened_module_143_fargs
        (_rocq_module_assumption_0 := _rocq_assumption_0)
        (_rocq_module_assumption_1 := _rocq_assumption_1)
        (_rocq_module_assumption_2 := _rocq_assumption_4)
        (_rocq_module_assumption_3 := _rocq_assumption_2)
        (_rocq_module_assumption_4 := _rocq_assumption_5)
        (_rocq_module_assumption_5 := _rocq_assumption_36)
        (_rocq_module_assumption_6 := _rocq_assumption_37)
        (_rocq_module_assumption_7 := _rocq_assumption_23)
        (_rocq_module_assumption_8 := _rocq_assumption_25)
        (_rocq_module_assumption_9 := _rocq_assumption_62)).(MonadVM.Precompiles.Utils.Ec_precompile_utils.M).(MonadVM.Precompiles.Utils.Ec_precompile_utils_M_signature.F_p2_t)
          MonadVM.Evmc.Result.StatusCode.t * (MonadVM.Evmc.Message.t * int)))}.
Context `{_rocq_assumption_68 : RocqOfOCaml.Basics.Unreachable
      (MonadVM.Evmc.Message.t * int ->
      MonadVM.Precompiles.Utils.Precompile.Inner.t
        (sum
          (MonadVM.Precompiles.Alt_bn128.opened_module_165_fargs
        (_rocq_module_assumption_0 := _rocq_assumption_0)
        (_rocq_module_assumption_1 := _rocq_assumption_1)
        (_rocq_module_assumption_2 := _rocq_assumption_4)
        (_rocq_module_assumption_3 := _rocq_assumption_36)
        (_rocq_module_assumption_4 := _rocq_assumption_37)
        (_rocq_module_assumption_5 := _rocq_assumption_2)
        (_rocq_module_assumption_6 := _rocq_assumption_9)
        (_rocq_module_assumption_7 := _rocq_assumption_60)
        (_rocq_module_assumption_8 := _rocq_assumption_61)
        (_rocq_module_assumption_9 := _rocq_assumption_64)).(MonadVM.Precompiles.Utils.Ec_precompile_utils.M).(MonadVM.Precompiles.Utils.Ec_precompile_utils_M_signature.F_p2_t)
          MonadVM.Evmc.Result.StatusCode.t * (MonadVM.Evmc.Message.t * int)))}.

Lemma generated_precompile_table_entry_gas_bounded
    (revision : MonadVM.Chain.Monad.Revision.active)
    (address : MonadVM.Chain.Ethereum.Address.t)
    (precompile : MonadVM.Precompiles.Utils.ethereum_precompile) :
  (revision = MonadVM.Support.Variants.Revision.Eight \/
   revision = MonadVM.Support.Variants.Revision.Nine) ->
  MonadVM.Chain.Ethereum.Address.Map.find_opt address
    (@MonadVM.Precompiles.Make.ethereum_precompiles
      (MonadVM.Precompiles.Make.Build_FArgs
        {| MonadVM.Precompiles.Make_Revision_signature.revision := revision |})
      _rocq_assumption_0 _rocq_assumption_1 _rocq_assumption_2 _rocq_assumption_3 _rocq_assumption_4
      _rocq_assumption_5 _rocq_assumption_6 UBlsFpPair _rocq_assumption_7 _rocq_assumption_8 _rocq_assumption_9
      UAltFpPair _rocq_assumption_10 _rocq_assumption_11 _rocq_assumption_12 _rocq_assumption_13 _rocq_assumption_14
      _rocq_assumption_15 _rocq_assumption_16 _rocq_assumption_17 _rocq_assumption_18 _rocq_assumption_19
      _rocq_assumption_20 _rocq_assumption_21 _rocq_assumption_22 _rocq_assumption_23 _rocq_assumption_24
      _rocq_assumption_25 _rocq_assumption_26 _rocq_assumption_27 _rocq_assumption_28 _rocq_assumption_29
      _rocq_assumption_30 _rocq_assumption_31 _rocq_assumption_32 _rocq_assumption_33 _rocq_assumption_34
      _rocq_assumption_35 _rocq_assumption_36 _rocq_assumption_37 _rocq_assumption_38 _rocq_assumption_39
      _rocq_assumption_40 _rocq_assumption_41 _rocq_assumption_42 _rocq_assumption_43 _rocq_assumption_44
      _rocq_assumption_45 _rocq_assumption_46 _rocq_assumption_47 _rocq_assumption_48 _rocq_assumption_49
      _rocq_assumption_50 _rocq_assumption_51 _rocq_assumption_52 _rocq_assumption_53 _rocq_assumption_54
      _rocq_assumption_55 _rocq_assumption_56 _rocq_assumption_57 _rocq_assumption_58 _rocq_assumption_59
      _rocq_assumption_60 _rocq_assumption_61 _rocq_assumption_62 _rocq_assumption_63 _rocq_assumption_64
      _rocq_assumption_65 _rocq_assumption_66 _rocq_assumption_67 _rocq_assumption_68) = Some precompile ->
  precompile_result_gas_bounded precompile.
Proof.
  intros Hrevision Hlookup.
  unfold MonadVM.Precompiles.Make.ethereum_precompiles in Hlookup.
  cbn zeta in Hlookup.
  eapply selected_address_precompile_gas_bounded;
    [| exact Hlookup].
  apply Forall_cons;
    [ unfold precompile_result_gas_bounded; intros msg Hvalid;
      apply generated_ecrecover_precompile_gas_bounded; exact Hvalid
    | ].
  apply Forall_cons;
    [ unfold precompile_result_gas_bounded; intros msg Hvalid;
      apply generated_sha256_precompile_gas_bounded; exact Hvalid
    | ].
  apply Forall_cons;
    [ unfold precompile_result_gas_bounded; intros msg Hvalid;
      apply generated_ripemd160_precompile_gas_bounded; exact Hvalid
    | ].
  apply Forall_cons;
    [ unfold precompile_result_gas_bounded; intros msg Hvalid;
      apply generated_identity_precompile_gas_bounded; exact Hvalid
    | ].
  apply Forall_cons;
    [ unfold precompile_result_gas_bounded; intros msg Hvalid;
      eapply generated_modexp_precompile_gas_bounded;
        [exact Hvalid | exact Hrevision]
    | ].
  apply Forall_cons;
    [ unfold precompile_result_gas_bounded; intros msg Hvalid;
      apply generated_alt_bn128_add_precompile_gas_bounded; exact Hvalid
    | ].
  apply Forall_cons;
    [ unfold precompile_result_gas_bounded; intros msg Hvalid;
      apply generated_alt_bn128_mul_precompile_gas_bounded; exact Hvalid
    | ].
  apply Forall_cons;
    [ unfold precompile_result_gas_bounded; intros msg Hvalid;
      apply generated_alt_bn128_pairing_precompile_gas_bounded; exact Hvalid
    | ].
  apply Forall_cons;
    [ unfold precompile_result_gas_bounded; intros msg Hvalid;
      apply generated_blake2f_precompile_gas_bounded; exact Hvalid
    | ].
  apply Forall_cons;
    [ unfold precompile_result_gas_bounded; intros msg Hvalid;
      apply generated_point_evaluation_gas_bounded; exact Hvalid
    | ].
  apply Forall_cons;
    [ unfold precompile_result_gas_bounded; intros msg Hvalid;
      apply generated_bls12381_g1_add_gas_bounded; exact Hvalid
    | ].
  apply Forall_cons;
    [ unfold precompile_result_gas_bounded; intros msg Hvalid;
      apply generated_bls12381_g1_msm_gas_bounded; exact Hvalid
    | ].
  apply Forall_cons;
    [ unfold precompile_result_gas_bounded; intros msg Hvalid;
      apply generated_bls12381_g2_add_gas_bounded; exact Hvalid
    | ].
  apply Forall_cons;
    [ unfold precompile_result_gas_bounded; intros msg Hvalid;
      apply generated_bls12381_g2_msm_gas_bounded; exact Hvalid
    | ].
  apply Forall_cons;
    [ unfold precompile_result_gas_bounded; intros msg Hvalid;
      apply generated_bls12381_pairing_precompile_gas_bounded; exact Hvalid
    | ].
  apply Forall_cons;
    [ unfold precompile_result_gas_bounded; intros msg Hvalid;
      apply generated_bls12381_map_fp_to_g1_gas_bounded; exact Hvalid
    | ].
  apply Forall_cons;
    [ unfold precompile_result_gas_bounded; intros msg Hvalid;
      apply generated_bls12381_map_fp2_to_g2_gas_bounded; exact Hvalid
    | ].
  apply Forall_cons;
    [ unfold precompile_result_gas_bounded; intros msg Hvalid;
      apply generated_secp256r1_precompile_gas_bounded; exact Hvalid
    | ].
  constructor.
Qed.
End ConcreteTable.
