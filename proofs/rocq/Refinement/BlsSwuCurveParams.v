From Stdlib Require Import List String ZArith.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import MonadVM.Ec.Bls12_381.
Require Import MonadVM.Numeric.
Require Import MonadVM.Support.UintN.
Require Import MonadExecutionSpecs.Refinement.BlsMapLiteralParsing.

(** Generated curve-module parameters are projected through the generated
    functor records. The G1 values are the first two checked BLS hex literals;
    the G2 parameters are the small source integers 240 and 1012 in Fp2. *)

Lemma generated_g1_swu_a_value
    (UZ : RocqOfOCaml.Basics.Unreachable Z.t)
    (UN : RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t)
    (UX : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.Integer.t)
    (UB : RocqOfOCaml.Basics.Unreachable
      MonadVM.Numeric.IntegerBase.(MonadVM.Numeric.Make.Make_result.t))
    (UF : RocqOfOCaml.Basics.Unreachable
      (@MonadVM.Ec.Bls12_381.F_p.t UZ UN UB)) :
  @MonadVM.Ec.Bls12_381.F_p_SWU_curve.Params.a_value UZ UN UX UB UF =
    parsed_bls_field_literal (nth 0 bls_map_hex_literals "").
Proof. vm_compute. reflexivity. Qed.

Lemma generated_g1_swu_b_value
    (UZ : RocqOfOCaml.Basics.Unreachable Z.t)
    (UN : RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t)
    (UX : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.Integer.t)
    (UB : RocqOfOCaml.Basics.Unreachable
      MonadVM.Numeric.IntegerBase.(MonadVM.Numeric.Make.Make_result.t))
    (UF : RocqOfOCaml.Basics.Unreachable
      (@MonadVM.Ec.Bls12_381.F_p.t UZ UN UB)) :
  @MonadVM.Ec.Bls12_381.F_p_SWU_curve.Params.b_value UZ UN UX UB UF =
    parsed_bls_field_literal (nth 1 bls_map_hex_literals "").
Proof. vm_compute. reflexivity. Qed.

Lemma generated_g2_swu_a_value
    (UZ : RocqOfOCaml.Basics.Unreachable Z.t)
    (UN : RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t)
    (UX : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.Integer.t)
    (UB : RocqOfOCaml.Basics.Unreachable
      MonadVM.Numeric.IntegerBase.(MonadVM.Numeric.Make.Make_result.t))
    (UF : RocqOfOCaml.Basics.Unreachable
      (@MonadVM.Ec.Bls12_381.F_p.t UZ UN UB)) :
  let a := @MonadVM.Ec.Bls12_381.F_p2_SWU_curve.Params.a_value UZ UN UX UB UF in
  a.(MonadVM.Ec.Algebra.Complex_extension.t.re) = 0%Z /\
  a.(MonadVM.Ec.Algebra.Complex_extension.t.im) = 240%Z.
Proof. vm_compute. split; reflexivity. Qed.

Lemma generated_g2_swu_b_value
    (UZ : RocqOfOCaml.Basics.Unreachable Z.t)
    (UN : RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t)
    (UX : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.Integer.t)
    (UB : RocqOfOCaml.Basics.Unreachable
      MonadVM.Numeric.IntegerBase.(MonadVM.Numeric.Make.Make_result.t))
    (UF : RocqOfOCaml.Basics.Unreachable
      (@MonadVM.Ec.Bls12_381.F_p.t UZ UN UB)) :
  let b := @MonadVM.Ec.Bls12_381.F_p2_SWU_curve.Params.b_value UZ UN UX UB UF in
  b.(MonadVM.Ec.Algebra.Complex_extension.t.re) = 1012%Z /\
  b.(MonadVM.Ec.Algebra.Complex_extension.t.im) = 1012%Z.
Proof. vm_compute. split; reflexivity. Qed.

Print Assumptions generated_g1_swu_a_value.
Print Assumptions generated_g1_swu_b_value.
Print Assumptions generated_g2_swu_a_value.
Print Assumptions generated_g2_swu_b_value.
