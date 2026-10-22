From Stdlib Require Import List String ZArith Lia.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import MonadVM.Ec.Bls12_381.
Require Import MonadVM.Ec.Algebra.
Require Import MonadVM.Numeric.
Require Import MonadVM.Support.UintN.
Require Import MonadExecutionSpecs.Refinement.BlsMapLiteralParsing.
Require Import MonadExecutionSpecs.Termination.PolynomialOfCoeffs.

Import ListNotations.
Open Scope string_scope.

Section G2Tables.
  Context
    (UZ : RocqOfOCaml.Basics.Unreachable Z.t)
    (UN : RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t)
    (UX : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.Integer.t)
    (UB : RocqOfOCaml.Basics.Unreachable
      MonadVM.Numeric.IntegerBase.(MonadVM.Numeric.Make.Make_result.t))
    (UF : RocqOfOCaml.Basics.Unreachable
      (@MonadVM.Ec.Bls12_381.F_p.t UZ UN UB))
    (UA : RocqOfOCaml.Basics.Unreachable
      (RocqOfOCaml.OCamlIarray.t
        (@MonadVM.Ec.Bls12_381.F_p2.t UZ UN UX UB UF)))
    (UF2 : RocqOfOCaml.Basics.Unreachable
      (@MonadVM.Ec.Bls12_381.F_p2.t UZ UN UX UB UF)).

  Let field := @MonadVM.Ec.Bls12_381.F_p2.t UZ UN UX UB UF.
  Let of_string := @MonadVM.Ec.Bls12_381.F_p2.op_tildeat UZ UN UX UB UF.
  Let add := @MonadVM.Ec.Bls12_381.F_p2.op_plus UZ UN UX UB UF.
  Let multiply := @MonadVM.Ec.Bls12_381.F_p2.op_star UZ UN UX UB UF.
  Let i := @MonadVM.Ec.Bls12_381.F_p2.i_value UZ UN UX UB UF.
  Let hex_at (index : nat) := nth index bls_map_hex_literals "".
  Let parsed (index : nat) := parsed_bls_field_literal (hex_at index).
  Let pair (real imaginary : Z) : field :=
    {| MonadVM.Ec.Algebra.Complex_extension.t.re := real;
       MonadVM.Ec.Algebra.Complex_extension.t.im := imaginary |}.

  Definition x_num_coefficients : list field :=
    [add (of_string (hex_at 56))
       (multiply (of_string (hex_at 57)) i);
     multiply (of_string (hex_at 58)) i;
     add (of_string (hex_at 59))
       (multiply (of_string (hex_at 60)) i);
     of_string (hex_at 61)].

  Lemma x_num_coefficients_match_parsed_values :
    x_num_coefficients =
      [pair (parsed 56) (parsed 57);
       pair 0%Z (parsed 58);
       pair (parsed 59) (parsed 60);
       pair (parsed 61) 0%Z].
  Proof.
    unfold x_num_coefficients, pair, parsed, hex_at.
    cbn.
    reflexivity.
  Qed.

  Lemma generated_x_num_matches_coefficients :
    @MonadVM.Ec.Bls12_381.F_p2_SWU_curve.x_num
      UZ UN UX UB UF UA UF2 = x_num_coefficients.
  Proof.
    change
      (@MonadVM.Ec.Algebra.Polynomial_ring.of_coeffs
        field
        (@MonadVM.Ec.Bls12_381.F_p2_SWU_curve.F_p2x_fargs
          UZ UN UX UB UF)
        UF2 UA x_num_coefficients = x_num_coefficients).
    apply generated_of_coeffs_keeps_nonzero_last.
    - unfold x_num_coefficients, RocqOfOCaml.OCamlIarray.length.
      simpl. lia.
    - unfold x_num_coefficients, RocqOfOCaml.OCamlIarray.length.
      vm_compute. reflexivity.
  Qed.

  Theorem generated_x_num_matches_parsed_values :
    @MonadVM.Ec.Bls12_381.F_p2_SWU_curve.x_num
      UZ UN UX UB UF UA UF2 =
      [pair (parsed 56) (parsed 57);
       pair 0%Z (parsed 58);
       pair (parsed 59) (parsed 60);
       pair (parsed 61) 0%Z].
  Proof.
    rewrite generated_x_num_matches_coefficients.
    apply x_num_coefficients_match_parsed_values.
  Qed.
End G2Tables.

Print Assumptions generated_x_num_matches_parsed_values.
