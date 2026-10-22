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

Section G2YTables.
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

  Definition y_num_coefficients : list field :=
    [add (of_string (hex_at 65))
       (multiply (of_string (hex_at 66)) i);
     multiply (of_string (hex_at 67)) i;
     add (of_string (hex_at 68))
       (multiply (of_string (hex_at 69)) i);
     of_string (hex_at 70)].

  Lemma y_num_coefficients_match_parsed_values :
    y_num_coefficients =
      [pair (parsed 65) (parsed 66);
       pair 0%Z (parsed 67);
       pair (parsed 68) (parsed 69);
       pair (parsed 70) 0%Z].
  Proof.
    unfold y_num_coefficients, pair, parsed, hex_at.
    cbn.
    reflexivity.
  Qed.

  Lemma generated_y_num_matches_coefficients :
    @MonadVM.Ec.Bls12_381.F_p2_SWU_curve.y_num
      UZ UN UX UB UF UA UF2 = y_num_coefficients.
  Proof.
    change
      (@MonadVM.Ec.Algebra.Polynomial_ring.of_coeffs
        field
        (@MonadVM.Ec.Bls12_381.F_p2_SWU_curve.F_p2x_fargs
          UZ UN UX UB UF)
        UF2 UA y_num_coefficients = y_num_coefficients).
    apply generated_of_coeffs_keeps_nonzero_last.
    - unfold y_num_coefficients, RocqOfOCaml.OCamlIarray.length.
      simpl. lia.
    - unfold y_num_coefficients, RocqOfOCaml.OCamlIarray.length.
      vm_compute. reflexivity.
  Qed.

  Theorem generated_y_num_matches_parsed_values :
    @MonadVM.Ec.Bls12_381.F_p2_SWU_curve.y_num
      UZ UN UX UB UF UA UF2 =
      [pair (parsed 65) (parsed 66);
       pair 0%Z (parsed 67);
       pair (parsed 68) (parsed 69);
       pair (parsed 70) 0%Z].
  Proof.
    rewrite generated_y_num_matches_coefficients.
    apply y_num_coefficients_match_parsed_values.
  Qed.

  Definition y_den_coefficients : list field :=
    [add (of_string (hex_at 71))
       (multiply (of_string (hex_at 72)) i);
     multiply (of_string (hex_at 73)) i;
     add (of_string (hex_at 74))
       (multiply (of_string (hex_at 75)) i);
     of_string "1"].

  Lemma y_den_coefficients_match_parsed_values :
    y_den_coefficients =
      [pair (parsed 71) (parsed 72);
       pair 0%Z (parsed 73);
       pair (parsed 74) (parsed 75);
       pair (parsed_bls_field_literal "1") 0%Z].
  Proof.
    unfold y_den_coefficients, pair, parsed, hex_at.
    cbn.
    reflexivity.
  Qed.

  Lemma generated_y_den_matches_coefficients :
    @MonadVM.Ec.Bls12_381.F_p2_SWU_curve.y_den
      UZ UN UX UB UF UA UF2 = y_den_coefficients.
  Proof.
    change
      (@MonadVM.Ec.Algebra.Polynomial_ring.of_coeffs
        field
        (@MonadVM.Ec.Bls12_381.F_p2_SWU_curve.F_p2x_fargs
          UZ UN UX UB UF)
        UF2 UA y_den_coefficients = y_den_coefficients).
    apply generated_of_coeffs_keeps_nonzero_last.
    - unfold y_den_coefficients, RocqOfOCaml.OCamlIarray.length.
      simpl. lia.
    - unfold y_den_coefficients, RocqOfOCaml.OCamlIarray.length.
      vm_compute. reflexivity.
  Qed.

  Theorem generated_y_den_matches_parsed_values :
    @MonadVM.Ec.Bls12_381.F_p2_SWU_curve.y_den
      UZ UN UX UB UF UA UF2 =
      [pair (parsed 71) (parsed 72);
       pair 0%Z (parsed 73);
       pair (parsed 74) (parsed 75);
       pair (parsed_bls_field_literal "1") 0%Z].
  Proof.
    rewrite generated_y_den_matches_coefficients.
    apply y_den_coefficients_match_parsed_values.
  Qed.
End G2YTables.

Print Assumptions generated_y_num_matches_parsed_values.
Print Assumptions generated_y_den_matches_parsed_values.
