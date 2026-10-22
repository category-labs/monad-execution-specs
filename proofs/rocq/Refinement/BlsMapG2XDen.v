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

(** Keep the three G2 x-denominator coefficients separate from polynomial
    normalization. Reducing the whole generated definition at once expands
    the complex-field functor too aggressively. *)
Section G2XDen.
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

  Definition coefficients : list field :=
    [multiply (of_string (hex_at 62)) i;
     add (of_string (hex_at 63))
       (multiply (of_string (hex_at 64)) i);
     of_string "1"].

  Let pair (real imaginary : Z) : field :=
    {| MonadVM.Ec.Algebra.Complex_extension.t.re := real;
       MonadVM.Ec.Algebra.Complex_extension.t.im := imaginary |}.

  Lemma coefficients_match_parsed_values :
    coefficients =
      [pair 0%Z (parsed_bls_field_literal (hex_at 62));
       pair (parsed_bls_field_literal (hex_at 63))
         (parsed_bls_field_literal (hex_at 64));
       pair (parsed_bls_field_literal "1") 0%Z].
  Proof.
    unfold coefficients, pair, hex_at.
    cbn.
    reflexivity.
  Qed.

  Lemma generated_x_den_matches_coefficients :
    @MonadVM.Ec.Bls12_381.F_p2_SWU_curve.x_den
      UZ UN UX UB UF UA UF2 = coefficients.
  Proof.
    change
      (@MonadVM.Ec.Algebra.Polynomial_ring.of_coeffs
        field
        (@MonadVM.Ec.Bls12_381.F_p2_SWU_curve.F_p2x_fargs
          UZ UN UX UB UF)
        UF2 UA coefficients = coefficients).
    apply generated_of_coeffs_keeps_nonzero_last.
    - unfold coefficients, RocqOfOCaml.OCamlIarray.length.
      simpl. lia.
    - unfold coefficients, RocqOfOCaml.OCamlIarray.length.
      vm_compute. reflexivity.
  Qed.

  Theorem generated_x_den_matches_parsed_values :
    @MonadVM.Ec.Bls12_381.F_p2_SWU_curve.x_den
      UZ UN UX UB UF UA UF2 =
      [pair 0%Z (parsed_bls_field_literal (hex_at 62));
       pair (parsed_bls_field_literal (hex_at 63))
         (parsed_bls_field_literal (hex_at 64));
       pair (parsed_bls_field_literal "1") 0%Z].
  Proof.
    rewrite generated_x_den_matches_coefficients.
    apply coefficients_match_parsed_values.
  Qed.
End G2XDen.

Print Assumptions coefficients_match_parsed_values.
Print Assumptions generated_x_den_matches_coefficients.
Print Assumptions generated_x_den_matches_parsed_values.
