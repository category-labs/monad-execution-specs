From Stdlib Require Import List String ZArith NArith.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import MonadVM.Ec.Bls12_381.
Require Import MonadVM.Support.UintN.
Require Import MonadExecutionSpecs.Refinement.BlsMapLiteralParsing.

Open Scope string_scope.

(** The two effective-cofactor constants follow the source and generated
    hexadecimal literals at positions 55 and 76 of the checked inventory.
    Their generated unsigned parsing has a stable exact integer value for
    arbitrary typed fallbacks. *)
Definition parsed_bls_integer_literal (literal : string) : Z :=
  match RocqOfOCaml.OCamlZ.of_string_opt literal with
  | Some value => value
  | None => 0%Z
  end.

Lemma generated_g1_effective_cofactor_matches_literal
    (UZ : RocqOfOCaml.Basics.Unreachable Z.t)
    (UN : RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t) :
  Z.of_N (@MonadVM.Ec.Bls12_381.F_p_SWU_curve.h_eff UZ UN) =
    parsed_bls_integer_literal (nth 55 bls_map_hex_literals "").
Proof. vm_compute. reflexivity. Qed.

Lemma generated_g2_effective_cofactor_matches_literal
    (UZ : RocqOfOCaml.Basics.Unreachable Z.t)
    (UN : RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t) :
  Z.of_N (@MonadVM.Ec.Bls12_381.F_p2_SWU_curve.h_eff UZ UN) =
    parsed_bls_integer_literal (nth 76 bls_map_hex_literals "").
Proof. vm_compute. reflexivity. Qed.

Print Assumptions generated_g1_effective_cofactor_matches_literal.
Print Assumptions generated_g2_effective_cofactor_matches_literal.
