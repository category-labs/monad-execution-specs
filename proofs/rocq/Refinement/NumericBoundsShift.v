From Stdlib Require Import ZArith.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import MonadVM.Numeric.

Open Scope Z_scope.

(** The source uses a native left shift for nonnegative fixed-width bounds.
    The generated operation is still the original mathematical power of two
    for every width, including a negative width in the compatibility model. *)
Lemma generated_pow2_for_bound_eq_pow
    `{_fargs : MonadVM.Numeric.Make.FArgs} (bits : Z) :
  MonadVM.Numeric.Make.Impl.pow2_for_bound bits = 2 ^ bits.
Proof.
  unfold MonadVM.Numeric.Make.Impl.pow2_for_bound.
  destruct (Z.ltb bits 0) eqn:Hbits.
  - reflexivity.
  - rewrite Z.shiftl_1_l.
    reflexivity.
Qed.

Lemma generated_max_t_eq_pow
    `{_fargs : MonadVM.Numeric.Make.FArgs} :
  MonadVM.Numeric.Make.Impl.max_t =
  match (MonadVM.Numeric.Make.Impl.bit_width,
         MonadVM.Numeric.Make.Impl.signed) with
  | (None, _) => None
  | (Some bits, true) => Some (2 ^ (bits - 1) - 1)
  | (Some bits, false) => Some (2 ^ bits - 1)
  end.
Proof.
  unfold MonadVM.Numeric.Make.Impl.max_t.
  destruct MonadVM.Numeric.Make.Impl.bit_width as [bits|];
    destruct MonadVM.Numeric.Make.Impl.signed;
    simpl; try reflexivity;
    now rewrite generated_pow2_for_bound_eq_pow.
Qed.

Lemma generated_min_t_eq_pow
    `{_fargs : MonadVM.Numeric.Make.FArgs} :
  MonadVM.Numeric.Make.Impl.min_t =
  match (MonadVM.Numeric.Make.Impl.bit_width,
         MonadVM.Numeric.Make.Impl.signed) with
  | (_, false) => Some 0
  | (Some bits, true) => Some (0 - 2 ^ (bits - 1))
  | (None, true) => None
  end.
Proof.
  unfold MonadVM.Numeric.Make.Impl.min_t.
  destruct MonadVM.Numeric.Make.Impl.bit_width as [bits|];
    destruct MonadVM.Numeric.Make.Impl.signed;
    simpl; try reflexivity;
    now rewrite generated_pow2_for_bound_eq_pow.
Qed.
