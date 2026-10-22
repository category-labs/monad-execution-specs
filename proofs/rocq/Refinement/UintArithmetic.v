(** Relate the [N]-backed override to the source's integer formulas.

    Quotient and remainder use truncation toward zero where the source does;
    unsigned inputs make these agree with their Euclidean counterparts.
    The explicit hypotheses exclude native exceptional inputs. These are
    arithmetic model laws, not a verification of the Zarith implementation. *)

From Stdlib Require Import NArith ZArith Lia.
Require Import RocqOfOCaml.Basics.
Require Import MonadVM.Support.UintN.

Local Open Scope Z_scope.

Lemma to_z_div (fallback : Unreachable N) (left right : N) :
  right <> 0%N ->
  to_z (@op_div fallback left right) = Z.quot (to_z left) (to_z right).
Proof.
  intro Hright. unfold op_div.
  destruct (N.eqb right 0) eqn:Htest.
  - apply N.eqb_eq in Htest. contradiction.
  - apply N2Z.inj_quot.
Qed.

Lemma to_z_modulo (fallback : Unreachable N) (left right : N) :
  right <> 0%N ->
  to_z (@modulo fallback left right) = Z.modulo (to_z left) (to_z right).
Proof.
  intro Hright. unfold modulo.
  destruct (N.eqb right 0) eqn:Htest.
  - apply N.eqb_eq in Htest. contradiction.
  - apply N2Z.inj_mod.
Qed.

Lemma to_z_rem (fallback : Unreachable N) (left right : N) :
  right <> 0%N ->
  to_z (@rem fallback left right) = Z.rem (to_z left) (to_z right).
Proof.
  intro Hright. unfold rem, modulo.
  destruct (N.eqb right 0) eqn:Htest.
  - apply N.eqb_eq in Htest. contradiction.
  - apply N2Z.inj_rem.
Qed.

Lemma to_z_addmod (fallback : Unreachable N) (left right modulus : N) :
  modulus <> 0%N ->
  to_z (@addmod fallback left right modulus) =
    Z.rem (to_z left + to_z right) (to_z modulus).
Proof.
  intro Hmodulus. unfold addmod.
  change (to_z (@rem fallback (left + right)%N modulus) =
    Z.rem (to_z left + to_z right) (to_z modulus)).
  rewrite to_z_rem by exact Hmodulus.
  unfold to_z. now rewrite N2Z.inj_add.
Qed.

Lemma to_z_mulmod (fallback : Unreachable N) (left right modulus : N) :
  modulus <> 0%N ->
  to_z (@mulmod fallback left right modulus) =
    Z.rem (to_z left * to_z right) (to_z modulus).
Proof.
  intro Hmodulus. unfold mulmod.
  change (to_z (@rem fallback (left * right)%N modulus) =
    Z.rem (to_z left * to_z right) (to_z modulus)).
  rewrite to_z_rem by exact Hmodulus.
  unfold to_z. now rewrite N2Z.inj_mul.
Qed.

Lemma to_z_pow (fallback : Unreachable N) (base : N) (exponent : Z) :
  0 <= exponent ->
  to_z (@op_starstar fallback base exponent) = Z.pow (to_z base) exponent.
Proof.
  intro Hexponent. unfold op_starstar.
  destruct (Z.ltb exponent 0) eqn:Htest.
  - apply Z.ltb_lt in Htest. lia.
  - unfold to_z. rewrite N2Z.inj_pow, Z2N.id by exact Hexponent. reflexivity.
Qed.

Theorem bytes_to_whole_words_source_formula
    (fallback : Unreachable N) (value : N) :
  to_z (@bytes_to_whole_words fallback value) =
    Z.quot (to_z value) 32 +
    (if Z.eqb (Z.rem (to_z value) 32) 0 then 0 else 1).
Proof.
  rewrite Z.quot_div_nonneg, Z.rem_mod_nonneg by
    (try apply to_z_nonnegative; lia).
  unfold bytes_to_whole_words, to_z.
  rewrite N2Z.inj_div, N2Z.inj_add.
  change ((Z.of_N value + 31) / 32 = Z.of_N value / 32 +
    (if Z.eqb (Z.of_N value mod 32) 0 then 0 else 1)).
  pose proof (Z.div_mod (Z.of_N value) 32 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound (Z.of_N value) 32 ltac:(lia)) as Hmod.
  destruct (Z.eqb (Z.of_N value mod 32) 0) eqn:Htest.
  - apply Z.eqb_eq in Htest. symmetry.
    apply Z.div_unique_pos with (r := 31); lia.
  - apply Z.eqb_neq in Htest. symmetry.
    apply Z.div_unique_pos with (r := Z.of_N value mod 32 - 1); lia.
Qed.

Lemma to_z_minus_1_64th (fallback : Unreachable N) (value : N) :
  to_z (@minus_1_64th fallback value) = to_z value - Z.quot (to_z value) 64.
Proof.
  unfold minus_1_64th, to_z. rewrite N2Z.inj_sub.
  - rewrite N2Z.inj_quot. reflexivity.
  - apply N2Z.inj_le. rewrite N2Z.inj_div.
    apply Z.div_le_upper_bound; [reflexivity|].
    pose proof (N2Z.is_nonneg value).
    change (Z.of_N value <= 64 * Z.of_N value). lia.
Qed.

Lemma to_z_div_rem (fallback : Unreachable N) (left right : N) :
  right <> 0%N ->
  let '(quotient, remainder) := @div_rem fallback left right in
  (to_z quotient, to_z remainder) =
    (Z.div (to_z left) (to_z right), Z.modulo (to_z left) (to_z right)).
Proof.
  intro Hright. unfold div_rem.
  destruct (N.eqb right 0) eqn:Htest.
  - apply N.eqb_eq in Htest. contradiction.
  - cbv beta iota zeta. unfold to_z.
    now rewrite N2Z.inj_div, N2Z.inj_mod.
Qed.

Lemma to_z_shift_left (fallback : Unreachable N) (value : N) (shift : Z) :
  0 <= shift ->
  to_z (@shift_left fallback value shift) = to_z value * 2 ^ shift.
Proof.
  intro Hshift. unfold shift_left.
  destruct (Z.ltb shift 0) eqn:Htest.
  - apply Z.ltb_lt in Htest. lia.
  - unfold to_z at 1.
    rewrite Z2N.id by (apply Z.shiftl_nonneg; apply to_z_nonnegative).
    apply Z.shiftl_mul_pow2. exact Hshift.
Qed.

Lemma to_z_shift_right (fallback : Unreachable N) (value : N) (shift : Z) :
  0 <= shift ->
  to_z (@shift_right fallback value shift) = to_z value / 2 ^ shift.
Proof.
  intro Hshift. unfold shift_right.
  destruct (Z.ltb shift 0) eqn:Htest.
  - apply Z.ltb_lt in Htest. lia.
  - unfold to_z at 1.
    rewrite Z2N.id by (apply Z.shiftr_nonneg; apply to_z_nonnegative).
    apply Z.shiftr_div_pow2. exact Hshift.
Qed.

Lemma shift_left_negative (fallback : Unreachable N) (value : N) (shift : Z) :
  shift < 0 -> @shift_left fallback value shift = @unreachable N fallback.
Proof.
  intro Hshift. unfold shift_left.
  assert (Htest : Z.ltb shift 0 = true) by (apply Z.ltb_lt; exact Hshift).
  now rewrite Htest.
Qed.

Lemma shift_right_negative (fallback : Unreachable N) (value : N) (shift : Z) :
  shift < 0 -> @shift_right fallback value shift = @unreachable N fallback.
Proof.
  intro Hshift. unfold shift_right.
  assert (Htest : Z.ltb shift 0 = true) by (apply Z.ltb_lt; exact Hshift).
  now rewrite Htest.
Qed.
