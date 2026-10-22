From Stdlib Require Import NArith ZArith Bool Lia.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import MonadVM.Chain.Ethereum.
Require Import MonadVM.Comparable.
Require Import MonadVM.Numeric.
Require Import MonadVM.Support.UintN.

Local Open Scope Z_scope.

(** The generated legacy-signature decoder rejects [v = 0] at the tracked
    fixture's chain ID for every other transaction field, independently of
    the typed exceptional-value parameters. *)
Lemma generated_legacy_v_zero_has_no_signature
    `{unreachable_u8 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U8.t}
    `{unreachable_u256 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}
    (tx : MonadVM.Chain.Ethereum.Transaction.legacy_tx) :
  @MonadVM.Chain.Ethereum.Transaction.signature
    unreachable_u8 unreachable_u256 143%N
    (MonadVM.Chain.Ethereum.Transaction.Legacy
      (MonadVM.Chain.Ethereum.Transaction.legacy_tx.with_v
        (@MonadVM.Numeric.U256.zero unreachable_u256) tx)) = None.
Proof.
  destruct tx.
  vm_compute.
  reflexivity.
Qed.

Print Assumptions generated_legacy_v_zero_has_no_signature.

(** The generated decoder's four acceptance checks, before the bounded
    arithmetic characterization proved below. *)
Definition generated_legacy_v_accepted
    `{unreachable_u256 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}
    (chain_id : MonadVM.Support.UintN.t)
    (v : MonadVM.Numeric.U256.t) : bool :=
  let parity :=
    MonadVM.Numeric.U256.op_minus
      (MonadVM.Numeric.U256.op_minus v
        (MonadVM.Numeric.U256.op_tildedollar 35))
      (MonadVM.Numeric.U256.op_star
        (MonadVM.Numeric.U256.op_tildedollar 2)
        (MonadVM.Numeric.U256.of_uint_exn chain_id)) in
  orb (MonadVM.Numeric.U256.op_eq v
         (MonadVM.Numeric.U256.op_tildedollar 27))
    (orb (MonadVM.Numeric.U256.op_eq v
            (MonadVM.Numeric.U256.op_tildedollar 28))
      (orb (MonadVM.Numeric.U256.op_eq parity
              MonadVM.Numeric.U256.zero)
           (MonadVM.Numeric.U256.op_eq parity
              MonadVM.Numeric.U256.one))).

Lemma generated_legacy_invalid_v_has_no_signature
    `{unreachable_u8 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U8.t}
    `{unreachable_u256 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}
    (chain_id : MonadVM.Support.UintN.t)
    (v : MonadVM.Numeric.U256.t)
    (tx : MonadVM.Chain.Ethereum.Transaction.legacy_tx) :
  generated_legacy_v_accepted chain_id v = false ->
  MonadVM.Chain.Ethereum.Transaction.signature chain_id
    (MonadVM.Chain.Ethereum.Transaction.Legacy
      (MonadVM.Chain.Ethereum.Transaction.legacy_tx.with_v v tx)) = None.
Proof.
  intro Hinvalid.
  unfold generated_legacy_v_accepted in Hinvalid.
  apply Bool.orb_false_iff in Hinvalid as [H27 Hrest].
  apply Bool.orb_false_iff in Hrest as [H28 Hrest].
  apply Bool.orb_false_iff in Hrest as [H0 H1].
  destruct tx.
  cbn [MonadVM.Chain.Ethereum.Transaction.signature
       MonadVM.Chain.Ethereum.Transaction.legacy_tx.with_v].
  rewrite H27, H28, H0, H1.
  reflexivity.
Qed.

Print Assumptions generated_legacy_invalid_v_has_no_signature.
Lemma u256_sub_eq
    (u : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t)
    (x y : Z) :
  @MonadVM.Numeric.U256.op_minus u x y = Z.land (x - y) (Z.ones 256).
Proof. reflexivity. Qed.

Lemma u256_mul_eq
    (u : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t)
    (x y : Z) :
  @MonadVM.Numeric.U256.op_star u x y = Z.land (x * y) (Z.ones 256).
Proof. reflexivity. Qed.

Lemma u256_eq_eq (x y : Z) :
  MonadVM.Numeric.U256.op_eq x y = Z.eqb x y.
Proof.
  unfold MonadVM.Numeric.U256.op_eq,
    MonadVM.Comparable.Make.op_eq,
    MonadVM.Comparable.Make.comparison_op.
  cbn.
  unfold MonadVM.Numeric.TwosComplement.Unsigned.op_eq,
    MonadVM.Numeric.Make.op_eq.
  cbn.
  unfold MonadVM.Comparable.Make.op_eq,
    MonadVM.Comparable.Make.comparison_op.
  cbn.
  unfold RocqOfOCaml.OCamlZ.compare.
  unfold MonadVM.Numeric.Make.to_z,
    MonadVM.Numeric.Make.Impl.to_z.
  cbn.
  destruct (Z.compare x y) eqn:Hcmp; cbn.
  - apply Z.compare_eq in Hcmp. subst. symmetry; apply Z.eqb_refl.
  - apply (proj1 (Z.compare_lt_iff x y)) in Hcmp.
    symmetry. apply Z.eqb_neq. lia.
  - apply (proj1 (Z.compare_gt_iff x y)) in Hcmp.
    symmetry. apply Z.eqb_neq. lia.
Qed.

Lemma u256_legacy_literals
    (u : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t) :
  @MonadVM.Numeric.U256.op_tildedollar u 2 = 2 /\
  @MonadVM.Numeric.U256.op_tildedollar u 27 = 27 /\
  @MonadVM.Numeric.U256.op_tildedollar u 28 = 28 /\
  @MonadVM.Numeric.U256.op_tildedollar u 35 = 35 /\
  @MonadVM.Numeric.U256.zero u = 0 /\
  @MonadVM.Numeric.U256.one u = 1.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

Lemma u256_of_uint_bound
    (u : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t)
    (chain_id : N) :
  Z.of_N chain_id < 2 ^ 256 ->
  @MonadVM.Numeric.U256.of_uint_exn u chain_id = Z.of_N chain_id.
Proof.
  intro Hbound.
  cbn.
  unfold MonadVM.Numeric.Make.of_z_exn.
  cbn.
  unfold MonadVM.Numeric.Make.of_z_opt,
    MonadVM.Numeric.Make.Impl.of_z_opt,
    MonadVM.Support.UintN.to_z.
  cbn.
  unfold MonadVM.Numeric.Make.Impl.in_range.
  cbn.
  assert (Hlo : (Z.of_N chain_id >=? 0) = true).
  { apply Z.geb_le. lia. }
  assert (Hhi : (Z.of_N chain_id <=? 2 ^ 256 - 1) = true).
  { apply Z.leb_le. lia. }
  unfold Z.zero.
  cbn in Hhi.
  rewrite Hlo, Hhi.
  reflexivity.
Qed.

Lemma u256_legacy_parity
    (u : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t)
    (chain_id : N) (v : Z) :
  Z.of_N chain_id < 2 ^ 256 ->
  @MonadVM.Numeric.U256.op_minus u
    (@MonadVM.Numeric.U256.op_minus u v
      (@MonadVM.Numeric.U256.op_tildedollar u 35))
    (@MonadVM.Numeric.U256.op_star u
      (@MonadVM.Numeric.U256.op_tildedollar u 2)
      (@MonadVM.Numeric.U256.of_uint_exn u chain_id)) =
  (v - 35 - 2 * Z.of_N chain_id) mod 2 ^ 256.
Proof.
  intro Hbound.
  rewrite u256_of_uint_bound by exact Hbound.
  destruct (u256_legacy_literals u) as [H2 [_ [_ [H35 _]]]].
  rewrite H2, H35.
  rewrite u256_sub_eq, u256_sub_eq, u256_mul_eq.
  repeat rewrite Z.land_ones by lia.
  rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r.
  reflexivity.
Qed.

Lemma modular_parity (modulus v base : Z) :
  2 < modulus ->
  0 <= v < modulus ->
  0 <= base ->
  base + 1 < modulus ->
  ((v - base) mod modulus = 0 \/
   (v - base) mod modulus = 1) <->
  (v = base \/ v = base + 1).
Proof.
  intros Hmod Hv Hbase Hbase_max.
  split.
  - intros [Hzero | Hone].
    + pose proof (Z.mod_eq (v - base) modulus ltac:(lia)) as Heq.
      rewrite Hzero in Heq.
      left.
      destruct (Z_lt_ge_dec ((v - base) / modulus) 0) as [Hneg | Hnonneg].
      * nia.
      * destruct (Z_lt_ge_dec ((v - base) / modulus) 1) as [Hq | Hq].
        -- assert (Hqzero : (v - base) / modulus = 0) by lia.
           rewrite Hqzero in Heq; lia.
        -- nia.
    + pose proof (Z.mod_eq (v - base) modulus ltac:(lia)) as Heq.
      rewrite Hone in Heq.
      right.
      destruct (Z_lt_ge_dec ((v - base) / modulus) 0) as [Hneg | Hnonneg].
      * nia.
      * destruct (Z_lt_ge_dec ((v - base) / modulus) 1) as [Hq | Hq].
        -- assert (Hqzero : (v - base) / modulus = 0) by lia.
           rewrite Hqzero in Heq; lia.
        -- nia.
  - intros [-> | ->].
    + left. replace (base - base) with 0 by lia.
      apply Z.mod_small; lia.
    + right. replace (base + 1 - base) with 1 by lia.
      apply Z.mod_small; lia.
Qed.

(** Canonical 256-bit values exclude the modular wraparound aliases. The
    chain bound also ensures [of_uint_exn] never reaches its fallback. *)
Lemma generated_legacy_v_accepted_iff_arithmetic
    (u : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t)
    (chain_id : N) (v : Z) :
  0 <= v < 2 ^ 256 ->
  2 * Z.of_N chain_id + 36 < 2 ^ 256 ->
  @generated_legacy_v_accepted u chain_id v = true <->
  (v = 27 \/ v = 28 \/
   v = 2 * Z.of_N chain_id + 35 \/
   v = 2 * Z.of_N chain_id + 36).
Proof.
  intros Hv Hchain.
  unfold generated_legacy_v_accepted.
  cbn zeta.
  rewrite u256_legacy_parity by lia.
  destruct (u256_legacy_literals u) as [H2 [H27 [H28 [H35 [H0 H1]]]]].
  rewrite H27, H28, H0, H1.
  repeat rewrite u256_eq_eq.
  repeat rewrite Bool.orb_true_iff.
  repeat rewrite Z.eqb_eq.
  replace (v - 35 - 2 * Z.of_N chain_id)
    with (v - (2 * Z.of_N chain_id + 35)) by ring.
  rewrite (modular_parity (2 ^ 256) v (2 * Z.of_N chain_id + 35)) by lia.
  lia.
Qed.

Print Assumptions generated_legacy_v_accepted_iff_arithmetic.

(** Within the canonical word range, rejecting the four numeric values
    suffices to reject every legacy signature, for every bounded chain ID. *)
Lemma generated_legacy_arithmetic_invalid_v_has_no_signature
    `{unreachable_u8 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U8.t}
    `{unreachable_u256 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}
    (chain_id : MonadVM.Support.UintN.t)
    (v : MonadVM.Numeric.U256.t)
    (tx : MonadVM.Chain.Ethereum.Transaction.legacy_tx) :
  0 <= v < 2 ^ 256 ->
  2 * Z.of_N chain_id + 36 < 2 ^ 256 ->
  v <> 27 -> v <> 28 ->
  v <> 2 * Z.of_N chain_id + 35 ->
  v <> 2 * Z.of_N chain_id + 36 ->
  MonadVM.Chain.Ethereum.Transaction.signature chain_id
    (MonadVM.Chain.Ethereum.Transaction.Legacy
      (MonadVM.Chain.Ethereum.Transaction.legacy_tx.with_v v tx)) = None.
Proof.
  intros Hv Hchain H27 H28 H35 H36.
  apply generated_legacy_invalid_v_has_no_signature.
  destruct (generated_legacy_v_accepted chain_id v) eqn:Hacc;
    [|reflexivity].
  apply (proj1
    (generated_legacy_v_accepted_iff_arithmetic
      unreachable_u256 chain_id v Hv Hchain)) in Hacc.
  tauto.
Qed.

Print Assumptions generated_legacy_arithmetic_invalid_v_has_no_signature.
