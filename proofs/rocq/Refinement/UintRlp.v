(** Canonical unsigned-integer RLP encoding for the [UintN] override.

    The source accepts the empty string for zero and otherwise requires a
    nonzero first byte. These proofs establish that characterization for all
    finite byte strings, using the executable byte decoder and bit-length
    calculation, then prove both directions of the codec round trip. Native
    machine-size and FFI refinement are separate tasks. *)

From Stdlib Require Import Ascii String ZArith NArith Lia.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import MonadVM.Support.UintN.
Require MonadVM.Rlp.

Local Open Scope Z_scope.

Lemma reverse_append_spec (value suffix : string) :
  reverse_append value suffix = Strings.String.append (reverse value) suffix.
Proof.
  assert (H : forall value prefix suffix,
    reverse_append value (Strings.String.append prefix suffix) =
    Strings.String.append (reverse_append value prefix) suffix).
  { intros xs. induction xs as [|byte rest IH]; intros prefix tail; cbn.
    - reflexivity.
    - exact (IH (String byte prefix) tail). }
  unfold reverse. apply (H value EmptyString suffix).
Qed.

Lemma reverse_cons (byte : ascii) (rest : string) :
  reverse (String byte rest) =
  Strings.String.append (reverse rest) (String byte EmptyString).
Proof.
  unfold reverse at 1. cbn. apply reverse_append_spec.
Qed.

Lemma reverse_length (value : string) :
  Strings.String.length (reverse value) = Strings.String.length value.
Proof.
  assert (H : forall value suffix,
    Strings.String.length (reverse_append value suffix) =
    (Strings.String.length value + Strings.String.length suffix)%nat).
  { intros xs. induction xs as [|byte rest IH]; intros suffix; cbn.
    - reflexivity.
    - rewrite IH. cbn. lia. }
  unfold reverse. rewrite H. cbn. lia.
Qed.

Lemma of_bits_append (left right : string) :
  OCamlZ.of_bits (Strings.String.append left right) =
  OCamlZ.of_bits left +
    256 ^ Z.of_nat (Strings.String.length left) * OCamlZ.of_bits right.
Proof.
  induction left as [|byte rest IH].
  - change (OCamlZ.of_bits right = 0 + 1 * OCamlZ.of_bits right). ring.
  - change (Z.of_N (N_of_ascii byte) +
      256 * OCamlZ.of_bits (Strings.String.append rest right) =
      Z.of_N (N_of_ascii byte) + 256 * OCamlZ.of_bits rest +
      256 ^ Z.of_nat (S (Strings.String.length rest)) * OCamlZ.of_bits right).
    rewrite IH, Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
Qed.

Lemma of_bits_bounds (value : string) :
  0 <= OCamlZ.of_bits value < 256 ^ Z.of_nat (Strings.String.length value).
Proof.
  induction value as [|byte rest IH].
  - cbn. lia.
  - change (0 <= Z.of_N (N_of_ascii byte) + 256 * OCamlZ.of_bits rest <
      256 ^ Z.of_nat (S (Strings.String.length rest))).
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    pose proof (N_ascii_bounded byte) as Hb.
    apply N2Z.inj_lt in Hb.
    pose proof (N2Z.is_nonneg (N_of_ascii byte)). nia.
Qed.

Lemma of_bytes_be_bounds
    (ascii_fallback : Unreachable ascii) (uint_fallback : Unreachable N)
    (value : string) :
  0 <= to_z (@of_bytes_be ascii_fallback uint_fallback value) <
    256 ^ Z.of_nat (Strings.String.length value).
Proof.
  unfold of_bytes_be, to_z.
  rewrite Z2N.id by apply of_bits_bounds.
  pose proof (of_bits_bounds (reverse value)).
  rewrite reverse_length in H. exact H.
Qed.

Lemma of_bytes_be_cons
    (ascii_fallback : Unreachable ascii) (uint_fallback : Unreachable N)
    (byte : ascii) (rest : string) :
  to_z (@of_bytes_be ascii_fallback uint_fallback (String byte rest)) =
    Z.of_N (N_of_ascii byte) * 256 ^ Z.of_nat (Strings.String.length rest) +
    to_z (@of_bytes_be ascii_fallback uint_fallback rest).
Proof.
  unfold of_bytes_be, to_z.
  repeat rewrite Z2N.id by apply of_bits_bounds.
  rewrite reverse_cons, of_bits_append, reverse_length.
  change (OCamlZ.of_bits (reverse rest) +
    256 ^ Z.of_nat (Strings.String.length rest) *
      (Z.of_N (N_of_ascii byte) + 256 * 0) =
    Z.of_N (N_of_ascii byte) * 256 ^ Z.of_nat (Strings.String.length rest) +
    OCamlZ.of_bits (reverse rest)). ring.
Qed.

Lemma significant_bits_nonzero (value : N) :
  value <> 0%N -> significant_bits value = 1 + Z.log2 (to_z value).
Proof.
  destruct value as [|p]; [contradiction|]. intros _.
  unfold significant_bits, to_z. rewrite N2Z.inj_succ.
  destruct p; cbn [N.eqb N.log2 Z.log2 Z.of_N]; lia.
Qed.

Lemma byte_power (length : nat) :
  256 ^ Z.of_nat length = 2 ^ (8 * Z.of_nat length).
Proof.
  rewrite Z.pow_mul_r by lia. reflexivity.
Qed.

Lemma significant_bytes_upper (value : N) (length : nat) :
  to_z value < 256 ^ Z.of_nat length ->
  significant_bytes value <= Z.of_nat length.
Proof.
  intros Hbound. destruct (N.eq_dec value 0) as [->|Hnonzero].
  - change (0 <= Z.of_nat length). lia.
  - assert (Hpositive : 0 < to_z value) by (unfold to_z; destruct value; lia).
    rewrite byte_power in Hbound.
    apply (proj1 (Z.log2_lt_pow2 _ _ Hpositive)) in Hbound.
    unfold significant_bytes.
    rewrite significant_bits_nonzero by exact Hnonzero.
    assert (Hdiv : (1 + Z.log2 (to_z value) + 7) / 8 < Z.of_nat length + 1).
    { apply Z.div_lt_upper_bound; lia. } lia.
Qed.

Lemma significant_bytes_lower (value : N) (length : nat) :
  256 ^ Z.of_nat length <= to_z value ->
  Z.of_nat length + 1 <= significant_bytes value.
Proof.
  intros Hbound.
  assert (Hpower : 0 < 256 ^ Z.of_nat length) by (apply Z.pow_pos_nonneg; lia).
  assert (Hpositive : 0 < to_z value) by lia.
  assert (Hnonzero : value <> 0%N) by (intro H; subst; discriminate Hpositive).
  rewrite byte_power in Hbound.
  apply (proj1 (Z.log2_le_pow2 _ _ Hpositive)) in Hbound.
  unfold significant_bytes.
  rewrite significant_bits_nonzero by exact Hnonzero.
  apply Z.div_le_lower_bound; lia.
Qed.

Lemma of_rlp_leading_zero
    (ascii_fallback : Unreachable ascii) (uint_fallback : Unreachable N)
    (rest : string) :
  @of_rlp ascii_fallback uint_fallback
    (MonadVM.Rlp.Bytes (String "000"%char rest)) = None.
Proof.
  unfold of_rlp. cbv beta iota zeta.
  match goal with
  | |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) eqn:Hsize
  end; [|reflexivity].
  apply Z.eqb_eq in Hsize.
  pose proof (of_bytes_be_bounds ascii_fallback uint_fallback rest) as Hrest.
  pose proof (of_bytes_be_cons ascii_fallback uint_fallback "000"%char rest)
    as Hcons.
  change (to_z (@of_bytes_be ascii_fallback uint_fallback
      (String "000"%char rest)) =
    0 * 256 ^ Z.of_nat (Strings.String.length rest) +
    to_z (@of_bytes_be ascii_fallback uint_fallback rest)) in Hcons.
  assert (Hupper : significant_bytes
    (@of_bytes_be ascii_fallback uint_fallback (String "000"%char rest)) <=
    Z.of_nat (Strings.String.length rest)).
  { apply significant_bytes_upper. lia. }
  unfold OCamlString.length in Hsize.
  cbn [Strings.String.length] in Hsize.
  rewrite Nat2Z.inj_succ in Hsize. lia.
Qed.

Lemma significant_bytes_nonzero_prefix
    (ascii_fallback : Unreachable ascii) (uint_fallback : Unreachable N)
    (byte : ascii) (rest : string) :
  byte <> "000"%char ->
  significant_bytes (@of_bytes_be ascii_fallback uint_fallback
    (String byte rest)) = Z.of_nat (S (Strings.String.length rest)).
Proof.
  intro Hbyte.
  assert (Hcode : N_of_ascii byte <> 0%N).
  { intro H. apply Hbyte.
    rewrite <- (ascii_N_embedding byte), H. reflexivity. }
  assert (Hcodepos : 0 < Z.of_N (N_of_ascii byte)).
  { pose proof (N2Z.is_nonneg (N_of_ascii byte)).
    destruct (N_of_ascii byte); cbn in *; lia. }
  pose proof (of_bytes_be_bounds ascii_fallback uint_fallback rest) as Hrest.
  pose proof (of_bytes_be_bounds ascii_fallback uint_fallback (String byte rest))
    as Hwhole.
  pose proof (significant_bytes_upper _ _ (proj2 Hwhole)) as Hupper.
  assert (Hlower : Z.of_nat (Strings.String.length rest) + 1 <=
    significant_bytes (@of_bytes_be ascii_fallback uint_fallback
      (String byte rest))).
  { apply significant_bytes_lower. rewrite of_bytes_be_cons.
    assert (0 < 256 ^ Z.of_nat (Strings.String.length rest)) by
      (apply Z.pow_pos_nonneg; lia). nia. }
  cbn [Strings.String.length] in Hupper.
  rewrite Nat2Z.inj_succ in *. lia.
Qed.

Lemma of_rlp_nonzero_prefix
    (ascii_fallback : Unreachable ascii) (uint_fallback : Unreachable N)
    (byte : ascii) (rest : string) :
  byte <> "000"%char ->
  @of_rlp ascii_fallback uint_fallback (MonadVM.Rlp.Bytes (String byte rest)) =
    Some (@of_bytes_be ascii_fallback uint_fallback (String byte rest)).
Proof.
  intro Hbyte. unfold of_rlp. cbv beta iota zeta.
  rewrite significant_bytes_nonzero_prefix by exact Hbyte.
  unfold OCamlString.length. cbn [Strings.String.length].
  rewrite Z.eqb_refl. reflexivity.
Qed.

Theorem of_rlp_bytes_spec
    (ascii_fallback : Unreachable ascii) (uint_fallback : Unreachable N)
    (bytes : string) :
  @of_rlp ascii_fallback uint_fallback (MonadVM.Rlp.Bytes bytes) =
    match bytes with
    | EmptyString => Some 0%N
    | String byte _ =>
        if Ascii.eqb byte "000"%char then None
        else Some (@of_bytes_be ascii_fallback uint_fallback bytes)
    end.
Proof.
  destruct bytes as [|byte rest]; [reflexivity|].
  destruct (Ascii.eqb byte "000"%char) eqn:Hbyte.
  - apply Ascii.eqb_eq in Hbyte. subst byte. apply of_rlp_leading_zero.
  - apply Ascii.eqb_neq in Hbyte. apply of_rlp_nonzero_prefix. exact Hbyte.
Qed.

Theorem of_rlp_fallback_independent
    (ascii_left ascii_right : Unreachable ascii)
    (uint_left uint_right : Unreachable N) (value : MonadVM.Rlp.t) :
  @of_rlp ascii_left uint_left value = @of_rlp ascii_right uint_right value.
Proof.
  reflexivity.
Qed.

(** The encoder emits exactly the significant bytes and is inverse to the
    decoder on its accepted domain. The fallback instances on the two sides
    may differ. *)

Lemma reverse_involutive (value : string) : reverse (reverse value) = value.
Proof.
  assert (H : forall value prefix suffix,
    reverse_append (reverse_append value prefix) suffix =
    reverse_append prefix (Strings.String.append value suffix)).
  { intros xs. induction xs as [|byte rest IH]; intros prefix suffix; cbn.
    - reflexivity.
    - rewrite IH. reflexivity. }
  unfold reverse. rewrite H. cbn. induction value; cbn; congruence.
Qed.

Lemma to_bits_bytes_length (count : nat) (value : Z) :
  Strings.String.length (OCamlZ.to_bits_bytes count value) = count.
Proof.
  revert value. induction count; intros value; cbn; congruence.
Qed.

Lemma of_bits_to_bits_bytes (count : nat) (value : Z) :
  0 <= value < 256 ^ Z.of_nat count ->
  OCamlZ.of_bits (OCamlZ.to_bits_bytes count value) = value.
Proof.
  revert value. induction count as [|count IH]; intros value Hbound.
  - cbn in Hbound. assert (value = 0) by lia. subst. reflexivity.
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hbound by lia.
    assert (Hmod : 0 <= value mod 256 < 256) by
      (apply Z.mod_pos_bound; lia).
    assert (Hquot : 0 <= value / 256 < 256 ^ Z.of_nat count).
    { split.
      - apply Z.div_pos; lia.
      - apply Z.div_lt_upper_bound; lia. }
    change (Z.of_N (N_of_ascii (ascii_of_N (Z.to_N (value mod 256)))) +
      256 * OCamlZ.of_bits (OCamlZ.to_bits_bytes count (value / 256)) = value).
    rewrite N_ascii_embedding.
    2: { apply N2Z.inj_lt. rewrite Z2N.id by lia. exact (proj2 Hmod). }
    rewrite Z2N.id by lia. rewrite IH by exact Hquot.
    pose proof (Z.div_mod value 256 ltac:(lia)). lia.
Qed.

Lemma numbits_to_z (value : N) :
  OCamlZ.numbits (to_z value) = significant_bits value.
Proof.
  destruct value as [|p]; [reflexivity|].
  rewrite significant_bits_nonzero by discriminate.
  change (Z.succ (Z.log2 (Z.pos p)) = 1 + Z.log2 (Z.pos p)). lia.
Qed.

Lemma significant_bytes_nonnegative (value : N) :
  0 <= significant_bytes value.
Proof.
  unfold significant_bytes. apply Z.div_pos; [|lia].
  unfold significant_bits. destruct (N.eqb value 0); [lia|].
  pose proof (N2Z.is_nonneg (N.succ (N.log2 value))). lia.
Qed.

Lemma significant_bytes_capacity (value : N) :
  to_z value < 256 ^ significant_bytes value.
Proof.
  destruct (N.eq_dec value 0) as [->|Hnonzero]; [reflexivity|].
  assert (Hpositive : 0 < to_z value) by (unfold to_z; destruct value; lia).
  assert (Hpow : 256 ^ significant_bytes value =
    2 ^ (8 * significant_bytes value)).
  { rewrite Z.pow_mul_r by (try lia; apply significant_bytes_nonnegative).
    reflexivity. }
  rewrite Hpow. apply (proj2 (Z.log2_lt_pow2 _ _ Hpositive)).
  unfold significant_bytes.
  rewrite significant_bits_nonzero by exact Hnonzero.
  pose proof (Z.div_mod (1 + Z.log2 (to_z value) + 7) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (1 + Z.log2 (to_z value) + 7) 8 ltac:(lia)). lia.
Qed.

Theorem of_bytes_be_to_bytes_be
    (bytes_fallback : Unreachable string)
    (encoder_ascii decoder_ascii : Unreachable ascii)
    (uint_fallback : Unreachable N) (value : N) :
  @of_bytes_be decoder_ascii uint_fallback
    (@to_bytes_be bytes_fallback encoder_ascii value) = value.
Proof.
  unfold of_bytes_be, to_bytes_be. rewrite reverse_involutive.
  unfold OCamlZ.to_bits. rewrite Z.abs_eq by apply to_z_nonnegative.
  rewrite numbits_to_z.
  change (Z.to_N (OCamlZ.of_bits (OCamlZ.to_bits_bytes
    (Z.to_nat (significant_bytes value)) (to_z value))) = value).
  rewrite of_bits_to_bits_bytes.
  - apply N2Z.id.
  - rewrite Z2Nat.id by apply significant_bytes_nonnegative.
    split; [apply to_z_nonnegative|apply significant_bytes_capacity].
Qed.

Theorem to_bytes_be_length
    (bytes_fallback : Unreachable string) (ascii_fallback : Unreachable ascii)
    (value : N) :
  OCamlString.length (@to_bytes_be bytes_fallback ascii_fallback value) =
    significant_bytes value.
Proof.
  unfold OCamlString.length, to_bytes_be. rewrite reverse_length.
  unfold OCamlZ.to_bits. rewrite Z.abs_eq by apply to_z_nonnegative.
  rewrite numbits_to_z, to_bits_bytes_length.
  apply Z2Nat.id. apply significant_bytes_nonnegative.
Qed.

Theorem of_rlp_to_rlp
    (bytes_fallback : Unreachable string)
    (encoder_ascii decoder_ascii : Unreachable ascii)
    (uint_fallback : Unreachable N) (value : N) :
  @of_rlp decoder_ascii uint_fallback
    (@to_rlp bytes_fallback encoder_ascii value) = Some value.
Proof.
  unfold to_rlp, of_rlp. cbv beta iota zeta.
  rewrite of_bytes_be_to_bytes_be, to_bytes_be_length, Z.eqb_refl. reflexivity.
Qed.

Lemma of_bits_same_length_injective (left right : string) :
  Strings.String.length left = Strings.String.length right ->
  OCamlZ.of_bits left = OCamlZ.of_bits right -> left = right.
Proof.
  revert right. induction left as [|byte rest IH];
    intros [|other tail] Hlength Hvalue; try discriminate; [reflexivity|].
  cbn [Strings.String.length] in Hlength. injection Hlength as Hlength.
  change (Z.of_N (N_of_ascii byte) + 256 * OCamlZ.of_bits rest =
    Z.of_N (N_of_ascii other) + 256 * OCamlZ.of_bits tail) in Hvalue.
  pose proof (N_ascii_bounded byte) as Hbyte.
  pose proof (N_ascii_bounded other) as Hother.
  apply N2Z.inj_lt in Hbyte. apply N2Z.inj_lt in Hother.
  pose proof (N2Z.is_nonneg (N_of_ascii byte)).
  pose proof (N2Z.is_nonneg (N_of_ascii other)).
  assert (Htail : OCamlZ.of_bits rest = OCamlZ.of_bits tail) by lia.
  assert (Hcode : Z.of_N (N_of_ascii byte) = Z.of_N (N_of_ascii other)) by lia.
  apply N2Z.inj in Hcode.
  assert (Hchar : byte = other).
  { rewrite <- (ascii_N_embedding byte), <- (ascii_N_embedding other), Hcode.
    reflexivity. }
  subst other. f_equal. apply IH; assumption.
Qed.

Lemma of_bytes_be_same_length_injective
    (ascii_fallback : Unreachable ascii) (uint_fallback : Unreachable N)
    (left right : string) :
  Strings.String.length left = Strings.String.length right ->
  @of_bytes_be ascii_fallback uint_fallback left =
    @of_bytes_be ascii_fallback uint_fallback right -> left = right.
Proof.
  intros Hlength Hvalue. apply (f_equal Z.of_N) in Hvalue.
  unfold of_bytes_be in Hvalue.
  repeat rewrite Z2N.id in Hvalue by apply of_bits_bounds.
  assert (Hreverse : reverse left = reverse right).
  { apply of_bits_same_length_injective.
    - now repeat rewrite reverse_length.
    - exact Hvalue. }
  apply (f_equal reverse) in Hreverse.
  now repeat rewrite reverse_involutive in Hreverse.
Qed.

Theorem to_rlp_of_rlp
    (bytes_fallback : Unreachable string)
    (encoder_ascii decoder_ascii : Unreachable ascii)
    (uint_fallback : Unreachable N) (encoded : MonadVM.Rlp.t) (decoded : N) :
  @of_rlp decoder_ascii uint_fallback encoded = Some decoded ->
  @to_rlp bytes_fallback encoder_ascii decoded = encoded.
Proof.
  destruct encoded as [bytes|elements]; intros Hdecode; [|discriminate].
  unfold of_rlp in Hdecode. cbv beta iota zeta in Hdecode.
  destruct (Z.eqb (significant_bytes (@of_bytes_be decoder_ascii uint_fallback
    bytes)) (OCamlString.length bytes)) eqn:Hsize; [|discriminate].
  injection Hdecode as Hvalue. subst decoded. unfold to_rlp. f_equal.
  apply (of_bytes_be_same_length_injective decoder_ascii uint_fallback).
  - apply Nat2Z.inj.
    change (OCamlString.length (@to_bytes_be bytes_fallback encoder_ascii
      (@of_bytes_be decoder_ascii uint_fallback bytes)) =
      OCamlString.length bytes).
    rewrite to_bytes_be_length. now apply Z.eqb_eq in Hsize.
  - apply of_bytes_be_to_bytes_be.
Qed.
