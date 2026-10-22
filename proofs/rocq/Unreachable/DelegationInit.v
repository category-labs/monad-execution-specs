From Stdlib Require Import Bool String ZArith Lia.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import RocqOfOCaml.Unreachable.StringBounds.
Require Import MonadVM.Byte_string.
Require Import MonadVM.Delegation.

Local Open Scope Z_scope.

(** The generated module initializer checks the EIP-7702 delegation prefix
    plus the concrete B20 address width. Both values are fixed in the
    generated code, so this particular typed exceptional call is avoided
    regardless of the supplied fallback instances. *)
Lemma generated_b20_byte_width_is_20
    (UI : RocqOfOCaml.Basics.Unreachable RocqOfOCaml.Basics.int) :
  @MonadVM.Byte_string.B20.byte_width UI = 20%Z.
Proof. reflexivity. Qed.

Lemma generated_delegation_prefix_length_is_3 :
  MonadVM.Byte_string.Bytes.length
    MonadVM.Delegation.eoa_delegation_prefix = 3.
Proof. reflexivity. Qed.

Lemma generated_delegated_code_length_is_23
    (UI : RocqOfOCaml.Basics.Unreachable RocqOfOCaml.Basics.int) :
  @MonadVM.Delegation.eoa_delegated_code_length UI = 23%Z.
Proof. reflexivity. Qed.

Lemma generated_delegation_validation_length
    (UI : RocqOfOCaml.Basics.Unreachable RocqOfOCaml.Basics.int)
    (code : MonadVM.Byte_string.Bytes.t) :
  @MonadVM.Delegation.is_valid_delegation UI code = true ->
  RocqOfOCaml.OCamlString.length code = 23%Z.
Proof.
  unfold MonadVM.Delegation.is_valid_delegation.
  rewrite generated_delegated_code_length_is_23.
  intros Hvalid.
  apply andb_true_iff in Hvalid as [Hlength _].
  unfold equiv_decb in Hlength.
  destruct (equiv_dec (MonadVM.Byte_string.Bytes.length code) 23%Z)
    as [Heq | Hneq].
  - exact Heq.
  - discriminate Hlength.
Qed.

Lemma generated_delegation_validation_independent
    (UI1 UI2 : RocqOfOCaml.Basics.Unreachable RocqOfOCaml.Basics.int)
    (code : MonadVM.Byte_string.Bytes.t) :
  @MonadVM.Delegation.is_valid_delegation UI1 code =
  @MonadVM.Delegation.is_valid_delegation UI2 code.
Proof. reflexivity. Qed.

Lemma generated_b20_of_bytes_exn_succeeds
    (UA : RocqOfOCaml.Basics.Unreachable MonadVM.Byte_string.B20.t)
    (UI : RocqOfOCaml.Basics.Unreachable RocqOfOCaml.Basics.int)
    (bytes : MonadVM.Byte_string.Bytes.t) :
  RocqOfOCaml.OCamlString.length bytes = 20%Z ->
  @MonadVM.Byte_string.B20.of_bytes_exn UA UI bytes = bytes.
Proof.
  intros Hlength.
  cbn.
  unfold MonadVM.Byte_string.Fixed.of_bytes_exn,
    MonadVM.Byte_string.Fixed.of_bytes.
  cbn.
  unfold MonadVM.Byte_string.Fixed.Impl.of_bytes.
  rewrite Hlength.
  reflexivity.
Qed.

Lemma generated_delegated_address_avoids_fallback
    (US : RocqOfOCaml.Basics.Unreachable MonadVM.Byte_string.Bytes.t)
    (UA : RocqOfOCaml.Basics.Unreachable MonadVM.Delegation.Address.t)
    (UI : RocqOfOCaml.Basics.Unreachable RocqOfOCaml.Basics.int)
    (code : MonadVM.Byte_string.Bytes.t) :
  @MonadVM.Delegation.get_delegated_address US UA UI code =
    if @MonadVM.Delegation.is_valid_delegation UI code
    then Some (substring 3 20 code)
    else None.
Proof.
  unfold MonadVM.Delegation.get_delegated_address.
  destruct (@MonadVM.Delegation.is_valid_delegation UI code) eqn:Hvalid.
  - pose proof (generated_delegation_validation_length UI code Hvalid)
      as Hlength.
    assert (Hpayload :
      RocqOfOCaml.OCamlString.length
        (@MonadVM.Byte_string.Bytes.sub UA code 3 20) = 20).
    { change (RocqOfOCaml.OCamlString.length
        (@RocqOfOCaml.OCamlString.sub UA code 3 20) = 20).
      apply sub_length_in_bounds; lia. }
    rewrite generated_delegation_prefix_length_is_3.
    rewrite (generated_b20_byte_width_is_20 UI).
    change (Some (@MonadVM.Byte_string.B20.of_bytes_exn UA UI
      (@MonadVM.Byte_string.Bytes.sub UA code 3 20)) =
      Some (substring 3 20 code)).
    rewrite (generated_b20_of_bytes_exn_succeeds UA UI _ Hpayload).
    change (Some (@RocqOfOCaml.OCamlString.sub UA code 3 20) =
      Some (substring 3 20 code)).
    rewrite (@sub_in_bounds UA code 3 20) by lia.
    reflexivity.
  - reflexivity.
Qed.

Lemma generated_delegated_address_independent
    (US1 US2 : RocqOfOCaml.Basics.Unreachable MonadVM.Byte_string.Bytes.t)
    (UA1 UA2 : RocqOfOCaml.Basics.Unreachable MonadVM.Delegation.Address.t)
    (UI1 UI2 : RocqOfOCaml.Basics.Unreachable RocqOfOCaml.Basics.int)
    (code : MonadVM.Byte_string.Bytes.t) :
  @MonadVM.Delegation.get_delegated_address US1 UA1 UI1 code =
  @MonadVM.Delegation.get_delegated_address US2 UA2 UI2 code.
Proof.
  rewrite !generated_delegated_address_avoids_fallback.
  rewrite (generated_delegation_validation_independent UI1 UI2 code).
  reflexivity.
Qed.

(** The fixed 20-byte zero address also avoids the string-initialization
    fallback. The delegated-code encoder only observes this value and its
    input address, so it is independent of its fallback instances. *)
Lemma generated_b20_zeros_independent
    (UA1 UA2 : RocqOfOCaml.Basics.Unreachable MonadVM.Byte_string.B20.t)
    (UI1 UI2 : RocqOfOCaml.Basics.Unreachable RocqOfOCaml.Basics.int) :
  @MonadVM.Byte_string.B20.zeros UA1 UI1 =
  @MonadVM.Byte_string.B20.zeros UA2 UI2.
Proof. vm_compute. reflexivity. Qed.

Lemma generated_delegation_code_independent
    (UA1 UA2 : RocqOfOCaml.Basics.Unreachable MonadVM.Delegation.Address.t)
    (UI1 UI2 : RocqOfOCaml.Basics.Unreachable RocqOfOCaml.Basics.int)
    (address : MonadVM.Delegation.Address.t) :
  @MonadVM.Delegation.delegation_code UA1 UI1 address =
  @MonadVM.Delegation.delegation_code UA2 UI2 address.
Proof.
  unfold MonadVM.Delegation.delegation_code.
  rewrite (generated_b20_zeros_independent UA1 UA2 UI1 UI2).
  reflexivity.
Qed.

(** The result type is [unit], so equality with [tt] alone would not show
    that the exceptional branch is avoided.  The guard is the evidence. *)
Lemma generated_delegation_init_guard_is_true
    (UI : RocqOfOCaml.Basics.Unreachable RocqOfOCaml.Basics.int) :
  equiv_decb (@MonadVM.Delegation.eoa_delegated_code_length UI) 23 = true.
Proof.
  rewrite generated_delegated_code_length_is_23.
  reflexivity.
Qed.

Lemma generated_delegation_init_avoids_fallback
    (UU : RocqOfOCaml.Basics.Unreachable unit)
    (UI : RocqOfOCaml.Basics.Unreachable RocqOfOCaml.Basics.int) :
  @MonadVM.Delegation.init_module UU UI = tt.
Proof.
  unfold MonadVM.Delegation.init_module.
  rewrite (generated_delegation_init_guard_is_true UI).
  reflexivity.
Qed.

Print Assumptions generated_delegated_code_length_is_23.
Print Assumptions generated_delegation_init_guard_is_true.
Print Assumptions generated_delegation_init_avoids_fallback.
Print Assumptions generated_delegated_address_avoids_fallback.
Print Assumptions generated_delegated_address_independent.
Print Assumptions generated_delegation_code_independent.
