From Stdlib Require Import Strings.String Strings.Ascii List.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import MonadVM.Precompiles.
Require Import MonadVM.Precompiles.Alt_bn128.
Require Import MonadVM.Precompiles.Bls12_381.
Require Import MonadVM.Precompiles.Modexp.
Require Import MonadVM.Precompiles.Point_evaluation.
Require Import MonadVM.Precompiles.Secp256r1.
Require Import MonadVM.Chain.Ethereum.
Require Import MonadVM.Byte_string.

Import ListNotations.

(** The fixed precompile addresses are the 20-byte encodings of 1 through 17,
    plus 256 for secp256r1. Every lemma below computes the generated parser
    result under arbitrary typed fallbacks. *)
Definition address_bytes (last : nat) : string :=
  string_of_list_ascii
    (repeat (ascii_of_nat 0) 19 ++ [ascii_of_nat last]).

Definition address_bytes_256 : string :=
  string_of_list_ascii
    (repeat (ascii_of_nat 0) 18 ++ [ascii_of_nat 1; ascii_of_nat 0]).

(** The source table names each of these fixed addresses once. *)
Lemma fixed_precompile_addresses_distinct :
  NoDup (map address_bytes (seq 1 17) ++ [address_bytes_256]).
Proof.
  vm_compute.
  repeat constructor; simpl; intuition discriminate.
Qed.

Section AddressValues.
Context
    (u0 : RocqOfOCaml.Basics.Unreachable (RocqOfOCaml.OCamlIarray.t int))
    (u1 : RocqOfOCaml.Basics.Unreachable MonadVM.Chain.Ethereum.Address.t)
    (u2 : RocqOfOCaml.Basics.Unreachable MonadVM.Byte_string.Bytes.t)
    (u3 : RocqOfOCaml.Basics.Unreachable unit)
    (u4 : RocqOfOCaml.Basics.Unreachable int)
    (u5 : RocqOfOCaml.Basics.Unreachable ascii).

Lemma ecrecover_address_value :
  @MonadVM.Precompiles.ecrecover_address u0 u1 u2 u3 u4 u5 =
    address_bytes 1.
Proof. vm_compute. reflexivity. Qed.

Lemma sha256_address_value :
  @MonadVM.Precompiles.sha256_address u0 u1 u2 u3 u4 u5 =
    address_bytes 2.
Proof. vm_compute. reflexivity. Qed.

Lemma ripemd160_address_value :
  @MonadVM.Precompiles.ripemd160_address u0 u1 u2 u3 u4 u5 =
    address_bytes 3.
Proof. vm_compute. reflexivity. Qed.

Lemma identity_address_value :
  @MonadVM.Precompiles.identity_address u0 u1 u2 u3 u4 u5 =
    address_bytes 4.
Proof. vm_compute. reflexivity. Qed.

Lemma blake2f_address_value :
  @MonadVM.Precompiles.blake2f_address u0 u1 u2 u3 u4 u5 =
    address_bytes 9.
Proof. vm_compute. reflexivity. Qed.

Lemma alt_bn128_add_address_value :
  @MonadVM.Precompiles.Alt_bn128.add_address u0 u1 u2 u3 u4 u5 =
    address_bytes 6.
Proof. vm_compute. reflexivity. Qed.

Lemma alt_bn128_mul_address_value :
  @MonadVM.Precompiles.Alt_bn128.mul_address u0 u1 u2 u3 u4 u5 =
    address_bytes 7.
Proof. vm_compute. reflexivity. Qed.

Lemma alt_bn128_pairing_check_address_value :
  @MonadVM.Precompiles.Alt_bn128.pairing_check_address u0 u1 u2 u3 u4 u5 =
    address_bytes 8.
Proof. vm_compute. reflexivity. Qed.

Lemma point_evaluation_address_value :
  @MonadVM.Precompiles.Point_evaluation.address u0 u1 u2 u3 u4 u5 =
    address_bytes 10.
Proof. vm_compute. reflexivity. Qed.

Lemma bls12_381_g1_add_address_value :
  @MonadVM.Precompiles.Bls12_381.g1_add_address u0 u1 u2 u3 u4 u5 =
    address_bytes 11.
Proof. vm_compute. reflexivity. Qed.

Lemma bls12_381_g1_msm_address_value :
  @MonadVM.Precompiles.Bls12_381.g1_msm_address u0 u1 u2 u3 u4 u5 =
    address_bytes 12.
Proof. vm_compute. reflexivity. Qed.

Lemma bls12_381_g2_add_address_value :
  @MonadVM.Precompiles.Bls12_381.g2_add_address u0 u1 u2 u3 u4 u5 =
    address_bytes 13.
Proof. vm_compute. reflexivity. Qed.

Lemma bls12_381_g2_msm_address_value :
  @MonadVM.Precompiles.Bls12_381.g2_msm_address u0 u1 u2 u3 u4 u5 =
    address_bytes 14.
Proof. vm_compute. reflexivity. Qed.

Lemma bls12_381_pairing_check_address_value :
  @MonadVM.Precompiles.Bls12_381.pairing_check_address u0 u1 u2 u3 u4 u5 =
    address_bytes 15.
Proof. vm_compute. reflexivity. Qed.

Lemma bls12_381_map_fp_to_g1_address_value :
  @MonadVM.Precompiles.Bls12_381.map_fp_to_g1_address u0 u1 u2 u3 u4 u5 =
    address_bytes 16.
Proof. vm_compute. reflexivity. Qed.

Lemma bls12_381_map_fp2_to_g2_address_value :
  @MonadVM.Precompiles.Bls12_381.map_fp2_to_g2_address u0 u1 u2 u3 u4 u5 =
    address_bytes 17.
Proof. vm_compute. reflexivity. Qed.

Lemma secp256r1_address_value :
  @MonadVM.Precompiles.Secp256r1.address u0 u1 u2 u3 u4 u5 =
    address_bytes_256.
Proof. vm_compute. reflexivity. Qed.
End AddressValues.

Section ModexpAddressValue.
Context
  (fargs : MonadVM.Precompiles.Modexp.Make.FArgs)
  (u0 : RocqOfOCaml.Basics.Unreachable (RocqOfOCaml.OCamlIarray.t int))
  (u1 : RocqOfOCaml.Basics.Unreachable MonadVM.Chain.Ethereum.Address.t)
  (u2 : RocqOfOCaml.Basics.Unreachable MonadVM.Byte_string.Bytes.t)
  (u3 : RocqOfOCaml.Basics.Unreachable unit)
  (u4 : RocqOfOCaml.Basics.Unreachable int)
  (u5 : RocqOfOCaml.Basics.Unreachable ascii).

Lemma modexp_address_value :
  @MonadVM.Precompiles.Modexp.Make.address fargs u0 u1 u2 u3 u4 u5 =
    address_bytes 5.
Proof. vm_compute. reflexivity. Qed.
End ModexpAddressValue.

Print Assumptions ecrecover_address_value.
Print Assumptions sha256_address_value.
Print Assumptions ripemd160_address_value.
Print Assumptions identity_address_value.
Print Assumptions blake2f_address_value.
Print Assumptions alt_bn128_add_address_value.
Print Assumptions alt_bn128_mul_address_value.
Print Assumptions alt_bn128_pairing_check_address_value.
Print Assumptions point_evaluation_address_value.
Print Assumptions bls12_381_g1_add_address_value.
Print Assumptions bls12_381_g1_msm_address_value.
Print Assumptions bls12_381_g2_add_address_value.
Print Assumptions bls12_381_g2_msm_address_value.
Print Assumptions bls12_381_pairing_check_address_value.
Print Assumptions bls12_381_map_fp_to_g1_address_value.
Print Assumptions bls12_381_map_fp2_to_g2_address_value.
Print Assumptions secp256r1_address_value.
Print Assumptions modexp_address_value.
Print Assumptions fixed_precompile_addresses_distinct.
