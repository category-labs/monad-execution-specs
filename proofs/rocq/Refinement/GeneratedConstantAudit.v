From Stdlib Require Import ZArith NArith.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import MonadVM.Crypto.
Require Import MonadVM.Ec.Alt_bn128.
Require Import MonadVM.Ec.Bls12_381.
Require Import MonadVM.Ec.Secp256r1.
Require Import MonadVM.Numeric.
Require Import MonadVM.Support.UintN.

(** These generated top-level values must reduce to their native Zarith
    integers regardless of the exceptional-value parameters in their types. *)

Lemma secp256k1_field_prime
    `{UZ : RocqOfOCaml.Basics.Unreachable Z.t}
    `{UW : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t} :
  MonadVM.Crypto.secp256k1p =
  115792089237316195423570985008687907853269984665640564039457584007908834671663%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma secp256k1_group_order
    `{UZ : RocqOfOCaml.Basics.Unreachable Z.t}
    `{UW : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t} :
  MonadVM.Crypto.secp256k1n =
  115792089237316195423570985008687907852837564279074904382605163141518161494337%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma secp256r1_field_prime
    `{UZ : RocqOfOCaml.Basics.Unreachable Z.t}
    `{UN : RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t} :
  MonadVM.Ec.Secp256r1.p_value =
  115792089210356248762697446949407573530086143415290314195533631308867097853951%N.
Proof. vm_compute. reflexivity. Qed.

Lemma secp256r1_group_order
    `{UZ : RocqOfOCaml.Basics.Unreachable Z.t}
    `{UN : RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t} :
  MonadVM.Ec.Secp256r1.q_value =
  115792089210356248762697446949407573529996955224135760342422259061068512044369%N.
Proof. vm_compute. reflexivity. Qed.

Lemma alt_bn128_field_prime
    `{UZ : RocqOfOCaml.Basics.Unreachable Z.t}
    `{UN : RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t} :
  MonadVM.Ec.Alt_bn128.p_value =
  21888242871839275222246405745257275088696311157297823662689037894645226208583%N.
Proof. vm_compute. reflexivity. Qed.

Lemma alt_bn128_group_order
    `{UZ : RocqOfOCaml.Basics.Unreachable Z.t}
    `{UN : RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t} :
  MonadVM.Ec.Alt_bn128.q_value =
  21888242871839275222246405745257275088548364400416034343698204186575808495617%N.
Proof. vm_compute. reflexivity. Qed.

Lemma bls12_381_field_prime
    `{UZ : RocqOfOCaml.Basics.Unreachable Z.t}
    `{UN : RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t} :
  MonadVM.Ec.Bls12_381.p_value =
  4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787%N.
Proof. vm_compute. reflexivity. Qed.

Lemma bls12_381_group_order
    `{UZ : RocqOfOCaml.Basics.Unreachable Z.t}
    `{UN : RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t} :
  MonadVM.Ec.Bls12_381.q_value =
  52435875175126190479447740508185965837690552500527637822603658699938581184513%N.
Proof. vm_compute. reflexivity. Qed.
