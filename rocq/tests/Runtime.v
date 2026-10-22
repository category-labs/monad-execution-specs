(** Predicative regression tests for the patched compatibility library.
    This file and all its dependencies are built without impredicative Set. *)
From Stdlib Require Import String.
Require Import RocqOfOCaml.Basics.
Require Import MonadVM.State.

Definition package := {A : Set @ (A * (A -> nat))%type}.

Definition observe (value : package) : nat :=
  let 'existS _ _ (element, read) := value in read element.

Definition sample : package :=
  existS _ nat (3%nat, fun x => x).

Example module_pack_unpack : observe sample = 3%nat.
Proof. reflexivity. Qed.

Definition sigma_sample : {A : Set & (A * (A -> nat))%type} :=
  existT _ nat (3%nat, fun x => x).

Example pack_conversion : observe (pack sigma_sample) = 3%nat.
Proof. reflexivity. Qed.

(** The payload family need not be Set-valued, and [pack] must work at
    independently chosen witness and payload universes. *)
Polymorphic Definition repack@{u v} {A : Type@{u}} {P : A -> Type@{v}}
    (value : {a : A & P a}) : {a : A @ P a} := pack value.

Definition higher_package : {A : Type @ A} := existS _ Set nat.

Definition variant_tag (value : Variant.t) : string :=
  match value with Variant.Build tag _ _ => tag end.

Example variant_payload :
  variant_tag (Variant.Build "Count"%string nat 3%nat) = "Count"%string.
Proof. reflexivity. Qed.

Definition exception_tag (value : extensible_type) : string :=
  match value with Build_extensible tag _ _ => tag end.

Example exception_payload :
  exception_tag (Build_extensible "Count"%string nat 3%nat) = "Count"%string.
Proof. reflexivity. Qed.

(** Raising the packages does not force ordinary project data out of Set. *)
Check (MonadVM.State.WorldState.t : Set).

Print Assumptions module_pack_unpack.
Print Assumptions pack_conversion.
Print Assumptions variant_payload.
Print Assumptions exception_payload.
