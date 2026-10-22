From Stdlib Require Import Lists.List ZArith.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import MonadExecutionSpecs.Refinement.PrecompileAddressConstants.
Require Import MonadVM.Precompiles.
Require Import MonadVM.Chain.Ethereum.
Import ListNotations.

(** This finite key list is established for the generated address definitions
    in [PrecompileAddressConstants]. The map lemmas quantify over all values,
    so they never evaluate a precompile implementation. *)
Definition fixed_keys :=
  map address_bytes (seq 1 17) ++ [address_bytes_256].

Lemma fixed_map_cardinal_any_values (a : Set) (values : list a) :
  Datatypes.length values = 18%nat ->
  MonadVM.Chain.Ethereum.Address.Map.cardinal
    (MonadVM.Chain.Ethereum.Address.Map.of_list
      (combine fixed_keys values)) = 18%Z.
Proof.
  intro Hlength.
  do 18 (destruct values as [| ? values]; [discriminate Hlength|]).
  destruct values as [| ? ?]; [| discriminate Hlength].
  vm_compute.
  reflexivity.
Qed.

Lemma combine_fst_snd {a : Set} (bindings : list (string * a)) :
  combine (map fst bindings) (map snd bindings) = bindings.
Proof.
  induction bindings as [| [key value] tail IH]; simpl; auto.
  now rewrite IH.
Qed.

Lemma cardinal_with_fixed_keys {a : Set} (bindings : list (string * a)) :
  map fst bindings = fixed_keys ->
  MonadVM.Chain.Ethereum.Address.Map.cardinal
    (MonadVM.Chain.Ethereum.Address.Map.of_list bindings) = 18%Z.
Proof.
  intro Hkeys.
  rewrite <- (combine_fst_snd bindings).
  rewrite Hkeys.
  apply fixed_map_cardinal_any_values.
  assert (Hlength :
    Datatypes.length (map fst bindings) =
    Datatypes.length (map snd bindings)).
  { clear Hkeys.
    induction bindings as [| [key value] tail IH]; simpl; auto. }
  rewrite <- Hlength.
  rewrite Hkeys.
  vm_compute.
  reflexivity.
Qed.

Lemma fixed_map_keys_any_values (a : Set) (values : list a) :
  Datatypes.length values = 18%nat ->
  map fst
    (MonadVM.Chain.Ethereum.Address.Map.bindings
      (MonadVM.Chain.Ethereum.Address.Map.of_list
        (combine fixed_keys values))) = fixed_keys.
Proof.
  intro Hlength.
  do 18 (destruct values as [| ? values]; [discriminate Hlength|]).
  destruct values as [| ? ?]; [| discriminate Hlength].
  vm_compute.
  reflexivity.
Qed.

Lemma fixed_map_bindings_any_values (a : Set) (values : list a) :
  Datatypes.length values = 18%nat ->
  MonadVM.Chain.Ethereum.Address.Map.bindings
    (MonadVM.Chain.Ethereum.Address.Map.of_list
      (combine fixed_keys values)) = combine fixed_keys values.
Proof.
  intro Hlength.
  do 18 (destruct values as [| ? values]; [discriminate Hlength|]).
  destruct values as [| ? ?]; [| discriminate Hlength].
  vm_compute.
  reflexivity.
Qed.

Lemma binding_keys_with_fixed_keys {a : Set}
    (bindings : list (string * a)) :
  map fst bindings = fixed_keys ->
  map fst
    (MonadVM.Chain.Ethereum.Address.Map.bindings
      (MonadVM.Chain.Ethereum.Address.Map.of_list bindings)) = fixed_keys.
Proof.
  intro Hkeys.
  rewrite <- (combine_fst_snd bindings).
  rewrite Hkeys.
  apply fixed_map_keys_any_values.
  assert (Hlength :
    Datatypes.length (map fst bindings) =
    Datatypes.length (map snd bindings)).
  { clear Hkeys.
    induction bindings as [| [key value] tail IH]; simpl; auto. }
  rewrite <- Hlength.
  rewrite Hkeys.
  vm_compute.
  reflexivity.
Qed.

Lemma binding_pairs_with_fixed_keys {a : Set}
    (bindings : list (string * a)) :
  map fst bindings = fixed_keys ->
  MonadVM.Chain.Ethereum.Address.Map.bindings
    (MonadVM.Chain.Ethereum.Address.Map.of_list bindings) = bindings.
Proof.
  intro Hkeys.
  rewrite <- (combine_fst_snd bindings).
  rewrite Hkeys.
  apply fixed_map_bindings_any_values.
  assert (Hlength :
    Datatypes.length (map fst bindings) =
    Datatypes.length (map snd bindings)).
  { clear Hkeys.
    induction bindings as [| [key value] tail IH]; simpl; auto. }
  rewrite <- Hlength.
  rewrite Hkeys.
  vm_compute.
  reflexivity.
Qed.

Lemma fixed_map_find_opt_index (a : Set) (values : list a)
    (index : nat) (key : string) :
  Datatypes.length values = 18%nat ->
  nth_error fixed_keys index = Some key ->
  MonadVM.Chain.Ethereum.Address.Map.find_opt key
    (MonadVM.Chain.Ethereum.Address.Map.of_list
      (combine fixed_keys values)) = nth_error values index.
Proof.
  intros Hlength Hkey.
  do 18 (destruct values as [| ? values]; [discriminate Hlength|]).
  destruct values as [| ? ?]; [| discriminate Hlength].
  do 18 (destruct index as [| index];
    [cbn in Hkey; inversion Hkey; subst key; vm_compute; reflexivity |]).
  vm_compute in Hkey.
  destruct index; discriminate.
Qed.

Lemma binding_find_opt_index_with_fixed_keys {a : Set}
    (bindings : list (string * a)) (index : nat) (key : string) :
  map fst bindings = fixed_keys ->
  nth_error fixed_keys index = Some key ->
  MonadVM.Chain.Ethereum.Address.Map.find_opt key
    (MonadVM.Chain.Ethereum.Address.Map.of_list bindings) =
      nth_error (map snd bindings) index.
Proof.
  intros Hkeys Hindex.
  rewrite <- (combine_fst_snd bindings) at 1.
  rewrite Hkeys.
  apply fixed_map_find_opt_index.
  - assert (Hlength :
      Datatypes.length (map fst bindings) =
      Datatypes.length (map snd bindings)).
    { clear Hkeys Hindex.
      induction bindings as [| [key' value] tail IH]; simpl; auto. }
    rewrite <- Hlength.
    rewrite Hkeys.
    vm_compute.
    reflexivity.
  - exact Hindex.
Qed.

Lemma binding_find_opt_index_from_ordered_bindings {a : Set}
    (entries : list (string * a)) (index : nat) (key : string) :
  map fst entries = fixed_keys ->
  nth_error fixed_keys index = Some key ->
  MonadVM.Chain.Ethereum.Address.Map.find_opt key
    (MonadVM.Chain.Ethereum.Address.Map.of_list entries) =
    nth_error
      (map snd
        (MonadVM.Chain.Ethereum.Address.Map.bindings
          (MonadVM.Chain.Ethereum.Address.Map.of_list entries))) index.
Proof.
  intros Hkeys Hindex.
  rewrite (binding_pairs_with_fixed_keys entries Hkeys).
  now apply binding_find_opt_index_with_fixed_keys.
Qed.

Print Assumptions fixed_map_cardinal_any_values.
Print Assumptions cardinal_with_fixed_keys.
Print Assumptions fixed_map_keys_any_values.
Print Assumptions fixed_map_bindings_any_values.
Print Assumptions binding_keys_with_fixed_keys.
Print Assumptions binding_pairs_with_fixed_keys.
Print Assumptions fixed_map_find_opt_index.
Print Assumptions binding_find_opt_index_with_fixed_keys.
Print Assumptions binding_find_opt_index_from_ordered_bindings.

(** The binders and their explicit named applications mirror the generated
    [Precompiles.Make.ethereum_precompiles] signature. Explicit arguments prevent typeclass
    search among its many overlapping fallback types. *)
Lemma precompiles_table_shape
  `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable Z.t}
  `{_rocq_assumption_1 : RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}
  `{_rocq_assumption_2 :
    RocqOfOCaml.Basics.Unreachable
      MonadVM.Numeric.IntegerBase.(MonadVM.Numeric.Make.Make_result.t)}
  `{_rocq_assumption_3 :
    RocqOfOCaml.Basics.Unreachable
      (RocqOfOCaml.OCamlIarray.t
        (MonadVM.Ec.Bls12_381.F_p.t (_rocq_assumption_0 := _rocq_assumption_0) (_rocq_assumption_1 := _rocq_assumption_1) (_rocq_assumption_2 := _rocq_assumption_2)))}
  `{_rocq_assumption_4 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.Integer.t}
  `{_rocq_assumption_5 :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Bls12_381.F_p.t (_rocq_assumption_0 := _rocq_assumption_0) (_rocq_assumption_1 := _rocq_assumption_1) (_rocq_assumption_2 := _rocq_assumption_2))}
  `{_rocq_assumption_6 : RocqOfOCaml.Basics.Unreachable bool}
  `{_rocq_assumption_7 :
    RocqOfOCaml.Basics.Unreachable
      (RocqOfOCaml.OCamlIarray.t
        (MonadVM.Ec.Bls12_381.F_p.t (_rocq_assumption_0 := _rocq_assumption_0) (_rocq_assumption_1 := _rocq_assumption_1) (_rocq_assumption_2 := _rocq_assumption_2))
        *
        RocqOfOCaml.OCamlIarray.t
          (MonadVM.Ec.Bls12_381.F_p.t (_rocq_assumption_0 := _rocq_assumption_0) (_rocq_assumption_1 := _rocq_assumption_1) (_rocq_assumption_2 := _rocq_assumption_2)))}
  `{_rocq_assumption_8 :
    RocqOfOCaml.Basics.Unreachable
      (RocqOfOCaml.OCamlSeq.t
        (MonadVM.Ec.Bls12_381.F_p12.t (_rocq_assumption_0 := _rocq_assumption_0) (_rocq_assumption_1 := _rocq_assumption_1) (_rocq_assumption_2 := _rocq_assumption_2) (_rocq_assumption_3 := _rocq_assumption_3) (_rocq_assumption_4 := _rocq_assumption_4) (_rocq_assumption_5 := _rocq_assumption_5) (_rocq_assumption_6 := _rocq_assumption_6) (_rocq_assumption_7 := _rocq_assumption_7)))}
  `{_rocq_assumption_9 :
    RocqOfOCaml.Basics.Unreachable
      (RocqOfOCaml.OCamlIarray.t
        (MonadVM.Ec.Alt_bn128.F_p (_rocq_module_assumption_0 := _rocq_assumption_0) (_rocq_module_assumption_1 := _rocq_assumption_1) (_rocq_module_assumption_2 := _rocq_assumption_2)).(MonadVM.Ec.Algebra.Prime_field.Prime_field_result.t))}
  `{_rocq_assumption_10 :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Alt_bn128.F_p (_rocq_module_assumption_0 := _rocq_assumption_0) (_rocq_module_assumption_1 := _rocq_assumption_1) (_rocq_module_assumption_2 := _rocq_assumption_2)).(MonadVM.Ec.Algebra.Prime_field.Prime_field_result.t)}
  `{_rocq_assumption_11 :
    RocqOfOCaml.Basics.Unreachable
      (RocqOfOCaml.OCamlIarray.t
        (MonadVM.Ec.Alt_bn128.F_p (_rocq_module_assumption_0 := _rocq_assumption_0) (_rocq_module_assumption_1 := _rocq_assumption_1) (_rocq_module_assumption_2 := _rocq_assumption_2)).(MonadVM.Ec.Algebra.Prime_field.Prime_field_result.t)
        *
        RocqOfOCaml.OCamlIarray.t
          (MonadVM.Ec.Alt_bn128.F_p (_rocq_module_assumption_0 := _rocq_assumption_0) (_rocq_module_assumption_1 := _rocq_assumption_1) (_rocq_module_assumption_2 := _rocq_assumption_2)).(MonadVM.Ec.Algebra.Prime_field.Prime_field_result.t))}
  `{_rocq_assumption_12 :
    RocqOfOCaml.Basics.Unreachable
      (RocqOfOCaml.OCamlSeq.t
        (MonadVM.Ec.Alt_bn128.F_p12.t (_rocq_assumption_0 := _rocq_assumption_0) (_rocq_assumption_1 := _rocq_assumption_1) (_rocq_assumption_2 := _rocq_assumption_4) (_rocq_assumption_3 := _rocq_assumption_6) (_rocq_assumption_4 := _rocq_assumption_2) (_rocq_assumption_5 := _rocq_assumption_9) (_rocq_assumption_6 := _rocq_assumption_10) (_rocq_assumption_7 := _rocq_assumption_11)))}
  `{_rocq_assumption_13 :
    RocqOfOCaml.Basics.Unreachable
      (RocqOfOCaml.OCamlIarray.t
        (MonadVM.Ec.Bls12_381.F_p2.t (_rocq_assumption_0 := _rocq_assumption_0) (_rocq_assumption_1 := _rocq_assumption_1) (_rocq_assumption_2 := _rocq_assumption_4) (_rocq_assumption_3 := _rocq_assumption_2) (_rocq_assumption_4 := _rocq_assumption_5)))}
  `{_rocq_assumption_14 :
    RocqOfOCaml.Basics.Unreachable (RocqOfOCaml.OCamlIarray.t int)}
  `{_rocq_assumption_15 : RocqOfOCaml.Basics.Unreachable MonadVM.Uint64.t}
  `{_rocq_assumption_16 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U8.Repr.t}
  `{_rocq_assumption_17 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U8.t}
  `{_rocq_assumption_18 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U64.Repr.t}
  `{_rocq_assumption_19 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U64.t}
  `{_rocq_assumption_20 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U32.Repr.t}
  `{_rocq_assumption_21 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U32.t}
  `{_rocq_assumption_22 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.Repr.t}
  `{_rocq_assumption_23 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}
  `{_rocq_assumption_24 : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}
  `{_rocq_assumption_25 :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Bls12_381.C_2 (_rocq_module_assumption_0 := _rocq_assumption_0) (_rocq_module_assumption_1 := _rocq_assumption_1) (_rocq_module_assumption_2 := _rocq_assumption_4) (_rocq_module_assumption_3 := _rocq_assumption_2) (_rocq_module_assumption_4 := _rocq_assumption_5)).(MonadVM.Ec.Curve.Make.Make_result.t)}
  `{_rocq_assumption_26 :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Bls12_381.G_2 (_rocq_module_assumption_0 := _rocq_assumption_0) (_rocq_module_assumption_1 := _rocq_assumption_1) (_rocq_module_assumption_2 := _rocq_assumption_4) (_rocq_module_assumption_3 := _rocq_assumption_2) (_rocq_module_assumption_4 := _rocq_assumption_5) (_rocq_module_assumption_5 := _rocq_assumption_25)).(MonadVM.Ec.Curve.Make.Subgroup.Subgroup_result.t)}
  `{_rocq_assumption_27 :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Bls12_381.C_1 (_rocq_module_assumption_0 := _rocq_assumption_0) (_rocq_module_assumption_1 := _rocq_assumption_1) (_rocq_module_assumption_2 := _rocq_assumption_4) (_rocq_module_assumption_3 := _rocq_assumption_2) (_rocq_module_assumption_4 := _rocq_assumption_5)).(MonadVM.Ec.Curve.Make.Make_result.t)}
  `{_rocq_assumption_28 :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Bls12_381.G_1 (_rocq_module_assumption_0 := _rocq_assumption_0) (_rocq_module_assumption_1 := _rocq_assumption_1) (_rocq_module_assumption_2 := _rocq_assumption_4) (_rocq_module_assumption_3 := _rocq_assumption_2) (_rocq_module_assumption_4 := _rocq_assumption_5) (_rocq_module_assumption_5 := _rocq_assumption_27)).(MonadVM.Ec.Curve.Make.Subgroup.Subgroup_result.t)}
  `{_rocq_assumption_29 :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Bls12_381.F_p_SWU_curve.t (_rocq_assumption_0 := _rocq_assumption_0) (_rocq_assumption_1 := _rocq_assumption_1) (_rocq_assumption_2 := _rocq_assumption_4) (_rocq_assumption_3 := _rocq_assumption_2) (_rocq_assumption_4 := _rocq_assumption_5))}
  `{_rocq_assumption_30 :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Bls12_381.F_p2_SWU_curve.t (_rocq_assumption_0 := _rocq_assumption_0) (_rocq_assumption_1 := _rocq_assumption_1) (_rocq_assumption_2 := _rocq_assumption_4) (_rocq_assumption_3 := _rocq_assumption_2) (_rocq_assumption_4 := _rocq_assumption_5))}
  `{_rocq_assumption_31 :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Bls12_381.F_p2.t (_rocq_assumption_0 := _rocq_assumption_0) (_rocq_assumption_1 := _rocq_assumption_1) (_rocq_assumption_2 := _rocq_assumption_4) (_rocq_assumption_3 := _rocq_assumption_2) (_rocq_assumption_4 := _rocq_assumption_5))}
  `{_rocq_assumption_32 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Chain.Ethereum.Address.t}
  `{_rocq_assumption_33 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Byte_string.Bytes.t}
  `{_rocq_assumption_34 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Byte_string.B20.t}
  `{_rocq_assumption_35 : RocqOfOCaml.Basics.Unreachable unit}
  `{_rocq_assumption_36 : RocqOfOCaml.Basics.Unreachable string}
  `{_rocq_assumption_37 :
    RocqOfOCaml.Basics.Unreachable
      (option
        (MonadVM.Ec.Bls12_381.F_p.t (_rocq_assumption_0 := _rocq_assumption_0) (_rocq_assumption_1 := _rocq_assumption_1) (_rocq_assumption_2 := _rocq_assumption_2)))}
  `{_rocq_assumption_38 : RocqOfOCaml.Basics.Unreachable int}
  `{_rocq_assumption_39 : RocqOfOCaml.Basics.Unreachable ascii}
  `{_rocq_assumption_40 :
    RocqOfOCaml.Basics.Unreachable
      ((MonadVM.Ec.Bls12_381.F_p12.t (_rocq_assumption_0 := _rocq_assumption_0) (_rocq_assumption_1 := _rocq_assumption_1) (_rocq_assumption_2 := _rocq_assumption_2) (_rocq_assumption_3 := _rocq_assumption_3) (_rocq_assumption_4 := _rocq_assumption_4) (_rocq_assumption_5 := _rocq_assumption_5) (_rocq_assumption_6 := _rocq_assumption_6) (_rocq_assumption_7 := _rocq_assumption_7))
        *
        (MonadVM.Ec.Bls12_381.F_p12.t (_rocq_assumption_0 := _rocq_assumption_0) (_rocq_assumption_1 := _rocq_assumption_1) (_rocq_assumption_2 := _rocq_assumption_2) (_rocq_assumption_3 := _rocq_assumption_3) (_rocq_assumption_4 := _rocq_assumption_4) (_rocq_assumption_5 := _rocq_assumption_5) (_rocq_assumption_6 := _rocq_assumption_6) (_rocq_assumption_7 := _rocq_assumption_7)))}
  `{_rocq_assumption_41 :
    RocqOfOCaml.Basics.Unreachable
      ((MonadVM.Ec.Alt_bn128.F_p12.t (_rocq_assumption_0 := _rocq_assumption_0) (_rocq_assumption_1 := _rocq_assumption_1) (_rocq_assumption_2 := _rocq_assumption_4) (_rocq_assumption_3 := _rocq_assumption_6) (_rocq_assumption_4 := _rocq_assumption_2) (_rocq_assumption_5 := _rocq_assumption_9) (_rocq_assumption_6 := _rocq_assumption_10) (_rocq_assumption_7 := _rocq_assumption_11))
        *
        (MonadVM.Ec.Alt_bn128.F_p12.t (_rocq_assumption_0 := _rocq_assumption_0) (_rocq_assumption_1 := _rocq_assumption_1) (_rocq_assumption_2 := _rocq_assumption_4) (_rocq_assumption_3 := _rocq_assumption_6) (_rocq_assumption_4 := _rocq_assumption_2) (_rocq_assumption_5 := _rocq_assumption_9) (_rocq_assumption_6 := _rocq_assumption_10) (_rocq_assumption_7 := _rocq_assumption_11)))}
  `{_rocq_assumption_42 : RocqOfOCaml.Basics.Unreachable (int * int)}
  `{_rocq_assumption_43 :
    RocqOfOCaml.Basics.Unreachable
      (RocqOfOCaml.OCamlSeq.t
        (MonadVM.Ec.Bls12_381.F_p12.t (_rocq_assumption_0 := _rocq_assumption_0) (_rocq_assumption_1 := _rocq_assumption_1) (_rocq_assumption_2 := _rocq_assumption_2) (_rocq_assumption_3 := _rocq_assumption_3) (_rocq_assumption_4 := _rocq_assumption_4) (_rocq_assumption_5 := _rocq_assumption_5) (_rocq_assumption_6 := _rocq_assumption_6) (_rocq_assumption_7 := _rocq_assumption_7))
      ->
      RocqOfOCaml.OCamlSeq.t
        (MonadVM.Ec.Bls12_381.F_p12.t (_rocq_assumption_0 := _rocq_assumption_0) (_rocq_assumption_1 := _rocq_assumption_1) (_rocq_assumption_2 := _rocq_assumption_2) (_rocq_assumption_3 := _rocq_assumption_3) (_rocq_assumption_4 := _rocq_assumption_4) (_rocq_assumption_5 := _rocq_assumption_5) (_rocq_assumption_6 := _rocq_assumption_6) (_rocq_assumption_7 := _rocq_assumption_7)))}
  `{_rocq_assumption_44 :
    RocqOfOCaml.Basics.Unreachable
      (RocqOfOCaml.OCamlSeq.t
        (MonadVM.Ec.Alt_bn128.F_p12.t (_rocq_assumption_0 := _rocq_assumption_0) (_rocq_assumption_1 := _rocq_assumption_1) (_rocq_assumption_2 := _rocq_assumption_4) (_rocq_assumption_3 := _rocq_assumption_6) (_rocq_assumption_4 := _rocq_assumption_2) (_rocq_assumption_5 := _rocq_assumption_9) (_rocq_assumption_6 := _rocq_assumption_10) (_rocq_assumption_7 := _rocq_assumption_11))
      ->
      RocqOfOCaml.OCamlSeq.t
        (MonadVM.Ec.Alt_bn128.F_p12.t (_rocq_assumption_0 := _rocq_assumption_0) (_rocq_assumption_1 := _rocq_assumption_1) (_rocq_assumption_2 := _rocq_assumption_4) (_rocq_assumption_3 := _rocq_assumption_6) (_rocq_assumption_4 := _rocq_assumption_2) (_rocq_assumption_5 := _rocq_assumption_9) (_rocq_assumption_6 := _rocq_assumption_10) (_rocq_assumption_7 := _rocq_assumption_11)))}
  `{_rocq_assumption_45 :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Support.UintN.Impl.t -> MonadVM.Support.UintN.Impl.t ->
      MonadVM.Support.UintN.Impl.t)}
  `{_rocq_assumption_46 :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Support.UintN.Impl.t -> MonadVM.Support.UintN.Impl.t ->
      MonadVM.Support.UintN.t)}
  `{_rocq_assumption_47 :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Support.UintN.Impl.t -> MonadVM.Support.UintN.Impl.t ->
      MonadVM.Support.UintN.Impl.t -> MonadVM.Support.UintN.Impl.t ->
      MonadVM.Support.UintN.Impl.t)}
  `{_rocq_assumption_48 :
    RocqOfOCaml.Basics.Unreachable
      ((MonadVM.Ec.Bls12_381.F_p.t (_rocq_assumption_0 := _rocq_assumption_0) (_rocq_assumption_1 := _rocq_assumption_1) (_rocq_assumption_2 := _rocq_assumption_2))
      ->
      option
        (MonadVM.Ec.Bls12_381.F_p.t (_rocq_assumption_0 := _rocq_assumption_0) (_rocq_assumption_1 := _rocq_assumption_1) (_rocq_assumption_2 := _rocq_assumption_2)))}
  `{_rocq_assumption_49 :
    RocqOfOCaml.Basics.Unreachable
      (RocqOfOCaml.OCamlIarray.t
        (MonadVM.Ec.Alt_bn128.F_p12.MonadVM_Ec_Algebra_Polynomial_extension_include_fargs (_rocq_module_assumption_0 := _rocq_assumption_0) (_rocq_module_assumption_1 := _rocq_assumption_1) (_rocq_module_assumption_2 := _rocq_assumption_4) (_rocq_module_assumption_3 := _rocq_assumption_6) (_rocq_module_assumption_4 := _rocq_assumption_2) (_rocq_module_assumption_5 := _rocq_assumption_9) (_rocq_module_assumption_6 := _rocq_assumption_10) (_rocq_module_assumption_7 := _rocq_assumption_11)).(MonadVM.Ec.Algebra.Polynomial_extension.F).(MonadVM.Ec.Algebra.FIELD.t))}
  `{_rocq_assumption_50 : RocqOfOCaml.Basics.Unreachable int64}
  `{_rocq_assumption_51 :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Secp256r1.F_p (_rocq_module_assumption_0 := _rocq_assumption_0) (_rocq_module_assumption_1 := _rocq_assumption_1) (_rocq_module_assumption_2 := _rocq_assumption_2)).(MonadVM.Ec.Algebra.Prime_field.Prime_field_result.t)}
  `{_rocq_assumption_52 :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Secp256r1.C_1 (_rocq_module_assumption_0 := _rocq_assumption_0) (_rocq_module_assumption_1 := _rocq_assumption_1) (_rocq_module_assumption_2 := _rocq_assumption_4) (_rocq_module_assumption_3 := _rocq_assumption_2) (_rocq_module_assumption_4 := _rocq_assumption_51)).(MonadVM.Ec.Curve.Make.Make_result.t)}
  `{_rocq_assumption_53 :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Secp256r1.G_1 (_rocq_module_assumption_0 := _rocq_assumption_0) (_rocq_module_assumption_1 := _rocq_assumption_1) (_rocq_module_assumption_2 := _rocq_assumption_4) (_rocq_module_assumption_3 := _rocq_assumption_2) (_rocq_module_assumption_4 := _rocq_assumption_51) (_rocq_module_assumption_5 := _rocq_assumption_52)).(MonadVM.Ec.Curve.Make.Subgroup.Subgroup_result.curve)}
  `{_rocq_assumption_54 :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Secp256r1.F_q (_rocq_module_assumption_0 := _rocq_assumption_0) (_rocq_module_assumption_1 := _rocq_assumption_1) (_rocq_module_assumption_2 := _rocq_assumption_2)).(MonadVM.Ec.Algebra.Prime_field.Prime_field_result.t)}
  `{_rocq_assumption_55 :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Bls12_381.F_p12.MonadVM_Ec_Algebra_Polynomial_extension_include (_rocq_module_assumption_0 := _rocq_assumption_0) (_rocq_module_assumption_1 := _rocq_assumption_1) (_rocq_module_assumption_2 := _rocq_assumption_2) (_rocq_module_assumption_3 := _rocq_assumption_3) (_rocq_module_assumption_4 := _rocq_assumption_4) (_rocq_module_assumption_5 := _rocq_assumption_5) (_rocq_module_assumption_6 := _rocq_assumption_6) (_rocq_module_assumption_7 := _rocq_assumption_7)).(MonadVM.Ec.Algebra.Polynomial_extension.Polynomial_extension_result.Underlying_ring).(MonadVM.Ec.Algebra.Polynomial_ring.Polynomial_ring_result.t)}
  `{_rocq_assumption_56 :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Bls12_381.G_2 (_rocq_module_assumption_0 := _rocq_assumption_0) (_rocq_module_assumption_1 := _rocq_assumption_1) (_rocq_module_assumption_2 := _rocq_assumption_4) (_rocq_module_assumption_3 := _rocq_assumption_2) (_rocq_module_assumption_4 := _rocq_assumption_5) (_rocq_module_assumption_5 := _rocq_assumption_25)).(MonadVM.Ec.Curve.Make.Subgroup.Subgroup_result.curve)}
  `{_rocq_assumption_57 :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Bls12_381.G_1 (_rocq_module_assumption_0 := _rocq_assumption_0) (_rocq_module_assumption_1 := _rocq_assumption_1) (_rocq_module_assumption_2 := _rocq_assumption_4) (_rocq_module_assumption_3 := _rocq_assumption_2) (_rocq_module_assumption_4 := _rocq_assumption_5) (_rocq_module_assumption_5 := _rocq_assumption_27)).(MonadVM.Ec.Curve.Make.Subgroup.Subgroup_result.curve)}
  `{_rocq_assumption_58 :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Bls12_381.F_p_SWU (_rocq_module_assumption_0 := _rocq_assumption_0) (_rocq_module_assumption_1 := _rocq_assumption_1) (_rocq_module_assumption_2 := _rocq_assumption_4) (_rocq_module_assumption_3 := _rocq_assumption_2) (_rocq_module_assumption_4 := _rocq_assumption_5) (_rocq_module_assumption_5 := _rocq_assumption_37) (_rocq_module_assumption_6 := _rocq_assumption_48)).(MonadVM.Ec.Curve.SWU_method.SWU_method_result.F).(MonadVM.Ec.Algebra.FIELD.t)}
  `{_rocq_assumption_59 :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Bls12_381.F_p2_SWU (_rocq_module_assumption_0 := _rocq_assumption_0) (_rocq_module_assumption_1 := _rocq_assumption_1) (_rocq_module_assumption_2 := _rocq_assumption_4) (_rocq_module_assumption_3 := _rocq_assumption_2) (_rocq_module_assumption_4 := _rocq_assumption_5) (_rocq_module_assumption_5 := _rocq_assumption_37) (_rocq_module_assumption_6 := _rocq_assumption_48)).(MonadVM.Ec.Curve.SWU_method.SWU_method_result.F).(MonadVM.Ec.Algebra.FIELD.t)}
  `{_rocq_assumption_60 :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Alt_bn128.F_p12.MonadVM_Ec_Algebra_Polynomial_extension_include_fargs (_rocq_module_assumption_0 := _rocq_assumption_0) (_rocq_module_assumption_1 := _rocq_assumption_1) (_rocq_module_assumption_2 := _rocq_assumption_4) (_rocq_module_assumption_3 := _rocq_assumption_6) (_rocq_module_assumption_4 := _rocq_assumption_2) (_rocq_module_assumption_5 := _rocq_assumption_9) (_rocq_module_assumption_6 := _rocq_assumption_10) (_rocq_module_assumption_7 := _rocq_assumption_11)).(MonadVM.Ec.Algebra.Polynomial_extension.F).(MonadVM.Ec.Algebra.FIELD.t)}
  `{_rocq_assumption_61 :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Alt_bn128.F_p12.MonadVM_Ec_Algebra_Polynomial_extension_include (_rocq_module_assumption_0 := _rocq_assumption_0) (_rocq_module_assumption_1 := _rocq_assumption_1) (_rocq_module_assumption_2 := _rocq_assumption_4) (_rocq_module_assumption_3 := _rocq_assumption_6) (_rocq_module_assumption_4 := _rocq_assumption_2) (_rocq_module_assumption_5 := _rocq_assumption_9) (_rocq_module_assumption_6 := _rocq_assumption_10) (_rocq_module_assumption_7 := _rocq_assumption_11)).(MonadVM.Ec.Algebra.Polynomial_extension.Polynomial_extension_result.Underlying_ring).(MonadVM.Ec.Algebra.Polynomial_ring.Polynomial_ring_result.t)}
  `{_rocq_assumption_62 :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Alt_bn128.C_2 (_rocq_module_assumption_0 := _rocq_assumption_0) (_rocq_module_assumption_1 := _rocq_assumption_1) (_rocq_module_assumption_2 := _rocq_assumption_4) (_rocq_module_assumption_3 := _rocq_assumption_2) (_rocq_module_assumption_4 := _rocq_assumption_10)).(MonadVM.Ec.Curve.Make.Make_result.t)}
  `{_rocq_assumption_63 :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Ec.Alt_bn128.C_1 (_rocq_module_assumption_0 := _rocq_assumption_0) (_rocq_module_assumption_1 := _rocq_assumption_1) (_rocq_module_assumption_2 := _rocq_assumption_4) (_rocq_module_assumption_3 := _rocq_assumption_2) (_rocq_module_assumption_4 := _rocq_assumption_10)).(MonadVM.Ec.Curve.Make.Make_result.t)}
  `{_rocq_assumption_64 :
    RocqOfOCaml.Basics.Unreachable
      MonadVM.Byte_string.B64.(MonadVM.Byte_string.Fixed.Fixed_result.t)}
  `{_rocq_assumption_65 :
    RocqOfOCaml.Basics.Unreachable
      MonadVM.Byte_string.B48.(MonadVM.Byte_string.Fixed.Fixed_result.t)}
  `{_rocq_assumption_66 :
    RocqOfOCaml.Basics.Unreachable
      MonadVM.Byte_string.B32.(MonadVM.Byte_string.Fixed.Fixed_result.t)}
  `{_rocq_assumption_67 :
    RocqOfOCaml.Basics.Unreachable
      ((MonadVM.Ec.Bls12_381.C_2 (_rocq_module_assumption_0 := _rocq_assumption_0) (_rocq_module_assumption_1 := _rocq_assumption_1) (_rocq_module_assumption_2 := _rocq_assumption_4) (_rocq_module_assumption_3 := _rocq_assumption_2) (_rocq_module_assumption_4 := _rocq_assumption_5)).(MonadVM.Ec.Curve.Make.Make_result.t)
      -> MonadVM.Byte_string.Bytes.t)}
  `{_rocq_assumption_68 :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Evmc.Message.t * int ->
      MonadVM.Precompiles.Utils.Precompile.Inner.t
        (sum MonadVM.Support.UintN.t MonadVM.Evmc.Result.StatusCode.t *
          (MonadVM.Evmc.Message.t * int)))}
  `{_rocq_assumption_69 :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Evmc.Message.t * int ->
      MonadVM.Precompiles.Utils.Precompile.Inner.t
        (sum
          (MonadVM.Precompiles.Bls12_381.opened_module_143_fargs (_rocq_module_assumption_0 := _rocq_assumption_0) (_rocq_module_assumption_1 := _rocq_assumption_1) (_rocq_module_assumption_2 := _rocq_assumption_4) (_rocq_module_assumption_3 := _rocq_assumption_2) (_rocq_module_assumption_4 := _rocq_assumption_5) (_rocq_module_assumption_5 := _rocq_assumption_38) (_rocq_module_assumption_6 := _rocq_assumption_39) (_rocq_module_assumption_7 := _rocq_assumption_25) (_rocq_module_assumption_8 := _rocq_assumption_27) (_rocq_module_assumption_9 := _rocq_assumption_64)).(MonadVM.Precompiles.Utils.Ec_precompile_utils.M).(MonadVM.Precompiles.Utils.Ec_precompile_utils_M_signature.F_p2_t)
          MonadVM.Evmc.Result.StatusCode.t * (MonadVM.Evmc.Message.t * int)))}
  `{_rocq_assumption_70 :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Evmc.Message.t * int ->
      MonadVM.Precompiles.Utils.Precompile.Inner.t
        (sum
          (MonadVM.Precompiles.Alt_bn128.opened_module_165_fargs (_rocq_module_assumption_0 := _rocq_assumption_0) (_rocq_module_assumption_1 := _rocq_assumption_1) (_rocq_module_assumption_2 := _rocq_assumption_4) (_rocq_module_assumption_3 := _rocq_assumption_38) (_rocq_module_assumption_4 := _rocq_assumption_39) (_rocq_module_assumption_5 := _rocq_assumption_2) (_rocq_module_assumption_6 := _rocq_assumption_10) (_rocq_module_assumption_7 := _rocq_assumption_62) (_rocq_module_assumption_8 := _rocq_assumption_63) (_rocq_module_assumption_9 := _rocq_assumption_66)).(MonadVM.Precompiles.Utils.Ec_precompile_utils.M).(MonadVM.Precompiles.Utils.Ec_precompile_utils_M_signature.F_p2_t)
          MonadVM.Evmc.Result.StatusCode.t * (MonadVM.Evmc.Message.t * int)))}
  (revision : MonadVM.Chain.Monad.Revision.active)
  : let table :=
      MonadVM.Precompiles.Make.ethereum_precompiles
        (_fargs := MonadVM.Precompiles.Make.Build_FArgs
          {| MonadVM.Precompiles.Make_Revision_signature.revision := revision |})
        (_rocq_assumption_0 := _rocq_assumption_0)
        (_rocq_assumption_1 := _rocq_assumption_1)
        (_rocq_assumption_2 := _rocq_assumption_2)
        (_rocq_assumption_3 := _rocq_assumption_3)
        (_rocq_assumption_4 := _rocq_assumption_4)
        (_rocq_assumption_5 := _rocq_assumption_5)
        (_rocq_assumption_6 := _rocq_assumption_6)
        (_rocq_assumption_7 := _rocq_assumption_7)
        (_rocq_assumption_8 := _rocq_assumption_8)
        (_rocq_assumption_9 := _rocq_assumption_9)
        (_rocq_assumption_10 := _rocq_assumption_10)
        (_rocq_assumption_11 := _rocq_assumption_11)
        (_rocq_assumption_12 := _rocq_assumption_12)
        (_rocq_assumption_13 := _rocq_assumption_13)
        (_rocq_assumption_14 := _rocq_assumption_14)
        (_rocq_assumption_15 := _rocq_assumption_15)
        (_rocq_assumption_16 := _rocq_assumption_16)
        (_rocq_assumption_17 := _rocq_assumption_17)
        (_rocq_assumption_18 := _rocq_assumption_18)
        (_rocq_assumption_19 := _rocq_assumption_19)
        (_rocq_assumption_20 := _rocq_assumption_20)
        (_rocq_assumption_21 := _rocq_assumption_21)
        (_rocq_assumption_22 := _rocq_assumption_22)
        (_rocq_assumption_23 := _rocq_assumption_23)
        (_rocq_assumption_24 := _rocq_assumption_24)
        (_rocq_assumption_25 := _rocq_assumption_25)
        (_rocq_assumption_26 := _rocq_assumption_26)
        (_rocq_assumption_27 := _rocq_assumption_27)
        (_rocq_assumption_28 := _rocq_assumption_28)
        (_rocq_assumption_29 := _rocq_assumption_29)
        (_rocq_assumption_30 := _rocq_assumption_30)
        (_rocq_assumption_31 := _rocq_assumption_31)
        (_rocq_assumption_32 := _rocq_assumption_32)
        (_rocq_assumption_33 := _rocq_assumption_33)
        (_rocq_assumption_34 := _rocq_assumption_34)
        (_rocq_assumption_35 := _rocq_assumption_35)
        (_rocq_assumption_36 := _rocq_assumption_36)
        (_rocq_assumption_37 := _rocq_assumption_37)
        (_rocq_assumption_38 := _rocq_assumption_38)
        (_rocq_assumption_39 := _rocq_assumption_39)
        (_rocq_assumption_40 := _rocq_assumption_40)
        (_rocq_assumption_41 := _rocq_assumption_41)
        (_rocq_assumption_42 := _rocq_assumption_42)
        (_rocq_assumption_43 := _rocq_assumption_43)
        (_rocq_assumption_44 := _rocq_assumption_44)
        (_rocq_assumption_45 := _rocq_assumption_45)
        (_rocq_assumption_46 := _rocq_assumption_46)
        (_rocq_assumption_47 := _rocq_assumption_47)
        (_rocq_assumption_48 := _rocq_assumption_48)
        (_rocq_assumption_49 := _rocq_assumption_49)
        (_rocq_assumption_50 := _rocq_assumption_50)
        (_rocq_assumption_51 := _rocq_assumption_51)
        (_rocq_assumption_52 := _rocq_assumption_52)
        (_rocq_assumption_53 := _rocq_assumption_53)
        (_rocq_assumption_54 := _rocq_assumption_54)
        (_rocq_assumption_55 := _rocq_assumption_55)
        (_rocq_assumption_56 := _rocq_assumption_56)
        (_rocq_assumption_57 := _rocq_assumption_57)
        (_rocq_assumption_58 := _rocq_assumption_58)
        (_rocq_assumption_59 := _rocq_assumption_59)
        (_rocq_assumption_60 := _rocq_assumption_60)
        (_rocq_assumption_61 := _rocq_assumption_61)
        (_rocq_assumption_62 := _rocq_assumption_62)
        (_rocq_assumption_63 := _rocq_assumption_63)
        (_rocq_assumption_64 := _rocq_assumption_64)
        (_rocq_assumption_65 := _rocq_assumption_65)
        (_rocq_assumption_66 := _rocq_assumption_66)
        (_rocq_assumption_67 := _rocq_assumption_67)
        (_rocq_assumption_68 := _rocq_assumption_68)
        (_rocq_assumption_69 := _rocq_assumption_69)
        (_rocq_assumption_70 := _rocq_assumption_70) in
    MonadVM.Chain.Ethereum.Address.Map.cardinal table = 18%Z /\
    map fst (MonadVM.Chain.Ethereum.Address.Map.bindings table) = fixed_keys /\
    MonadVM.Chain.Ethereum.Address.Map.find_opt (address_bytes 1) table =
      Some (MonadVM.Precompiles.ecrecover
        (_rocq_assumption_0 := _rocq_assumption_0)
        (_rocq_assumption_1 := _rocq_assumption_15)
        (_rocq_assumption_2 := _rocq_assumption_16)
        (_rocq_assumption_3 := _rocq_assumption_17)
        (_rocq_assumption_4 := _rocq_assumption_22)
        (_rocq_assumption_5 := _rocq_assumption_23)
        (_rocq_assumption_6 := _rocq_assumption_24)
        (_rocq_assumption_7 := _rocq_assumption_32)
        (_rocq_assumption_8 := _rocq_assumption_34)
        (_rocq_assumption_9 := _rocq_assumption_35)
        (_rocq_assumption_10 := _rocq_assumption_36)
        (_rocq_assumption_11 := _rocq_assumption_38)
        (_rocq_assumption_12 := _rocq_assumption_39)
        (_rocq_assumption_13 := _rocq_assumption_42)
        (_rocq_assumption_14 := _rocq_assumption_66)) /\
    MonadVM.Chain.Ethereum.Address.Map.find_opt (address_bytes 2) table =
      Some (MonadVM.Precompiles.sha256
        (_rocq_assumption_0 := _rocq_assumption_15)
        (_rocq_assumption_1 := _rocq_assumption_24)
        (_rocq_assumption_2 := _rocq_assumption_32)
        (_rocq_assumption_3 := _rocq_assumption_35)
        (_rocq_assumption_4 := _rocq_assumption_36)
        (_rocq_assumption_5 := _rocq_assumption_38)) /\
    MonadVM.Chain.Ethereum.Address.Map.find_opt (address_bytes 3) table =
      Some (MonadVM.Precompiles.ripemd160
        (_rocq_assumption_0 := _rocq_assumption_15)
        (_rocq_assumption_1 := _rocq_assumption_24)
        (_rocq_assumption_2 := _rocq_assumption_32)
        (_rocq_assumption_3 := _rocq_assumption_34)
        (_rocq_assumption_4 := _rocq_assumption_35)
        (_rocq_assumption_5 := _rocq_assumption_36)
        (_rocq_assumption_6 := _rocq_assumption_38)
        (_rocq_assumption_7 := _rocq_assumption_39)) /\
    MonadVM.Chain.Ethereum.Address.Map.find_opt (address_bytes 4) table =
      Some (MonadVM.Precompiles.identity
        (_rocq_assumption_0 := _rocq_assumption_15)
        (_rocq_assumption_1 := _rocq_assumption_24)
        (_rocq_assumption_2 := _rocq_assumption_32)
        (_rocq_assumption_3 := _rocq_assumption_35)
        (_rocq_assumption_4 := _rocq_assumption_38)) /\
    MonadVM.Chain.Ethereum.Address.Map.find_opt (address_bytes 5) table =
      Some (let Modexp :=
        MonadVM.Precompiles.Modexp.Make
          ({|
            MonadVM.Precompiles.Modexp.Make_Revision_signature.revision :=
              revision
          |} : MonadVM.Precompiles.Modexp.Make_Revision_signature) in
        Modexp.(MonadVM.Precompiles.Modexp.Make.Make_result.precompile)
          (_rocq_assumption_0 := _rocq_assumption_0)
          (_rocq_assumption_1 := _rocq_assumption_15)
          (_rocq_assumption_2 := _rocq_assumption_1)
          (_rocq_assumption_3 := _rocq_assumption_22)
          (_rocq_assumption_4 := _rocq_assumption_23)
          (_rocq_assumption_5 := _rocq_assumption_24)
          (_rocq_assumption_6 := _rocq_assumption_32)
          (_rocq_assumption_7 := _rocq_assumption_33)
          (_rocq_assumption_8 := _rocq_assumption_35)
          (_rocq_assumption_9 := _rocq_assumption_36)
          (_rocq_assumption_10 := _rocq_assumption_38)
          (_rocq_assumption_11 := _rocq_assumption_39)
          (_rocq_assumption_12 := _rocq_assumption_42)
          (_rocq_assumption_13 := _rocq_assumption_45)
          (_rocq_assumption_14 := _rocq_assumption_46)
          (_rocq_assumption_15 := _rocq_assumption_47)
          (_rocq_assumption_16 := _rocq_assumption_68)) /\
    MonadVM.Chain.Ethereum.Address.Map.find_opt (address_bytes 6) table =
      Some (MonadVM.Precompiles.Alt_bn128.add
        (_rocq_assumption_0 := _rocq_assumption_0)
        (_rocq_assumption_1 := _rocq_assumption_15)
        (_rocq_assumption_2 := _rocq_assumption_1)
        (_rocq_assumption_3 := _rocq_assumption_4)
        (_rocq_assumption_4 := _rocq_assumption_24)
        (_rocq_assumption_5 := _rocq_assumption_32)
        (_rocq_assumption_6 := _rocq_assumption_33)
        (_rocq_assumption_7 := _rocq_assumption_35)
        (_rocq_assumption_8 := _rocq_assumption_38)
        (_rocq_assumption_9 := _rocq_assumption_39)
        (_rocq_assumption_10 := _rocq_assumption_2)
        (_rocq_assumption_11 := _rocq_assumption_10)
        (_rocq_assumption_12 := _rocq_assumption_62)
        (_rocq_assumption_13 := _rocq_assumption_63)
        (_rocq_assumption_14 := _rocq_assumption_66)) /\
    MonadVM.Chain.Ethereum.Address.Map.find_opt (address_bytes 7) table =
      Some (MonadVM.Precompiles.Alt_bn128.mul
        (_rocq_assumption_0 := _rocq_assumption_0)
        (_rocq_assumption_1 := _rocq_assumption_15)
        (_rocq_assumption_2 := _rocq_assumption_1)
        (_rocq_assumption_3 := _rocq_assumption_22)
        (_rocq_assumption_4 := _rocq_assumption_23)
        (_rocq_assumption_5 := _rocq_assumption_4)
        (_rocq_assumption_6 := _rocq_assumption_24)
        (_rocq_assumption_7 := _rocq_assumption_32)
        (_rocq_assumption_8 := _rocq_assumption_33)
        (_rocq_assumption_9 := _rocq_assumption_35)
        (_rocq_assumption_10 := _rocq_assumption_38)
        (_rocq_assumption_11 := _rocq_assumption_39)
        (_rocq_assumption_12 := _rocq_assumption_2)
        (_rocq_assumption_13 := _rocq_assumption_10)
        (_rocq_assumption_14 := _rocq_assumption_62)
        (_rocq_assumption_15 := _rocq_assumption_63)
        (_rocq_assumption_16 := _rocq_assumption_66)) /\
    MonadVM.Chain.Ethereum.Address.Map.find_opt (address_bytes 8) table =
      Some (MonadVM.Precompiles.Alt_bn128.pairing_check
        (_rocq_assumption_0 := _rocq_assumption_0)
        (_rocq_assumption_1 := _rocq_assumption_1)
        (_rocq_assumption_2 := _rocq_assumption_4)
        (_rocq_assumption_3 := _rocq_assumption_6)
        (_rocq_assumption_4 := _rocq_assumption_2)
        (_rocq_assumption_5 := _rocq_assumption_9)
        (_rocq_assumption_6 := _rocq_assumption_10)
        (_rocq_assumption_7 := _rocq_assumption_11)
        (_rocq_assumption_8 := _rocq_assumption_12)
        (_rocq_assumption_9 := _rocq_assumption_15)
        (_rocq_assumption_10 := _rocq_assumption_22)
        (_rocq_assumption_11 := _rocq_assumption_23)
        (_rocq_assumption_12 := _rocq_assumption_24)
        (_rocq_assumption_13 := _rocq_assumption_32)
        (_rocq_assumption_14 := _rocq_assumption_35)
        (_rocq_assumption_15 := _rocq_assumption_38)
        (_rocq_assumption_16 := _rocq_assumption_39)
        (_rocq_assumption_17 := _rocq_assumption_41)
        (_rocq_assumption_18 := _rocq_assumption_42)
        (_rocq_assumption_19 := _rocq_assumption_44)
        (_rocq_assumption_20 := _rocq_assumption_49)
        (_rocq_assumption_21 := _rocq_assumption_60)
        (_rocq_assumption_22 := _rocq_assumption_61)
        (_rocq_assumption_23 := _rocq_assumption_62)
        (_rocq_assumption_24 := _rocq_assumption_63)
        (_rocq_assumption_25 := _rocq_assumption_66)
        (_rocq_assumption_26 := _rocq_assumption_70)) /\
    MonadVM.Chain.Ethereum.Address.Map.find_opt (address_bytes 9) table =
      Some (MonadVM.Precompiles.blake2f
        (_rocq_assumption_0 := _rocq_assumption_15)
        (_rocq_assumption_1 := _rocq_assumption_1)
        (_rocq_assumption_2 := _rocq_assumption_18)
        (_rocq_assumption_3 := _rocq_assumption_19)
        (_rocq_assumption_4 := _rocq_assumption_20)
        (_rocq_assumption_5 := _rocq_assumption_21)
        (_rocq_assumption_6 := _rocq_assumption_24)
        (_rocq_assumption_7 := _rocq_assumption_32)
        (_rocq_assumption_8 := _rocq_assumption_35)
        (_rocq_assumption_9 := _rocq_assumption_36)
        (_rocq_assumption_10 := _rocq_assumption_38)
        (_rocq_assumption_11 := _rocq_assumption_39)
        (_rocq_assumption_12 := _rocq_assumption_42)
        (_rocq_assumption_13 := _rocq_assumption_50)) /\
    MonadVM.Chain.Ethereum.Address.Map.find_opt (address_bytes 10) table =
      Some (MonadVM.Precompiles.Point_evaluation.precompile
        (_rocq_assumption_0 := _rocq_assumption_0)
        (_rocq_assumption_1 := _rocq_assumption_1)
        (_rocq_assumption_2 := _rocq_assumption_2)
        (_rocq_assumption_3 := _rocq_assumption_3)
        (_rocq_assumption_4 := _rocq_assumption_4)
        (_rocq_assumption_5 := _rocq_assumption_5)
        (_rocq_assumption_6 := _rocq_assumption_6)
        (_rocq_assumption_7 := _rocq_assumption_7)
        (_rocq_assumption_8 := _rocq_assumption_8)
        (_rocq_assumption_9 := _rocq_assumption_14)
        (_rocq_assumption_10 := _rocq_assumption_15)
        (_rocq_assumption_11 := _rocq_assumption_23)
        (_rocq_assumption_12 := _rocq_assumption_24)
        (_rocq_assumption_13 := _rocq_assumption_25)
        (_rocq_assumption_14 := _rocq_assumption_26)
        (_rocq_assumption_15 := _rocq_assumption_32)
        (_rocq_assumption_16 := _rocq_assumption_33)
        (_rocq_assumption_17 := _rocq_assumption_35)
        (_rocq_assumption_18 := _rocq_assumption_36)
        (_rocq_assumption_19 := _rocq_assumption_37)
        (_rocq_assumption_20 := _rocq_assumption_38)
        (_rocq_assumption_21 := _rocq_assumption_39)
        (_rocq_assumption_22 := _rocq_assumption_40)
        (_rocq_assumption_23 := _rocq_assumption_42)
        (_rocq_assumption_24 := _rocq_assumption_43)
        (_rocq_assumption_25 := _rocq_assumption_48)
        (_rocq_assumption_26 := _rocq_assumption_55)
        (_rocq_assumption_27 := _rocq_assumption_56)
        (_rocq_assumption_28 := _rocq_assumption_27)
        (_rocq_assumption_29 := _rocq_assumption_57)
        (_rocq_assumption_30 := _rocq_assumption_65)
        (_rocq_assumption_31 := _rocq_assumption_66)) /\
    MonadVM.Chain.Ethereum.Address.Map.find_opt (address_bytes 11) table =
      Some (MonadVM.Precompiles.Bls12_381.g1_add
        (_rocq_assumption_0 := _rocq_assumption_0)
        (_rocq_assumption_1 := _rocq_assumption_15)
        (_rocq_assumption_2 := _rocq_assumption_1)
        (_rocq_assumption_3 := _rocq_assumption_4)
        (_rocq_assumption_4 := _rocq_assumption_24)
        (_rocq_assumption_5 := _rocq_assumption_2)
        (_rocq_assumption_6 := _rocq_assumption_5)
        (_rocq_assumption_7 := _rocq_assumption_32)
        (_rocq_assumption_8 := _rocq_assumption_33)
        (_rocq_assumption_9 := _rocq_assumption_35)
        (_rocq_assumption_10 := _rocq_assumption_38)
        (_rocq_assumption_11 := _rocq_assumption_39)
        (_rocq_assumption_12 := _rocq_assumption_25)
        (_rocq_assumption_13 := _rocq_assumption_27)
        (_rocq_assumption_14 := _rocq_assumption_64)) /\
    MonadVM.Chain.Ethereum.Address.Map.find_opt (address_bytes 12) table =
      Some (MonadVM.Precompiles.Bls12_381.g1_msm
        (_rocq_assumption_0 := _rocq_assumption_0)
        (_rocq_assumption_1 := _rocq_assumption_15)
        (_rocq_assumption_2 := _rocq_assumption_1)
        (_rocq_assumption_3 := _rocq_assumption_22)
        (_rocq_assumption_4 := _rocq_assumption_23)
        (_rocq_assumption_5 := _rocq_assumption_4)
        (_rocq_assumption_6 := _rocq_assumption_24)
        (_rocq_assumption_7 := _rocq_assumption_2)
        (_rocq_assumption_8 := _rocq_assumption_5)
        (_rocq_assumption_9 := _rocq_assumption_32)
        (_rocq_assumption_10 := _rocq_assumption_33)
        (_rocq_assumption_11 := _rocq_assumption_35)
        (_rocq_assumption_12 := _rocq_assumption_38)
        (_rocq_assumption_13 := _rocq_assumption_39)
        (_rocq_assumption_14 := _rocq_assumption_25)
        (_rocq_assumption_15 := _rocq_assumption_27)
        (_rocq_assumption_16 := _rocq_assumption_64)) /\
    MonadVM.Chain.Ethereum.Address.Map.find_opt (address_bytes 13) table =
      Some (MonadVM.Precompiles.Bls12_381.g2_add
        (_rocq_assumption_0 := _rocq_assumption_0)
        (_rocq_assumption_1 := _rocq_assumption_15)
        (_rocq_assumption_2 := _rocq_assumption_1)
        (_rocq_assumption_3 := _rocq_assumption_4)
        (_rocq_assumption_4 := _rocq_assumption_24)
        (_rocq_assumption_5 := _rocq_assumption_2)
        (_rocq_assumption_6 := _rocq_assumption_5)
        (_rocq_assumption_7 := _rocq_assumption_32)
        (_rocq_assumption_8 := _rocq_assumption_33)
        (_rocq_assumption_9 := _rocq_assumption_35)
        (_rocq_assumption_10 := _rocq_assumption_38)
        (_rocq_assumption_11 := _rocq_assumption_39)
        (_rocq_assumption_12 := _rocq_assumption_25)
        (_rocq_assumption_13 := _rocq_assumption_27)
        (_rocq_assumption_14 := _rocq_assumption_64)
        (_rocq_assumption_15 := _rocq_assumption_67)
        (_rocq_assumption_16 := _rocq_assumption_69)) /\
    MonadVM.Chain.Ethereum.Address.Map.find_opt (address_bytes 14) table =
      Some (MonadVM.Precompiles.Bls12_381.g2_msm
        (_rocq_assumption_0 := _rocq_assumption_0)
        (_rocq_assumption_1 := _rocq_assumption_15)
        (_rocq_assumption_2 := _rocq_assumption_1)
        (_rocq_assumption_3 := _rocq_assumption_22)
        (_rocq_assumption_4 := _rocq_assumption_23)
        (_rocq_assumption_5 := _rocq_assumption_4)
        (_rocq_assumption_6 := _rocq_assumption_24)
        (_rocq_assumption_7 := _rocq_assumption_2)
        (_rocq_assumption_8 := _rocq_assumption_5)
        (_rocq_assumption_9 := _rocq_assumption_32)
        (_rocq_assumption_10 := _rocq_assumption_33)
        (_rocq_assumption_11 := _rocq_assumption_35)
        (_rocq_assumption_12 := _rocq_assumption_38)
        (_rocq_assumption_13 := _rocq_assumption_39)
        (_rocq_assumption_14 := _rocq_assumption_25)
        (_rocq_assumption_15 := _rocq_assumption_27)
        (_rocq_assumption_16 := _rocq_assumption_64)
        (_rocq_assumption_17 := _rocq_assumption_67)
        (_rocq_assumption_18 := _rocq_assumption_69)) /\
    MonadVM.Chain.Ethereum.Address.Map.find_opt (address_bytes 15) table =
      Some (MonadVM.Precompiles.Bls12_381.pairing_check
        (_rocq_assumption_0 := _rocq_assumption_0)
        (_rocq_assumption_1 := _rocq_assumption_1)
        (_rocq_assumption_2 := _rocq_assumption_2)
        (_rocq_assumption_3 := _rocq_assumption_3)
        (_rocq_assumption_4 := _rocq_assumption_4)
        (_rocq_assumption_5 := _rocq_assumption_5)
        (_rocq_assumption_6 := _rocq_assumption_6)
        (_rocq_assumption_7 := _rocq_assumption_7)
        (_rocq_assumption_8 := _rocq_assumption_8)
        (_rocq_assumption_9 := _rocq_assumption_15)
        (_rocq_assumption_10 := _rocq_assumption_23)
        (_rocq_assumption_11 := _rocq_assumption_24)
        (_rocq_assumption_12 := _rocq_assumption_32)
        (_rocq_assumption_13 := _rocq_assumption_35)
        (_rocq_assumption_14 := _rocq_assumption_36)
        (_rocq_assumption_15 := _rocq_assumption_38)
        (_rocq_assumption_16 := _rocq_assumption_39)
        (_rocq_assumption_17 := _rocq_assumption_40)
        (_rocq_assumption_18 := _rocq_assumption_42)
        (_rocq_assumption_19 := _rocq_assumption_43)
        (_rocq_assumption_20 := _rocq_assumption_55)
        (_rocq_assumption_21 := _rocq_assumption_25)
        (_rocq_assumption_22 := _rocq_assumption_27)
        (_rocq_assumption_23 := _rocq_assumption_64)
        (_rocq_assumption_24 := _rocq_assumption_69)) /\
    MonadVM.Chain.Ethereum.Address.Map.find_opt (address_bytes 16) table =
      Some (MonadVM.Precompiles.Bls12_381.map_fp_to_g1
        (_rocq_assumption_0 := _rocq_assumption_0)
        (_rocq_assumption_1 := _rocq_assumption_1)
        (_rocq_assumption_2 := _rocq_assumption_2)
        (_rocq_assumption_3 := _rocq_assumption_3)
        (_rocq_assumption_4 := _rocq_assumption_15)
        (_rocq_assumption_5 := _rocq_assumption_4)
        (_rocq_assumption_6 := _rocq_assumption_24)
        (_rocq_assumption_7 := _rocq_assumption_5)
        (_rocq_assumption_8 := _rocq_assumption_27)
        (_rocq_assumption_9 := _rocq_assumption_28)
        (_rocq_assumption_10 := _rocq_assumption_29)
        (_rocq_assumption_11 := _rocq_assumption_32)
        (_rocq_assumption_12 := _rocq_assumption_33)
        (_rocq_assumption_13 := _rocq_assumption_35)
        (_rocq_assumption_14 := _rocq_assumption_37)
        (_rocq_assumption_15 := _rocq_assumption_38)
        (_rocq_assumption_16 := _rocq_assumption_39)
        (_rocq_assumption_17 := _rocq_assumption_48)
        (_rocq_assumption_18 := _rocq_assumption_58)
        (_rocq_assumption_19 := _rocq_assumption_25)
        (_rocq_assumption_20 := _rocq_assumption_64)) /\
    MonadVM.Chain.Ethereum.Address.Map.find_opt (address_bytes 17) table =
      Some (MonadVM.Precompiles.Bls12_381.map_fp2_to_g2
        (_rocq_assumption_0 := _rocq_assumption_0)
        (_rocq_assumption_1 := _rocq_assumption_1)
        (_rocq_assumption_2 := _rocq_assumption_4)
        (_rocq_assumption_3 := _rocq_assumption_2)
        (_rocq_assumption_4 := _rocq_assumption_5)
        (_rocq_assumption_5 := _rocq_assumption_13)
        (_rocq_assumption_6 := _rocq_assumption_15)
        (_rocq_assumption_7 := _rocq_assumption_24)
        (_rocq_assumption_8 := _rocq_assumption_25)
        (_rocq_assumption_9 := _rocq_assumption_26)
        (_rocq_assumption_10 := _rocq_assumption_30)
        (_rocq_assumption_11 := _rocq_assumption_31)
        (_rocq_assumption_12 := _rocq_assumption_32)
        (_rocq_assumption_13 := _rocq_assumption_33)
        (_rocq_assumption_14 := _rocq_assumption_35)
        (_rocq_assumption_15 := _rocq_assumption_37)
        (_rocq_assumption_16 := _rocq_assumption_38)
        (_rocq_assumption_17 := _rocq_assumption_39)
        (_rocq_assumption_18 := _rocq_assumption_48)
        (_rocq_assumption_19 := _rocq_assumption_59)
        (_rocq_assumption_20 := _rocq_assumption_27)
        (_rocq_assumption_21 := _rocq_assumption_64)
        (_rocq_assumption_22 := _rocq_assumption_67)
        (_rocq_assumption_23 := _rocq_assumption_69)) /\
    MonadVM.Chain.Ethereum.Address.Map.find_opt (address_bytes_256) table =
      Some (MonadVM.Precompiles.Secp256r1.verify
        (_rocq_assumption_0 := _rocq_assumption_0)
        (_rocq_assumption_1 := _rocq_assumption_15)
        (_rocq_assumption_2 := _rocq_assumption_1)
        (_rocq_assumption_3 := _rocq_assumption_22)
        (_rocq_assumption_4 := _rocq_assumption_23)
        (_rocq_assumption_5 := _rocq_assumption_4)
        (_rocq_assumption_6 := _rocq_assumption_24)
        (_rocq_assumption_7 := _rocq_assumption_32)
        (_rocq_assumption_8 := _rocq_assumption_35)
        (_rocq_assumption_9 := _rocq_assumption_36)
        (_rocq_assumption_10 := _rocq_assumption_38)
        (_rocq_assumption_11 := _rocq_assumption_39)
        (_rocq_assumption_12 := _rocq_assumption_42)
        (_rocq_assumption_13 := _rocq_assumption_2)
        (_rocq_assumption_14 := _rocq_assumption_51)
        (_rocq_assumption_15 := _rocq_assumption_52)
        (_rocq_assumption_16 := _rocq_assumption_53)
        (_rocq_assumption_17 := _rocq_assumption_54)) /\
    forall (index : nat) (key : string),
      nth_error fixed_keys index = Some key ->
      MonadVM.Chain.Ethereum.Address.Map.find_opt key table =
        nth_error
          (map snd (MonadVM.Chain.Ethereum.Address.Map.bindings table))
          index.
Proof.
  cbn zeta.
  unfold MonadVM.Precompiles.Make.ethereum_precompiles.
  split.
  - apply cardinal_with_fixed_keys.
    cbn [map fst].
    vm_compute.
    reflexivity.
  - split.
    + apply binding_keys_with_fixed_keys.
      cbn [map fst].
      vm_compute.
      reflexivity.
    + repeat split.
      intros index key Hkey.
      cbn zeta.
      match goal with
      | |- MonadVM.Chain.Ethereum.Address.Map.find_opt _
             (MonadVM.Chain.Ethereum.Address.Map.of_list ?entries) = _ =>
          apply (binding_find_opt_index_from_ordered_bindings
            entries index key)
      end.
      * cbn [map fst]. vm_compute. reflexivity.
      * exact Hkey.
Qed.

Print Assumptions precompiles_table_shape.
