(** A lookup in the generated precompile map preserves entry gas bounds. *)

From Stdlib Require Import List ZArith.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import MonadExecutionSpecs.Termination.VmUnsignedGas.
Require MonadVM.Evmc.
Require MonadVM.Chain.Ethereum.
Require MonadVM.Precompiles.Utils.

Local Open Scope Z_scope.

Section MapLookup.
Context {key : Set} (order : RocqOfOCaml.OCamlMap.OrderedType (t := key)).
Context {A : Set} (property : A -> Prop).

Lemma map_add_preserves_property
    (address : key) (value : A)
    (map : RocqOfOCaml.OCamlMap.Make.t A) :
  property value ->
  Forall (fun entry : key * A => property (snd entry)) map ->
  Forall (fun entry : key * A => property (snd entry))
    (@RocqOfOCaml.OCamlMap.Make.add key order A address value map).
Proof.
  intros Hvalue Hmap.
  induction Hmap as [|[old_address old_value] tail Hold Htail IH].
  - constructor; [exact Hvalue | constructor].
  - cbn [RocqOfOCaml.OCamlMap.Make.add].
    destruct (RocqOfOCaml.OCamlMap.Make.key_before
      order address old_address) eqn:Hbefore.
    + constructor; [exact Hvalue | constructor; assumption].
    + destruct (RocqOfOCaml.OCamlMap.Make.key_equal
        order address old_address) eqn:Hequal.
      * constructor; assumption.
      * constructor; assumption.
Qed.

Lemma map_of_list_preserves_property
    (entries : list (key * A)) :
  Forall (fun entry : key * A => property (snd entry)) entries ->
  Forall (fun entry : key * A => property (snd entry))
    (@RocqOfOCaml.OCamlMap.Make.of_list key order A entries).
Proof.
  intro Hentries.
  induction Hentries as [|[address value] tail Hvalue Htail IH].
  - constructor.
  - cbn [RocqOfOCaml.OCamlMap.Make.of_list].
    apply map_add_preserves_property; assumption.
Qed.

Lemma map_find_opt_preserves_property
    (address : key) (map : RocqOfOCaml.OCamlMap.Make.t A)
    (value : A) :
  Forall (fun entry : key * A => property (snd entry)) map ->
  @RocqOfOCaml.OCamlMap.Make.find_opt key order A address map =
    Some value ->
  property value.
Proof.
  intros Hmap Hlookup.
  induction Hmap as [|[old_address old_value] tail Hold Htail IH].
  - discriminate Hlookup.
  - cbn [RocqOfOCaml.OCamlMap.Make.find_opt] in Hlookup.
    destruct (RocqOfOCaml.OCamlMap.Make.key_before
      order address old_address) eqn:Hbefore.
    + discriminate Hlookup.
    + destruct (RocqOfOCaml.OCamlMap.Make.key_equal
        order address old_address) eqn:Hequal.
      * inversion Hlookup; subst. exact Hold.
      * apply IH. exact Hlookup.
Qed.

Lemma map_lookup_of_list_preserves_property
    (entries : list (key * A)) (address : key) (value : A) :
  Forall (fun entry : key * A => property (snd entry)) entries ->
  @RocqOfOCaml.OCamlMap.Make.find_opt key order A address
    (@RocqOfOCaml.OCamlMap.Make.of_list key order A entries) =
    Some value ->
  property value.
Proof.
  intros Hentries Hlookup.
  eapply map_find_opt_preserves_property.
  - apply map_of_list_preserves_property. exact Hentries.
  - exact Hlookup.
Qed.
End MapLookup.

Definition precompile_result_gas_bounded
    (precompile : MonadVM.Precompiles.Utils.ethereum_precompile) : Prop :=
  forall msg : MonadVM.Evmc.Message.t,
    valid_int64_repr msg.(MonadVM.Evmc.Message.t.gas) ->
    (RocqOfOCaml.OCamlZ.of_int64_unsigned
      (precompile msg).(MonadVM.Evmc.Result.t.gas_left)
      <= RocqOfOCaml.OCamlZ.of_int64_unsigned
        msg.(MonadVM.Evmc.Message.t.gas))%Z.

Lemma selected_precompile_gas_bounded
    {key : Set} (order : RocqOfOCaml.OCamlMap.OrderedType (t := key))
    (entries : list (key * MonadVM.Precompiles.Utils.ethereum_precompile))
    (address : key) (precompile : MonadVM.Precompiles.Utils.ethereum_precompile) :
  Forall (fun entry => precompile_result_gas_bounded (snd entry))
    entries ->
  @RocqOfOCaml.OCamlMap.Make.find_opt key order
    MonadVM.Precompiles.Utils.ethereum_precompile address
    (@RocqOfOCaml.OCamlMap.Make.of_list key order
      MonadVM.Precompiles.Utils.ethereum_precompile entries) =
    Some precompile ->
  precompile_result_gas_bounded precompile.
Proof.
  apply map_lookup_of_list_preserves_property.
Qed.

Lemma selected_address_precompile_gas_bounded
    (entries : list
      (MonadVM.Chain.Ethereum.Address.t *
        MonadVM.Precompiles.Utils.ethereum_precompile))
    (address : MonadVM.Chain.Ethereum.Address.t)
    (precompile : MonadVM.Precompiles.Utils.ethereum_precompile) :
  Forall (fun entry => precompile_result_gas_bounded (snd entry))
    entries ->
  MonadVM.Chain.Ethereum.Address.Map.find_opt address
    (MonadVM.Chain.Ethereum.Address.Map.of_list entries) =
    Some precompile ->
  precompile_result_gas_bounded precompile.
Proof.
  intros Hentries Hlookup.
  eapply selected_precompile_gas_bounded.
  - exact Hentries.
  - exact Hlookup.
Qed.
