(** A finite-tree precondition for native Patricia nodes.

    [Address] represents physical node identity, so repeated addresses model
    sharing and cycles that are absent from the generated inductive tree.
    [children] records the child pointers of Branch and Extension nodes.
    Accessibility under that edge relation is the required precondition for
    unfolding a native value into a finite tree. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.

Inductive patricia_kind :=
| NativeEmpty | NativeBranch | NativeLeaf | NativeExtension.

Inductive finite_patricia_tree :=
| FiniteNode : patricia_kind -> list finite_patricia_tree ->
    finite_patricia_tree.

Fixpoint map_with_membership {A B : Type} (values : list A) :
    (forall value, In value values -> B) -> list B :=
  match values as current return
      (forall value, In value current -> B) -> list B with
  | [] => fun _ => []
  | value :: rest => fun f =>
      f value (or_introl eq_refl) ::
      map_with_membership rest (fun other Hin =>
        f other (or_intror Hin))
  end.

Lemma map_with_membership_length {A B : Type} (values : list A)
    (f : forall value, In value values -> B) :
  length (map_with_membership values f) = length values.
Proof.
  induction values as [|value rest IH]; simpl.
  - reflexivity.
  - f_equal. apply IH.
Qed.

Lemma map_with_membership_Forall {A B : Type} (values : list A)
    (f : forall value, In value values -> B) (P : B -> Prop) :
  (forall value Hedge, P (f value Hedge)) ->
  Forall P (map_with_membership values f).
Proof.
  revert f.
  induction values as [|value rest IH]; intros f Hall; simpl.
  - constructor.
  - constructor.
    + apply Hall.
    + apply IH. intros child Hedge. apply Hall.
Qed.

Inductive finite_tree_shape : finite_patricia_tree -> Prop :=
| finite_empty_shape : finite_tree_shape (FiniteNode NativeEmpty [])
| finite_leaf_shape : finite_tree_shape (FiniteNode NativeLeaf [])
| finite_extension_shape child :
    finite_tree_shape child ->
    finite_tree_shape (FiniteNode NativeExtension [child])
| finite_branch_shape children :
    length children = 16 -> Forall finite_tree_shape children ->
    finite_tree_shape (FiniteNode NativeBranch children).

Section NativeGraph.
  Context {Address : Type}.
  Variable kind : Address -> patricia_kind.
  Variable children : Address -> list Address.

  Definition child_of (child parent : Address) : Prop :=
    In child (children parent).

  Definition finite_at (root : Address) : Prop :=
    Acc child_of root.

  (** The native constructors have these child counts. This is separate from
      finiteness: a finite but malformed branch array is still malformed. *)
  Definition shape_valid (node : Address) : Prop :=
    match kind node with
    | NativeEmpty | NativeLeaf => children node = []
    | NativeExtension => exists child, children node = [child]
    | NativeBranch => length (children node) = 16
    end.

  Lemma finite_child (parent child : Address) :
    finite_at parent -> child_of child parent -> finite_at child.
  Proof.
    intros Hfinite Hedge.
    exact (Acc_inv Hfinite Hedge).
  Qed.

  Definition unfold_step (parent : Address)
      (recurse : forall child, child_of child parent -> finite_patricia_tree)
      : finite_patricia_tree :=
    FiniteNode (kind parent)
      (map_with_membership (children parent)
        (fun child Hedge => recurse child Hedge)).

  Definition unfold_tree (root : Address) (Hfinite : finite_at root) :
      finite_patricia_tree :=
    @Fix_F Address child_of (fun _ => finite_patricia_tree)
      unfold_step root Hfinite.

  Lemma unfold_tree_step (root : Address) (Hfinite : finite_at root) :
    unfold_tree root Hfinite =
      FiniteNode (kind root)
        (map_with_membership (children root)
          (fun child Hedge =>
            unfold_tree child (Acc_inv Hfinite Hedge))).
  Proof.
    unfold unfold_tree at 1.
    rewrite <- Fix_F_eq.
    reflexivity.
  Qed.

  Inductive path : nat -> Address -> Address -> Prop :=
  | path_here (node : Address) : path 0 node node
  | path_step (steps : nat) (parent child final : Address) :
      child_of child parent ->
      path steps child final ->
      path (S steps) parent final.

  Lemma path_append (first second : nat)
      (start middle final : Address) :
    path first start middle -> path second middle final ->
    path (first + second) start final.
  Proof.
    intros Hfirst Hsecond.
    induction Hfirst.
    - exact Hsecond.
    - simpl. eapply path_step; eauto.
  Qed.

  Lemma finite_descendant (steps : nat)
      (root descendant : Address) :
    path steps root descendant ->
    finite_at root -> finite_at descendant.
  Proof.
    intro Hpath.
    induction Hpath; intro Hfinite.
    - exact Hfinite.
    - apply IHHpath. eapply finite_child; eauto.
  Qed.

  (** A faithful graph view of a native [PatriciaTrie.t] must include every
      physical child, preserve the Branch array order, and classify the
      four constructors correctly. Under that representation relation this
      predicate is the finite-tree precondition for lookup. *)
  Definition native_finite_tree (root : Address) : Prop :=
    finite_at root /\
    forall steps node, path steps root node -> shape_valid node.

  Definition unfold_native (root : Address)
      (Hnative : native_finite_tree root) : finite_patricia_tree :=
    unfold_tree root (proj1 Hnative).

  Theorem unfold_native_shape (root : Address)
      (Hnative : native_finite_tree root) :
    finite_tree_shape (unfold_native root Hnative).
  Proof.
    assert (Hwell : forall node (Hfinite : finite_at node),
        (forall steps descendant,
          path steps node descendant -> shape_valid descendant) ->
        finite_tree_shape (unfold_tree node Hfinite)).
    { fix IH 2.
      intros node Hfinite Hshape.
      destruct Hfinite as [Hchildren].
      rewrite unfold_tree_step.
      set (converted :=
        map_with_membership (children node)
          (fun child Hedge =>
            unfold_tree child (Acc_inv (Acc_intro node Hchildren) Hedge))).
      assert (Hlength : length converted = length (children node)).
      { unfold converted. apply map_with_membership_length. }
      assert (Hall : Forall finite_tree_shape converted).
      { unfold converted. apply map_with_membership_Forall.
        intros child Hedge.
        apply IH.
        intros steps descendant Hpath.
        apply (Hshape (S steps) descendant).
        eapply path_step; eauto. }
      pose proof (Hshape 0 node (path_here node)) as Hroot.
      unfold shape_valid in Hroot.
      destruct (kind node) eqn:Hkind; simpl in Hroot.
      - rewrite Hroot in Hlength.
        destruct converted as [|child rest]; [constructor | discriminate].
      - apply finite_branch_shape.
        + rewrite Hlength. exact Hroot.
        + exact Hall.
      - rewrite Hroot in Hlength.
        destruct converted as [|child rest]; [constructor | discriminate].
      - destruct Hroot as [child Hchildren_eq].
        rewrite Hchildren_eq in Hlength.
        destruct converted as [|first rest]; [discriminate |].
        destruct rest as [|second rest]; [|discriminate].
        apply finite_extension_shape.
        inversion Hall; assumption. }
    apply Hwell. exact (proj2 Hnative).
  Qed.

  Lemma native_finite_tree_child (parent child : Address) :
    native_finite_tree parent -> child_of child parent ->
    native_finite_tree child.
  Proof.
    intros [Hfinite Hshape] Hedge.
    split.
    - eapply finite_child; eauto.
    - intros steps node Hpath.
      apply (Hshape (S steps) node).
      eapply path_step; eauto.
  Qed.

  Theorem finite_at_excludes_cycles (root : Address) :
    finite_at root ->
    forall steps, ~ path (S steps) root root.
  Proof.
    intro Hfinite.
    induction Hfinite as [root Hchildren IH].
    intros steps Hcycle.
    inversion Hcycle as
      [|previous parent child final Hedge Htail]; subst.
    assert (Hback : path 1 root child).
    { eapply path_step; [exact Hedge | constructor]. }
    pose proof (path_append steps 1 child root child
      Htail Hback) as Hchild_cycle.
    replace (steps + 1)%nat with (S steps)
      in Hchild_cycle by lia.
    exact (IH child Hedge steps Hchild_cycle).
  Qed.

  Corollary native_finite_tree_excludes_cycles (root : Address) :
    native_finite_tree root ->
    forall steps, ~ path (S steps) root root.
  Proof.
    intros [Hfinite _].
    apply finite_at_excludes_cycles. exact Hfinite.
  Qed.
End NativeGraph.
