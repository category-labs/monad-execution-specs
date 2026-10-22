(** Termination certificates for recursive Merkle Patricia Trie conversions. *)

From Stdlib Require Import Lia List Arith.Wf_nat.
Require Import MonadVM.Rlp.

Import ListNotations.

Fixpoint rlp_size (value : MonadVM.Rlp.t) : nat :=
  match value with
  | MonadVM.Rlp.Bytes _ => 1
  | MonadVM.Rlp.List values =>
      let fix list_size (values : list MonadVM.Rlp.t) : nat :=
        match values with
        | [] => 0
        | value :: values => rlp_size value + list_size values
        end
      in S (list_size values)
  end.

(** The even phase decodes a full node.  The odd phase classifies an encoded
    child as an inline node or a hash. *)
Definition node_of_rlp_rank
    (call : MonadVM.Rlp.t + MonadVM.Rlp.t) : nat :=
  match call with
  | inl value => 2 * rlp_size value
  | inr value => 2 * rlp_size value + 1
  end.

Lemma node_of_rlp_list_child_decreases
    (child : MonadVM.Rlp.t) (values : list MonadVM.Rlp.t) :
  In child values ->
  (node_of_rlp_rank (inr child) <
   node_of_rlp_rank (inl (MonadVM.Rlp.List values)))%nat.
Proof.
  intros Hchild.
  induction values as [|head tail IH].
  - inversion Hchild.
  - cbn [node_of_rlp_rank rlp_size] in *.
    destruct Hchild as [<- | Hchild].
    + lia.
    + specialize (IH Hchild).
      lia.
Qed.

Lemma node_of_rlp_helper_phase_decreases (value : MonadVM.Rlp.t) :
  (node_of_rlp_rank (inl value) < node_of_rlp_rank (inr value))%nat.
Proof.
  unfold node_of_rlp_rank.
  lia.
Qed.

Ltac solve_node_of_rlp_decrease :=
  match goal with
  | call_equation : ?call = inl ?state |- _ => rewrite call_equation
  | call_equation : ?call = inr ?state |- _ => rewrite call_equation
  end;
  unfold ltof;
  match goal with
  | [ measure := _ : _ -> nat |- _ ] => unfold measure
  end;
  cbn beta iota zeta;
  repeat match goal with
  | equation : ?scrutinee = (?value, ?flag) |- _ =>
      lazymatch type of value with
      | MonadVM.Rlp.t =>
          let body := (eval cbv delta in scrutinee) in
          lazymatch body with
          | (?state, ?computed_flag) =>
              change (body = (value, flag)) in equation;
              let Hstate := fresh "Hstate" in
              assert (Hstate : state = value) by congruence;
              rewrite Hstate;
              clear Hstate equation
          end
      end
  end;
  first
    [ apply node_of_rlp_helper_phase_decreases
    | eapply node_of_rlp_list_child_decreases;
      cbn;
      tauto ].
