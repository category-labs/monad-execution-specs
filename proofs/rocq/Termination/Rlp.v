(** Termination of the mutually recursive RLP decoders.

    [decode_all] may call [decode_first] on the same input. All other
    recursive edges must consume bytes, including when an exceptional
    primitive has been supplied an arbitrary [Unreachable] fallback. *)

From Stdlib Require Import String Ascii ZArith Lia Arith.Wf_nat.
Require Import RocqOfOCaml.OCamlString.
Require Import RocqOfOCaml.Unreachable.StringBounds.

Local Open Scope Z_scope.

Definition decode_rank (call : string + string) : nat :=
  match call with
  | inl bytes => 2 * Strings.String.length bytes
  | inr bytes => 2 * Strings.String.length bytes + 1
  end.

Lemma decode_all_to_first_decreases (bytes : string) :
  (decode_rank (inl bytes) < decode_rank (inr bytes))%nat.
Proof. unfold decode_rank; lia. Qed.

Lemma decode_first_to_all_decreases (bytes payload : string) :
  OCamlString.length payload < OCamlString.length bytes ->
  (decode_rank (inr payload) < decode_rank (inl bytes))%nat.
Proof. unfold decode_rank, OCamlString.length; lia. Qed.

Lemma decode_all_to_all_decreases (bytes rest : string) :
  OCamlString.length rest < OCamlString.length bytes ->
  (decode_rank (inr rest) < decode_rank (inr bytes))%nat.
Proof. unfold decode_rank, OCamlString.length; lia. Qed.

Ltac solve_decode_decrease :=
  match goal with
  | equation : ?call = inl ?state |- _ => rewrite equation
  | equation : ?call = inr ?state |- _ => rewrite equation
  end;
  unfold ltof;
  match goal with
  | [ measure := _ : _ -> nat |- _ ] => unfold measure
  end;
  cbn beta iota zeta;
  first
    [ apply decode_all_to_first_decreases
    | apply decode_first_to_all_decreases; apply Z.ltb_lt; assumption
    | apply decode_all_to_all_decreases; apply Z.ltb_lt; assumption ].

(** Both the list payload and the remainder start after at least the tag.
    Whenever their substring bounds are valid, the new progress guards are
    true regardless of the exceptional fallback instance. *)
Lemma bounded_slice_progress
    `{RocqOfOCaml.Basics.Unreachable string}
    (bytes : string) (start count : Z) :
  0 < start -> 0 <= count -> start + count <= OCamlString.length bytes ->
  Z.ltb (OCamlString.length (OCamlString.sub bytes start count))
    (OCamlString.length bytes) = true.
Proof.
  intros Hstart Hcount Hbound.
  rewrite sub_length_in_bounds by lia.
  apply Z.ltb_lt; lia.
Qed.

Lemma bounded_remainder_progress
    `{RocqOfOCaml.Basics.Unreachable string}
    (bytes : string) (consumed : Z) :
  0 < consumed -> consumed <= OCamlString.length bytes ->
  Z.ltb (OCamlString.length
    (OCamlString.sub bytes consumed (OCamlString.length bytes - consumed)))
    (OCamlString.length bytes) = true.
Proof.
  intros Hpositive Hbound.
  apply bounded_slice_progress; lia.
Qed.

(** A one-byte truncated list declares one payload byte that is absent.
    Native [String.sub] raises. The compatibility model's exceptional
    branch can instead return the original input. Before the explicit
    progress checks, this created the cycle
    [decode_first bytes -> decode_all bytes -> decode_first bytes]. *)
Definition truncated_list : string :=
  String (ascii_of_nat 193) EmptyString.

Example exceptional_substring_can_repeat_input :
  @OCamlString.sub
    {| RocqOfOCaml.Basics.unreachable := truncated_list |}
    truncated_list 1 1 = truncated_list.
Proof. reflexivity. Qed.

Example exceptional_remainder_can_repeat_input :
  @OCamlString.sub
    {| RocqOfOCaml.Basics.unreachable := truncated_list |}
    truncated_list 2 (-1) = truncated_list.
Proof. reflexivity. Qed.

Example repeated_input_does_not_decrease :
  ~ (decode_rank (inr truncated_list) <
     decode_rank (inl truncated_list))%nat.
Proof. unfold decode_rank; lia. Qed.
