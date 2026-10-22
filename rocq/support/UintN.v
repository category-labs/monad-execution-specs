(** An executable [N]-backed model of [Numeric.Uint].

    The OCaml module represents arbitrary-width unsigned integers using an
    abstract, nonnegative subset of [Z.t].  Using [N] here makes that invariant
    intrinsic to the Rocq type.  Operations that can raise in OCaml retain an
    [Unreachable] argument; callers must prove that those exceptional cases are
    not reached before relying on their result. *)

Require Import RocqOfOCaml.RocqOfOCaml.
Require Import MonadVM.Byte_string.
Require Import MonadVM.Map.
Require Import MonadVM.Rlp.

Local Open Scope Z_scope.

Module Impl.
  Definition t : Set := N.
End Impl.

Definition t : Set := Impl.t.

Definition signed : bool := false.
Definition max_t : option t := None.
Definition min_t : option t := Some 0%N.

Definition to_z (value : t) : Z := Z.of_N value.

Definition in_range (value : Z) : bool := Z.leb 0 value.

Definition of_z_opt (value : Z) : option t :=
  if in_range value then Some (Z.to_N value) else None.

Definition of_z_truncating
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable t} :
    option (Z -> t) := None.

Definition of_z_exn
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable t}
    (value : Z) : t :=
  match of_z_opt value with
  | Some result => result
  | None => RocqOfOCaml.Basics.unreachable
  end.

Definition zero
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable t} : t := 0%N.

Definition one
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable t} : t := 1%N.

Definition testbit (value : t) (index : int) : bool :=
  Z.testbit (to_z value) index.

(** [rocq-of-ocaml] represents an included OCaml module both as a module
    namespace and as a record-valued package.  The namespace [Impl] above
    supports paths such as [Impl.t]; this package supplies the corresponding
    value exposed by [include Numeric.Uint]. *)
Record impl_signature : Type := {
  impl_signed : bool;
  impl_max_t : option t;
  impl_min_t : option t;
  impl_in_range : Z -> bool;
  impl_of_z_opt : Z -> option t;
  impl_of_z_truncating :
    forall `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable t},
      option (Z -> t);
  impl_to_z : t -> Z;
  impl_testbit : t -> int -> bool;
}.

Definition Impl : impl_signature :=
  {|
    impl_signed := signed;
    impl_max_t := max_t;
    impl_min_t := min_t;
    impl_in_range := in_range;
    impl_of_z_opt := of_z_opt;
    impl_of_z_truncating := @of_z_truncating;
    impl_to_z := to_z;
    impl_testbit := testbit;
  |}.

Definition byte
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable ascii}
    (index_le : int) (value : t) : ascii :=
  if Z.ltb index_le 0 then
    RocqOfOCaml.Basics.unreachable
  else
    ascii_of_N
      (N.land (N.shiftr value (8 * Z.to_N index_le)%N) 255%N).

Definition significant_bits (value : t) : int :=
  if N.eqb value 0%N then 0 else Z.of_N (N.succ (N.log2 value)).

Definition significant_bytes (value : t) : int :=
  Z.div (significant_bits value + 7) 8.

Definition of_bool
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable t}
    (value : bool) : t :=
  if value then 1%N else 0%N.

Definition of_byte
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable t}
    (value : ascii) : t := N_of_ascii value.

Definition of_int
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable t}
    (value : int) : t := of_z_exn value.

Definition op_tildedollar
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable t} : int -> t :=
  of_int.

Definition to_int
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable int}
    (value : t) : int := RocqOfOCaml.OCamlZ.to_int (to_z value).

Definition to_int_opt
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable int}
    (value : t) : option int :=
  if RocqOfOCaml.OCamlZ.fits_int (to_z value) then
    Some (RocqOfOCaml.OCamlZ.to_int (to_z value))
  else None.

Definition of_uint64
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable t}
    (value : int64) : t :=
  of_z_exn (RocqOfOCaml.OCamlZ.of_int64_unsigned value).

Definition of_int64
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable t}
    (value : int64) : t := of_z_exn value.

Definition to_uint64
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable int64}
    (value : t) : int64 :=
  RocqOfOCaml.OCamlZ.to_int64_unsigned (to_z value).

Definition to_int64
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable int64}
    (value : t) : int64 := RocqOfOCaml.OCamlZ.to_int64 (to_z value).

Definition of_uint32
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable t}
    (value : int32) : t :=
  of_z_exn (RocqOfOCaml.OCamlZ.of_int32_unsigned value).

Definition of_int32
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable t}
    (value : int32) : t := of_z_exn value.

Definition to_uint32
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable int32}
    (value : t) : int32 :=
  RocqOfOCaml.OCamlZ.to_int32_unsigned (to_z value).

Definition to_int32
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable int32}
    (value : t) : int32 := RocqOfOCaml.OCamlZ.to_int32 (to_z value).

Definition hash (value : t) : int := RocqOfOCaml.OCamlZ.hash (to_z value).

Definition compare (left right : t) : int :=
  match N.compare left right with
  | Lt => -1
  | Eq => 0
  | Gt => 1
  end.

Definition ordered_type : MonadVM.Map.OrderedType (t := t) :=
  {| RocqOfOCaml.OCamlMap.OrderedType.compare := compare |}.

Definition _Set := RocqOfOCaml.OCamlSet.Make ordered_type.
Definition Map := MonadVM.Map.Make ordered_type.

Definition comparison_op (int_cmp : int -> int -> bool) (left right : t) :
    bool := int_cmp (compare left right) 0.

Definition op_lt (left right : t) : bool := N.ltb left right.
Definition op_lteq (left right : t) : bool := N.leb left right.
Definition op_eq (left right : t) : bool := N.eqb left right.
Definition op_gteq (left right : t) : bool := N.leb right left.
Definition op_gt (left right : t) : bool := N.ltb right left.
Definition op_ltgt (left right : t) : bool := negb (N.eqb left right).
Definition equal : t -> t -> bool := op_eq.

Definition max (left right : t) : t :=
  if N.ltb left right then right else left.

Definition min (left right : t) : t :=
  if N.ltb left right then left else right.

Definition is_zero
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable t}
    (value : t) : bool := N.eqb value 0%N.

Definition to_string (value : t) : string :=
  RocqOfOCaml.OCamlZ.to_string (to_z value).

Definition to_hex_string (value : t) : string :=
  RocqOfOCaml.OCamlZ.format "%#x" (to_z value).

(** Use the same parser and nonnegativity check as [Numeric.Uint.of_string]. *)
Definition of_string
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable Z}
    `{_rocq_assumption_1 : RocqOfOCaml.Basics.Unreachable t}
    (value : string) : t :=
  match RocqOfOCaml.OCamlZ.of_string_opt value with
  | Some result => of_z_exn result
  | None => RocqOfOCaml.Basics.unreachable
  end.

Definition op_tildeat
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable Z}
    `{_rocq_assumption_1 : RocqOfOCaml.Basics.Unreachable t} : string -> t :=
  of_string.

Definition of_z_after_op
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable t} : Z -> t :=
  of_z_exn.

Definition lift_1
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable t}
    (operation : Z -> Z) (value : t) : t :=
  of_z_after_op (operation (to_z value)).

Definition lift_2
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable t}
    (operation : Z -> Z -> Z) (left right : t) : t :=
  of_z_after_op (operation (to_z left) (to_z right)).

Definition logand
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable t}
    (left right : t) : t := N.land left right.

Definition logor
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable t}
    (left right : t) : t := N.lor left right.

Definition logxor
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable t}
    (left right : t) : t := N.lxor left right.

Definition lognot
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable t}
    (_value : t) : t := RocqOfOCaml.Basics.unreachable.

Definition op_plus
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable t}
    (left right : t) : t := (left + right)%N.

Definition op_minus
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable t}
    (left right : t) : t :=
  if N.leb right left then (left - right)%N
  else RocqOfOCaml.Basics.unreachable.

Definition op_star
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable t}
    (left right : t) : t := (left * right)%N.

Definition op_div
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable t}
    (left right : t) : t :=
  if N.eqb right 0%N then RocqOfOCaml.Basics.unreachable
  else N.div left right.

Definition modulo
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable t}
    (left right : t) : t :=
  if N.eqb right 0%N then RocqOfOCaml.Basics.unreachable
  else N.modulo left right.

Definition rem
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable t} : t -> t -> t :=
  modulo.

Definition addmod
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable t}
    (left right modulus : t) : t := modulo (left + right)%N modulus.

Definition mulmod
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable t}
    (left right modulus : t) : t := modulo (left * right)%N modulus.

Definition shift_left
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable t}
    (value : t) (shift : int) : t :=
  if Z.ltb shift 0 then RocqOfOCaml.Basics.unreachable
  else Z.to_N (Z.shiftl (to_z value) shift).

Definition shift_right
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable t}
    (value : t) (shift : int) : t :=
  if Z.ltb shift 0 then RocqOfOCaml.Basics.unreachable
  else Z.to_N (Z.shiftr (to_z value) shift).

Definition op_starstar
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable t}
    (base : t) (exponent : int) : t :=
  if Z.ltb exponent 0 then RocqOfOCaml.Basics.unreachable
  else N.pow base (Z.to_N exponent).

Definition exp_mod
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable Z}
    `{_rocq_assumption_1 : RocqOfOCaml.Basics.Unreachable t}
    (modulo_value x_value y_value : t) : t :=
  if N.eqb modulo_value 0%N then RocqOfOCaml.Basics.unreachable
  else
    Z.to_N
      (RocqOfOCaml.OCamlZ.powm (to_z x_value) (to_z y_value)
        (to_z modulo_value)).

Definition minus_1_64th
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable t}
    (value : t) : t := (value - N.div value 64)%N.

Definition bytes_to_whole_words
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable t}
    (value : t) : t := N.div (value + 31)%N 32%N.

Definition as_signed
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable Z}
    (value : t) : Z := to_z value.

Fixpoint reverse_append (value suffix : string) : string :=
  match value with
  | EmptyString => suffix
  | String byte rest => reverse_append rest (String byte suffix)
  end.

Definition reverse (value : string) : string :=
  reverse_append value EmptyString.

Definition of_bytes_be
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable ascii}
    `{_rocq_assumption_1 : RocqOfOCaml.Basics.Unreachable t}
    (value : MonadVM.Byte_string.Bytes.t) : t :=
  Z.to_N (RocqOfOCaml.OCamlZ.of_bits (reverse value)).

Definition to_bytes_be
    `{_rocq_assumption_0 :
      RocqOfOCaml.Basics.Unreachable MonadVM.Byte_string.Bytes.t}
    `{_rocq_assumption_1 : RocqOfOCaml.Basics.Unreachable ascii}
    (value : t) : MonadVM.Byte_string.Bytes.t :=
  reverse (RocqOfOCaml.OCamlZ.to_bits (to_z value)).

Definition of_rlp
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable ascii}
    `{_rocq_assumption_1 : RocqOfOCaml.Basics.Unreachable t}
    (value : MonadVM.Rlp.t) : option t :=
  match value with
  | MonadVM.Rlp.Bytes bytes =>
      let result := of_bytes_be bytes in
      (* [Numeric.Uint.of_rlp] requires the shortest integer encoding. *)
      if Z.eqb (significant_bytes result)
          (RocqOfOCaml.OCamlString.length bytes)
      then Some result else None
  | MonadVM.Rlp.List _ => None
  end.

Definition to_rlp
    `{_rocq_assumption_0 :
      RocqOfOCaml.Basics.Unreachable MonadVM.Byte_string.Bytes.t}
    `{_rocq_assumption_1 : RocqOfOCaml.Basics.Unreachable ascii}
    (value : t) : MonadVM.Rlp.t := MonadVM.Rlp.Bytes (to_bytes_be value).

Definition ceil_div
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable t}
    (left right : t) : t :=
  op_div (op_minus (op_plus left right) 1%N) right.

Definition div_rem
    `{_rocq_assumption_0 : RocqOfOCaml.Basics.Unreachable t}
    (left right : t) : t * t :=
  if N.eqb right 0%N then
    (RocqOfOCaml.Basics.unreachable, RocqOfOCaml.Basics.unreachable)
  else (N.div left right, N.modulo left right).

(** The representation is a faithful refinement of nonnegative [Z]. *)
Lemma to_z_nonnegative (value : t) : (0 <= to_z value)%Z.
Proof.
  apply N2Z.is_nonneg.
Qed.

Lemma of_z_opt_nonnegative (value : Z) :
  (0 <= value)%Z -> of_z_opt value = Some (Z.to_N value).
Proof.
  intros Hvalue.
  unfold of_z_opt, in_range.
  assert (Hleb : Z.leb 0 value = true).
  { apply Z.leb_le. exact Hvalue. }
  rewrite Hleb.
  reflexivity.
Qed.

Lemma to_z_of_z_nonnegative (value : Z) :
  (0 <= value)%Z -> to_z (Z.to_N value) = value.
Proof.
  apply Z2N.id.
Qed.

Lemma to_z_plus `{RocqOfOCaml.Basics.Unreachable t} (left right : t) :
  to_z (op_plus left right) = (to_z left + to_z right)%Z.
Proof.
  apply N2Z.inj_add.
Qed.

Lemma to_z_mul `{RocqOfOCaml.Basics.Unreachable t} (left right : t) :
  to_z (op_star left right) = (to_z left * to_z right)%Z.
Proof.
  apply N2Z.inj_mul.
Qed.

Lemma to_z_minus `{RocqOfOCaml.Basics.Unreachable t} (left right : t) :
  (right <= left)%N ->
  to_z (op_minus left right) = (to_z left - to_z right)%Z.
Proof.
  intros Hle.
  unfold op_minus.
  assert (Hleb : N.leb right left = true).
  { apply N.leb_le. exact Hle. }
  rewrite Hleb.
  apply N2Z.inj_sub.
  exact Hle.
Qed.
