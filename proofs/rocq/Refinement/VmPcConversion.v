(** The generated U256-to-machine-int option used by VM dispatch has a
    small, executable expression after unfolding its numeric functor. *)

Require Import RocqOfOCaml.RocqOfOCaml.
Require MonadVM.Numeric.
Require MonadVM.Opcode.
Require MonadVM.String.

Definition pc_to_int_opt
    `{U : RocqOfOCaml.Basics.Unreachable int} (pc : Z) : option int :=
  if RocqOfOCaml.OCamlZ.fits_int pc then
    Some (RocqOfOCaml.OCamlZ.to_int pc)
  else None.

Lemma generated_u256_to_int_opt_eq
    `{U : RocqOfOCaml.Basics.Unreachable int}
    (pc : MonadVM.Numeric.U256.t) :
  MonadVM.Numeric.U256.to_int_opt pc = pc_to_int_opt pc.
Proof. reflexivity. Qed.

Definition selected_opcode_model
    `{U : RocqOfOCaml.Basics.Unreachable int}
    `{A : RocqOfOCaml.Basics.Unreachable ascii}
    (bytecode : string) (pc : Z) : MonadVM.Opcode.t :=
  match pc_to_int_opt pc with
  | Some index =>
      if Z.ltb index (MonadVM.String.length bytecode) then
        MonadVM.Opcode.of_byte (MonadVM.String.get bytecode index)
      else MonadVM.Opcode.Stop
  | None => MonadVM.Opcode.Stop
  end.
