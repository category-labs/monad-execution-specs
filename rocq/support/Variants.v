Require Import RocqOfOCaml.RocqOfOCaml.

(** Concrete targets for the closed polymorphic-variant rows used by the
    execution model.  This module is project configuration, not translator
    logic: other projects can map their rows to different inductives. *)

Module ByteWidth.
  Inductive t : Set :=
  | Fixed (bytes : Z)
  | VariableWidth.
End ByteWidth.

Module Signedness.
  Inductive t : Set :=
  | Signed
  | Unsigned.
End Signedness.

Module AccessStatus.
  Inductive t : Set :=
  | Warm
  | Cold.
End AccessStatus.

Module Revision.
  Inductive t : Set :=
  | Zero
  | One
  | Two
  | Three
  | Four
  | Five
  | Six
  | Seven
  | Eight
  | Nine
  | Ten
  | Next.
End Revision.

Module MerkleKind.
  Inductive t : Set :=
  | Transactions
  | Withdrawals
  | State
  | Receipts.
End MerkleKind.

Module TransactionKind.
  Inductive t : Set :=
  | Legacy
  | AccessList
  | FeeMarket
  | SetCode.
End TransactionKind.
