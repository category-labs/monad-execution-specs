(** The successful reserve-balance precompile spends exactly 100 gas. *)

From Stdlib Require Import ZArith Lia.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import MonadExecutionSpecs.Termination.VmUnsignedGas.
Require Import MonadExecutionSpecs.Termination.VmPrecompileTableGasBound.
Require MonadVM.Gas.
Require MonadVM.Precompiles.
Require MonadVM.Precompiles.Reserve_balance_introspection.
Require MonadVM.Support.UintN.

Local Open Scope Z_scope.

Section ReserveBalanceGas.
Context `{UGas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
Context `{UInt64 : RocqOfOCaml.Basics.Unreachable int64}.

Lemma reserve_gas_after_success_bounded (raw : Z) :
  valid_int64_repr raw ->
  (100 <= MonadVM.Gas.of_uint64 raw)%N ->
  (RocqOfOCaml.OCamlZ.of_int64_unsigned
      (MonadVM.Gas.to_uint64
        (MonadVM.Gas.op_minus
          (MonadVM.Gas.of_uint64 raw) 100%N))
    <= RocqOfOCaml.OCamlZ.of_int64_unsigned raw)%Z.
Proof.
  intros Hvalid Hafford.
  pose proof (unsigned_repr_in_range raw Hvalid) as [Hnonnegative Hupper].
  pose proof (initial_gas_matches_unsigned raw Hnonnegative) as Hinitial.
  assert (Hleb : N.leb 100 (MonadVM.Gas.of_uint64 raw) = true).
  { apply N.leb_le. exact Hafford. }
  unfold MonadVM.Gas.op_minus, MonadVM.Support.UintN.op_minus.
  rewrite Hleb.
  rewrite uintn_to_uint64_roundtrip.
  - lia.
  - lia.
Qed.
End ReserveBalanceGas.

Section ReserveBalanceAction.
Context `{F : MonadVM.Precompiles.Reserve_balance_introspection.Make.FArgs}.
Context `{U0 : RocqOfOCaml.Basics.Unreachable
  (RocqOfOCaml.OCamlSeq.t
    (MonadVM.Chain.Ethereum.Address.Map.key * MonadVM.Chain.Ethereum.Account.t))}.
Context `{U1 : RocqOfOCaml.Basics.Unreachable (RocqOfOCaml.OCamlIarray.t int)}.
Context `{U2 : RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}.
Context `{U3 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U64.t}.
Context `{U4 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
Context `{U5 : RocqOfOCaml.Basics.Unreachable MonadVM.Int64.t}.
Context `{U6 : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
Context `{U7 : RocqOfOCaml.Basics.Unreachable MonadVM.Chain.Ethereum.Address.t}.
Context `{U8 : RocqOfOCaml.Basics.Unreachable unit}.
Context `{U9 : RocqOfOCaml.Basics.Unreachable string}.
Context `{U10 : RocqOfOCaml.Basics.Unreachable int}.
Context `{U11 : RocqOfOCaml.Basics.Unreachable ascii}.
Context `{U12 : RocqOfOCaml.Basics.Unreachable (int * int)}.

Lemma generated_reserve_balance_precompile_gas_bounded
    (msg : MonadVM.Evmc.Message.t)
    (state : MonadVM.State.TransactionState.t) :
  valid_int64_repr msg.(MonadVM.Evmc.Message.t.gas) ->
  (RocqOfOCaml.OCamlZ.of_int64_unsigned
      (fst ((@MonadVM.Precompiles.Reserve_balance_introspection.Make.precompile
        F U0 U1 U2 U3 U4 U5 U6 U7 U8 U9 U10 U11 U12 msg) state))
        .(MonadVM.Evmc.Result.t.gas_left)
    <= RocqOfOCaml.OCamlZ.of_int64_unsigned
       msg.(MonadVM.Evmc.Message.t.gas))%Z.
Proof.
  intro Hvalid.
  unfold MonadVM.Precompiles.Reserve_balance_introspection.Make.precompile.
  destruct (MonadVM.Gas.op_lt
    (MonadVM.Gas.of_uint64 msg.(MonadVM.Evmc.Message.t.gas))
    (MonadVM.Precompiles.Reserve_balance_introspection.Make.gas_dipped_into_reserve
      (_rocq_assumption_0 := U6))) eqn:Hafford.
  - cbn. pose proof (unsigned_repr_in_range _ Hvalid) as [Hnonnegative _].
    lia.
  - destruct (Z.ltb (MonadVM.Byte_string.Bytes.length msg.(MonadVM.Evmc.Message.t.input_data)) 4).
    + cbn. pose proof (unsigned_repr_in_range _ Hvalid) as [Hnonnegative _]. lia.
    + destruct (nequiv_decb
        (MonadVM.Byte_string.Bytes.sub msg.(MonadVM.Evmc.Message.t.input_data) 0 4)
        (MonadVM.Precompiles.Reserve_balance_introspection.Make.selector_dipped_into_reserve)) eqn:Hselector.
      * cbn. pose proof (unsigned_repr_in_range _ Hvalid) as [Hnonnegative _]. lia.
      * destruct (MonadVM.Numeric.U256.op_ltgt msg.(MonadVM.Evmc.Message.t.value)
          MonadVM.Numeric.U256.zero); cbn.
        -- pose proof (unsigned_repr_in_range _ Hvalid) as [Hnonnegative _]. lia.
        -- destruct (Z.gtb (MonadVM.Byte_string.Bytes.length msg.(MonadVM.Evmc.Message.t.input_data)) 4); cbn.
           ++ pose proof (unsigned_repr_in_range _ Hvalid) as [Hnonnegative _]. lia.
           ++ destruct (MonadVM.Reserve_balance.dipped_into_reserve
                 F.(MonadVM.Precompiles.Reserve_balance_introspection.Make.Revision)
                   .(MonadVM.Precompiles.Reserve_balance_introspection.Make_Revision_signature.revision)
                 state) as [dipped state'] eqn:Hdipped.
              cbn.
              apply reserve_gas_after_success_bounded; try assumption.
              unfold MonadVM.Gas.op_lt, MonadVM.Support.UintN.op_lt in Hafford.
              unfold MonadVM.Precompiles.Reserve_balance_introspection.Make.gas_dipped_into_reserve,
                MonadVM.Gas.op_tildedollar, MonadVM.Support.UintN.op_tildedollar,
                MonadVM.Support.UintN.of_int, MonadVM.Support.UintN.of_z_exn,
                MonadVM.Support.UintN.of_z_opt, MonadVM.Support.UintN.in_range in Hafford.
              cbn in Hafford. apply N.ltb_ge in Hafford. exact Hafford.
Qed.
End ReserveBalanceAction.

Definition monad_precompile_gas_bounded
    (precompile : MonadVM.Precompiles.Utils.monad_precompile) : Prop :=
  forall (msg : MonadVM.Evmc.Message.t)
      (state : MonadVM.State.TransactionState.t),
    valid_int64_repr msg.(MonadVM.Evmc.Message.t.gas) ->
    (RocqOfOCaml.OCamlZ.of_int64_unsigned
      (fst (precompile msg state)).(MonadVM.Evmc.Result.t.gas_left)
      <= RocqOfOCaml.OCamlZ.of_int64_unsigned
        msg.(MonadVM.Evmc.Message.t.gas))%Z.

Section MonadTable.
Context `{F : MonadVM.Precompiles.Make.FArgs}.
Context `{U0 : RocqOfOCaml.Basics.Unreachable
  (RocqOfOCaml.OCamlSeq.t
    (MonadVM.Chain.Ethereum.Address.Map.key * MonadVM.Chain.Ethereum.Account.t))}.
Context `{U1 : RocqOfOCaml.Basics.Unreachable (RocqOfOCaml.OCamlIarray.t int)}.
Context `{U2 : RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}.
Context `{U3 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U64.t}.
Context `{U4 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
Context `{U5 : RocqOfOCaml.Basics.Unreachable MonadVM.Int64.t}.
Context `{U6 : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
Context `{U7 : RocqOfOCaml.Basics.Unreachable
  (MonadVM.Chain.Ethereum.Address.Map.t
    MonadVM.Precompiles.Utils.monad_precompile)}.
Context `{U8 : RocqOfOCaml.Basics.Unreachable MonadVM.Chain.Ethereum.Address.t}.
Context `{U9 : RocqOfOCaml.Basics.Unreachable MonadVM.Byte_string.Bytes.t}.
Context `{U10 : RocqOfOCaml.Basics.Unreachable unit}.
Context `{U11 : RocqOfOCaml.Basics.Unreachable string}.
Context `{U12 : RocqOfOCaml.Basics.Unreachable int}.
Context `{U13 : RocqOfOCaml.Basics.Unreachable ascii}.
Context `{U14 : RocqOfOCaml.Basics.Unreachable (int * int)}.

Lemma generated_monad_precompile_table_entry_gas_bounded
    (address : MonadVM.Chain.Ethereum.Address.t)
    (precompile : MonadVM.Precompiles.Utils.monad_precompile) :
  (F.(MonadVM.Precompiles.Make.Revision)
      .(MonadVM.Precompiles.Make_Revision_signature.revision) =
      MonadVM.Support.Variants.Revision.Eight \/
   F.(MonadVM.Precompiles.Make.Revision)
      .(MonadVM.Precompiles.Make_Revision_signature.revision) =
      MonadVM.Support.Variants.Revision.Nine) ->
  MonadVM.Chain.Ethereum.Address.Map.find_opt address
    (@MonadVM.Precompiles.Make.monad_precompiles
      F U0 U1 U2 U3 U4 U5 U6 U7 U8 U9 U10 U11 U12 U13 U14) =
    Some precompile ->
  monad_precompile_gas_bounded precompile.
Proof.
  intros Hrevision Hlookup.
  destruct Hrevision as [Hrevision | Hrevision];
    unfold MonadVM.Precompiles.Make.monad_precompiles in Hlookup;
    rewrite Hrevision in Hlookup; cbn zeta in Hlookup.
  - cbn in Hlookup. discriminate Hlookup.
  - eapply map_lookup_of_list_preserves_property;
      [| exact Hlookup].
    constructor.
    + unfold monad_precompile_gas_bounded.
        intros msg state Hvalid.
        apply generated_reserve_balance_precompile_gas_bounded.
        exact Hvalid.
    + constructor.
Qed.
End MonadTable.
