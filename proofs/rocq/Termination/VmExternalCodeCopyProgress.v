(** Gas progress for the generated EXTCODECOPY handler. *)

From Stdlib Require Import List String NArith ZArith Lia.
Require Import RocqOfOCaml.RocqOfOCaml.
Require MonadVM.Byte_string.
Require MonadVM.Chain.Ethereum.
Require MonadVM.Evmc.
Require MonadVM.Gas.
Require MonadVM.Numeric.
Require MonadVM.Support.UintN.
Require MonadVM.Support.Variants.
Require MonadVM.Vm.
Require Import MonadExecutionSpecs.Refinement.UintRlp.
Require Import MonadExecutionSpecs.Termination.VmOpcodeProgress.

Local Open Scope Z_scope.

Lemma ocaml_string_init_nat_length
    (count : nat) (index : int) (element : int -> ascii) :
  Strings.String.length
    (RocqOfOCaml.OCamlString.init_nat count index element) = count.
Proof.
  revert index.
  induction count as [|count IH]; intro index; cbn; [reflexivity|].
  now rewrite IH.
Qed.

Lemma ocaml_string_init_length
    `{Ustring : RocqOfOCaml.Basics.Unreachable string}
    (count : int) (element : int -> ascii) :
  0 <= count ->
  Z.of_nat (Strings.String.length
    (@RocqOfOCaml.OCamlString.init Ustring count element)) = count.
Proof.
  intro Hcount.
  rewrite RocqOfOCaml.OCamlString.init_matches_structural.
  assert (Hnonnegative : (count <? 0) = false)
    by (apply Z.ltb_ge; lia).
  rewrite Hnonnegative.
  rewrite ocaml_string_init_nat_length.
  now rewrite Z2Nat.id by lia.
Qed.

Lemma sub_with_zero_padding_length
    `{Ustring : RocqOfOCaml.Basics.Unreachable string}
    `{Uascii : RocqOfOCaml.Basics.Unreachable ascii}
    (bytes : MonadVM.Byte_string.Bytes.t) (start size : int) :
  0 <= size ->
  Z.of_nat (Strings.String.length
    (@MonadVM.Byte_string.Bytes.sub_with_zero_padding
      Ustring Uascii bytes start size)) = size.
Proof.
  intro Hsize.
  unfold MonadVM.Byte_string.Bytes.sub_with_zero_padding,
    MonadVM.Byte_string.Bytes.init, MonadVM.String.init.
  apply ocaml_string_init_length.
  exact Hsize.
Qed.

Lemma u256_of_uint_exn_exact
    `{U256 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}
    (value : MonadVM.Support.UintN.t) :
  (Z.of_N value < 2 ^ 256)%Z ->
  @MonadVM.Numeric.U256.of_uint_exn U256 value = Z.of_N value.
Proof.
  intro Hvalue.
  unfold MonadVM.Numeric.U256.of_uint_exn.
  cbn.
  unfold MonadVM.Numeric.Make.of_z_exn,
    MonadVM.Numeric.Make.of_z_opt,
    MonadVM.Support.UintN.to_z.
  cbn.
  unfold MonadVM.Numeric.Make.Impl.of_z_opt,
    MonadVM.Numeric.Make.Impl.in_range.
  cbn.
  assert (Hlower : (Z.of_N value >=? Z.zero) = true).
  { apply Z.geb_le. apply N2Z.is_nonneg. }
  assert (Hupper :
    (Z.of_N value <=?
      115792089237316195423570985008687907853269984665640564039457584007913129639935) = true).
  { apply Z.leb_le.
    replace 115792089237316195423570985008687907853269984665640564039457584007913129639935
      with (2 ^ 256 - 1) by reflexivity.
    lia. }
  rewrite ?Hlower, ?Hupper.
  cbn.
  reflexivity.
Qed.

Lemma push_immediate_in_range
    `{Ustring : RocqOfOCaml.Basics.Unreachable string}
    `{Uascii : RocqOfOCaml.Basics.Unreachable ascii}
    `{Uuint : RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}
    `{U256 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}
    (code : MonadVM.Byte_string.Bytes.t) (here size : int) :
  0 <= size <= 32 ->
  let bytes := @MonadVM.Byte_string.Bytes.sub_with_zero_padding
    Ustring Uascii code (here + 1) size in
  (0 <= @MonadVM.Numeric.U256.of_uint_exn U256
    (@MonadVM.Support.UintN.of_bytes_be Uascii Uuint bytes) <
    2 ^ 256)%Z.
Proof.
  intros Hsize bytes.
  pose proof (sub_with_zero_padding_length code (here + 1) size
    (proj1 Hsize)) as Hlength.
  pose proof (@of_bytes_be_bounds Uascii Uuint bytes) as Hdecoded.
  change (0 <= Z.of_N (@MonadVM.Support.UintN.of_bytes_be
    Uascii Uuint bytes) <
    256 ^ Z.of_nat (Strings.String.length bytes)) in Hdecoded.
  unfold bytes in Hdecoded.
  rewrite Hlength in Hdecoded.
  pose proof (Z.pow_le_mono_r 256 size 32 ltac:(lia) ltac:(lia))
    as Hpow.
  replace (256 ^ 32) with (2 ^ 256) in Hpow by reflexivity.
  assert (Hraw :
    (Z.of_N (@MonadVM.Support.UintN.of_bytes_be Uascii Uuint bytes)
      < 2 ^ 256)%Z).
  { unfold bytes. lia. }
  rewrite (u256_of_uint_exn_exact _ Hraw).
  lia.
Qed.

(** A native unsigned word which cannot be converted to an OCaml [int]
    already requires more copy gas than the transaction limit.  Connecting
    the valid-word and entry-gas invariants to all handler calls remains
    necessary before restoring the source assertion. *)
Lemma nonfitting_nonnegative_large (size : Z) :
  0 <= size -> RocqOfOCaml.OCamlZ.fits_int size = false ->
  2 ^ 62 <= size.
Proof.
  intros Hnonnegative Hfit.
  unfold RocqOfOCaml.OCamlZ.fits_int,
    RocqOfOCaml.OCamlZ.fits_signed,
    RocqOfOCaml.OCamlZ.signed_min,
    RocqOfOCaml.OCamlZ.signed_max in Hfit.
  replace (Z.pred 63) with 62 in Hfit by reflexivity.
  destruct (Z.leb (- (2 ^ 62)) size) eqn:Hlower.
  - apply Z.leb_le in Hlower.
    destruct (Z.leb size (Z.pred (2 ^ 62))) eqn:Hupper.
    + discriminate.
    + apply Z.leb_gt in Hupper. lia.
  - apply Z.leb_gt in Hlower. lia.
Qed.

Section CopySizeRange.
  Context `{Uint : RocqOfOCaml.Basics.Unreachable int}.

  Lemma nonfitting_u256_large (size : MonadVM.Numeric.U256.t) :
    0 <= size ->
    MonadVM.Numeric.U256.to_int_opt size = None ->
    2 ^ 62 <= size.
  Proof.
    intros Hnonnegative Hnone.
    apply nonfitting_nonnegative_large; [exact Hnonnegative|].
    destruct (RocqOfOCaml.OCamlZ.fits_int size) eqn:Hfits;
      [exfalso|reflexivity].
    change
      ((if RocqOfOCaml.OCamlZ.fits_int size then
          Some (RocqOfOCaml.OCamlZ.to_int size)
        else None) = None) in Hnone.
    rewrite Hfits in Hnone.
    discriminate.
  Qed.
End CopySizeRange.

Lemma large_size_word_lower_bound (size : Z) :
  2 ^ 62 <= size -> 2 ^ 57 <= size / 32.
Proof.
  intro Hsize.
  pose proof (Z.div_mod size 32 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound size 32 ltac:(lia)) as Hmod.
  replace (2 ^ 62) with (32 * 2 ^ 57) in Hsize by reflexivity.
  lia.
Qed.

Lemma large_size_copy_cost_exceeds_cap (size : Z) :
  2 ^ 62 <= size -> 30_000_000 < 3 * (size / 32).
Proof.
  intro Hsize.
  pose proof (large_size_word_lower_bound size Hsize) as Hwords.
  lia.
Qed.

Section GeneratedWordCount.
  Context `{U256 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
  Context `{Uuint :
    RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}.

  Lemma word_count_exact (size : MonadVM.Numeric.U256.t) :
    0 <= size < 2 ^ 256 ->
    Z.of_N (MonadVM.Numeric.U256.to_uint
      (MonadVM.Numeric.U256.bytes_to_whole_words size)) =
      size / 32 + (if size mod 32 =? 0 then 0 else 1).
  Proof.
    intro Hsize.
    unfold MonadVM.Numeric.U256.to_uint,
      MonadVM.Numeric.U256.bytes_to_whole_words.
    cbn -[Z.quotrem Z.land Z.shiftl].
    unfold MonadVM.Numeric.TwosComplement.Unsigned.to_uint,
      MonadVM.Numeric.Make.bytes_to_whole_words.
    cbn -[Z.quotrem Z.land Z.shiftl].
    unfold MonadVM.Numeric.Make.Impl.to_z,
      MonadVM.Numeric.Make.of_z_exn,
      MonadVM.Support.UintN.of_z_exn,
      RocqOfOCaml.OCamlZ.of_int.
    cbn -[Z.quotrem Z.land Z.shiftl].
    unfold MonadVM.Numeric.Make.Impl.of_z_opt,
      MonadVM.Support.UintN.of_z_opt.
    cbn -[Z.quotrem Z.land Z.shiftl].
    unfold MonadVM.Numeric.Make.Impl.in_range,
      MonadVM.Support.UintN.in_range.
    cbn -[Z.quotrem Z.land Z.shiftl].
    destruct (Z.quotrem size 32) as [q r] eqn:Hqr.
    assert (Hq : q = size / 32).
    { pose proof (Z.quot_div_nonneg size 32 (proj1 Hsize) ltac:(lia)) as H.
      unfold Z.quot in H. rewrite Hqr in H. exact H. }
    assert (Hr : r = size mod 32).
    { pose proof (Z.rem_mod_nonneg size 32 (proj1 Hsize) ltac:(lia)) as H.
      unfold Z.rem in H. rewrite Hqr in H. exact H. }
    assert (Hdiv := Z.div_mod size 32 ltac:(lia)).
    assert (Hmod := Z.mod_pos_bound size 32 ltac:(lia)).
    assert (Hqbound : 0 <= q < 2 ^ 256 - 1) by lia.
    replace (2 ^ 256) with
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      in Hqbound by (vm_compute; reflexivity).
    assert (Hqge : (q >=? 0) = true) by (apply Z.geb_le; lia).
    assert (Hqle :
      (q <=? 115792089237316195423570985008687907853269984665640564039457584007913129639935) = true)
      by (apply Z.leb_le; lia).
    unfold Z.zero, Z.one.
    rewrite ?Hqge, ?Hqle. cbn.
    replace
      115792089237316195423570985008687907853269984665640564039457584007913129639935
      with (Z.ones 256) by reflexivity.
    cbv beta iota zeta delta
      [MonadVM.Numeric.Make.to_z
       MonadVM.Numeric.Make.Impl.to_z].
    rewrite Hqr.
    cbv beta iota zeta delta
      [MonadVM.Numeric.Make.of_z_opt
       MonadVM.Numeric.Make.Impl.of_z_opt
       MonadVM.Numeric.Make.Impl.in_range].
    cbn -[Z.quotrem Z.land Z.shiftl].
    replace (Z.shiftl Z.one 256 - Z.one) with
      115792089237316195423570985008687907853269984665640564039457584007913129639935
      by (vm_compute; reflexivity).
    rewrite ?Hqge, ?Hqle.
    cbn -[Z.quotrem Z.land Z.shiftl].
    rewrite Z.land_ones by lia.
    replace (q >=? Z.zero) with true
      by (symmetry; unfold Z.zero; exact Hqge).
    cbn -[Z.quotrem Z.shiftl].
    unfold Z.zero, Z.one in *.
    rewrite Z.mod_small by (destruct (r =? 0); lia).
    destruct (r =? 0) eqn:Hrzero; cbn;
      rewrite Hq, Hr in *; rewrite Hrzero; cbn.
    - assert (Hword : (0 <=? size / 32 + 0) = true)
        by (apply Z.leb_le; lia).
      rewrite Hword. cbn.
      rewrite Z2N.id by lia. lia.
    - assert (Hword : (0 <=? size / 32 + 1) = true)
        by (apply Z.leb_le; lia).
      rewrite Hword. cbn.
      rewrite Z2N.id by lia. lia.
  Qed.

  Context `{Uint : RocqOfOCaml.Basics.Unreachable int}.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.

  Lemma nonfitting_extcodecopy_charge_exceeds_cap
      (size : MonadVM.Numeric.U256.t) :
    0 <= size < 2 ^ 256 ->
    MonadVM.Numeric.U256.to_int_opt size = None ->
    30_000_000 <
      Z.of_N (@MonadVM.Gas.op_star Ugas
        (@MonadVM.Numeric.U256.to_uint Uuint
          (@MonadVM.Numeric.U256.bytes_to_whole_words U256 size))
        (@MonadVM.Gas.copy_cost_per_word Ugas)).
  Proof.
    intros Hsize Hnone.
    pose proof (nonfitting_u256_large size (proj1 Hsize) Hnone)
      as Hlarge.
    pose proof (word_count_exact size Hsize) as Hwords.
    change (30_000_000 <
      Z.of_N ((@MonadVM.Numeric.U256.to_uint Uuint
        (@MonadVM.Numeric.U256.bytes_to_whole_words U256 size)) * 3)%N).
    rewrite N2Z.inj_mul.
    change (Z.of_N 3%N) with 3.
    rewrite Hwords.
    pose proof (large_size_copy_cost_exceeds_cap size Hlarge).
    destruct (size mod 32 =? 0); lia.
  Qed.

  Let total_copy_gas
      (size : MonadVM.Numeric.U256.t)
      (memory_extension_gas access_gas : MonadVM.Gas.t) :
      MonadVM.Gas.t :=
    @MonadVM.Gas.op_plus Ugas
      (@MonadVM.Gas.op_plus Ugas
        (@MonadVM.Gas.op_star Ugas
          (@MonadVM.Numeric.U256.to_uint Uuint
            (@MonadVM.Numeric.U256.bytes_to_whole_words U256 size))
          (@MonadVM.Gas.copy_cost_per_word Ugas))
        memory_extension_gas) access_gas.

  Lemma nonfitting_extcodecopy_total_exceeds_cap
      (size : MonadVM.Numeric.U256.t)
      (memory_extension_gas access_gas : MonadVM.Gas.t) :
    0 <= size < 2 ^ 256 ->
    @MonadVM.Numeric.U256.to_int_opt Uint size = None ->
    30_000_000 <
      Z.of_N (total_copy_gas size memory_extension_gas access_gas).
  Proof.
    intros Hsize Hnone.
    pose proof
      (nonfitting_extcodecopy_charge_exceeds_cap size Hsize Hnone)
      as Hcopy.
    unfold total_copy_gas.
    change (30_000_000 <
      Z.of_N
        ((@MonadVM.Gas.op_star Ugas
          (@MonadVM.Numeric.U256.to_uint Uuint
            (@MonadVM.Numeric.U256.bytes_to_whole_words U256 size))
          (@MonadVM.Gas.copy_cost_per_word Ugas)
          + memory_extension_gas + access_gas)%N)).
    rewrite !N2Z.inj_add.
    lia.
  Qed.

  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.

  Lemma nonfitting_extcodecopy_spend_fails
      (size : MonadVM.Numeric.U256.t)
      (memory_extension_gas access_gas : MonadVM.Gas.t)
      (state : @MonadVM.Vm.Make.MachineState.t Host_t F) :
    0 <= size < 2 ^ 256 ->
    @MonadVM.Numeric.U256.to_int_opt Uint size = None ->
    Z.of_N state.(MonadVM.Vm.Make.MachineState.t.gas) <= 30_000_000 ->
    @MonadVM.Vm.Make.spend Host_t F Ugas
      (total_copy_gas size memory_extension_gas access_gas) state =
      ((inr MonadVM.Evmc.Result.StatusCode.Out_of_gas :
        sum unit MonadVM.Evmc.Result.StatusCode.t), state).
  Proof.
    intros Hsize Hnone Hgas.
    pose proof
      (nonfitting_extcodecopy_total_exceeds_cap size
        memory_extension_gas access_gas Hsize Hnone) as Htotal.
    assert (Hlt :
      N.ltb state.(MonadVM.Vm.Make.MachineState.t.gas)
        (total_copy_gas size memory_extension_gas access_gas) = true).
    { apply N.ltb_lt. apply N2Z.inj_lt. lia. }
    unfold MonadVM.Vm.Make.spend.
    unfold MonadVM.Gas.op_lt, MonadVM.Support.UintN.op_lt.
    rewrite Hlt.
    reflexivity.
  Qed.

  Lemma extcodecopy_successful_spend_size_fits
      (size : MonadVM.Numeric.U256.t)
      (memory_extension_gas access_gas : MonadVM.Gas.t)
      (state next : @MonadVM.Vm.Make.MachineState.t Host_t F) :
    0 <= size < 2 ^ 256 ->
    Z.of_N state.(MonadVM.Vm.Make.MachineState.t.gas) <= 30_000_000 ->
    @MonadVM.Vm.Make.spend Host_t F Ugas
      (total_copy_gas size memory_extension_gas access_gas) state =
      ((inl tt : sum unit MonadVM.Evmc.Result.StatusCode.t), next) ->
    exists native_size,
      @MonadVM.Numeric.U256.to_int_opt Uint size = Some native_size.
  Proof.
    intros Hsize Hgas Hspent.
    destruct (@MonadVM.Numeric.U256.to_int_opt Uint size)
      as [native_size|] eqn:Hfit.
    - now exists native_size.
    - rewrite (nonfitting_extcodecopy_spend_fails size
        memory_extension_gas access_gas state Hsize Hfit Hgas)
        in Hspent.
      discriminate.
  Qed.
End GeneratedWordCount.

Section StackWordRange.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.

  Let State := @MonadVM.Vm.Make.MachineState.t Host_t F.

  Definition valid_stack_words (state : State) : Prop :=
    Forall (fun word : MonadVM.Numeric.U256.t =>
      (0 <= word < 2 ^ 256)%Z)
      state.(MonadVM.Vm.Make.MachineState.t.stack).

  Lemma initial_has_valid_stack_words
      `{Uuint :
        RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}
      `{U256 :
        RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}
      `{Uinteger :
        RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.Integer.t}
      `{Uunit : RocqOfOCaml.Basics.Unreachable unit}
      (host : Host_t) (gas memory_capacity : MonadVM.Support.UintN.t) :
    valid_stack_words
      (@MonadVM.Vm.Make.MachineState.initial Host_t F
        Uuint U256 Uinteger Uunit host gas memory_capacity).
  Proof.
    unfold valid_stack_words, MonadVM.Vm.Make.MachineState.initial.
    simpl. constructor.
  Qed.

  Lemma pop_preserves_valid_stack_words
      (state next : State) (value : MonadVM.Numeric.U256.t) :
    valid_stack_words state ->
    @MonadVM.Vm.Make.pop Host_t F state =
      ((inl value : sum MonadVM.Numeric.U256.t
        MonadVM.Evmc.Result.StatusCode.t), next) ->
    valid_stack_words next.
  Proof.
    intros Hstack Hpop.
    unfold valid_stack_words in *.
    unfold MonadVM.Vm.Make.pop in Hpop.
    destruct state.(MonadVM.Vm.Make.MachineState.t.stack)
      as [|head tail]; try discriminate.
    inversion Hpop; subst next.
    cbn [MonadVM.Vm.Make.MachineState.t.stack
      MonadVM.Vm.Make.MachineState.t.with_stack
      MonadVM.Vm.Make.MachineState.t.with_stack_depth].
    now apply Forall_inv_tail in Hstack.
  Qed.

  Lemma pop_returns_valid_word
      (state next : State) (value : MonadVM.Numeric.U256.t) :
    valid_stack_words state ->
    @MonadVM.Vm.Make.pop Host_t F state =
      ((inl value : sum MonadVM.Numeric.U256.t
        MonadVM.Evmc.Result.StatusCode.t), next) ->
    (0 <= value < 2 ^ 256)%Z.
  Proof.
    intros Hstack Hpop.
    unfold valid_stack_words in Hstack.
    unfold MonadVM.Vm.Make.pop in Hpop.
    destruct state.(MonadVM.Vm.Make.MachineState.t.stack)
      as [|head tail]; try discriminate.
    inversion Hpop; subst value.
    now apply Forall_inv in Hstack.
  Qed.

  Lemma push_preserves_valid_stack_words
      (state next : State) (value : MonadVM.Numeric.U256.t) :
    valid_stack_words state ->
    (0 <= value < 2 ^ 256)%Z ->
    @MonadVM.Vm.Make.push Host_t F value state =
      ((inl tt : sum unit MonadVM.Evmc.Result.StatusCode.t), next) ->
    valid_stack_words next.
  Proof.
    intros Hstack Hvalue Hpush.
    unfold valid_stack_words in *.
    unfold MonadVM.Vm.Make.push in Hpush.
    destruct (Z.geb
      state.(MonadVM.Vm.Make.MachineState.t.stack_depth)
      (@MonadVM.Vm.Make.max_stack_depth Host_t F));
      try discriminate.
    inversion Hpush; subst next.
    cbn [MonadVM.Vm.Make.MachineState.t.stack
      MonadVM.Vm.Make.MachineState.t.with_stack
      MonadVM.Vm.Make.MachineState.t.with_stack_depth].
    now constructor.
  Qed.

  (** [SWAP] replaces one stack word with a word already popped from the
      stack.  This lemma isolates the generated list replacement so its
      range argument can be reused when proving the opcode invariant. *)
  Lemma replace_list_preserves_valid_words
      {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}
      (i : int) (replacement displaced : MonadVM.Numeric.U256.t)
      (stack stack' : list MonadVM.Numeric.U256.t) :
    (0 <= replacement < 2 ^ 256)%Z ->
    Forall (fun word : MonadVM.Numeric.U256.t =>
      (0 <= word < 2 ^ 256)%Z) stack ->
    @MonadVM.Vm.Make.Executor.replace_list Host_t F E
      MonadVM.Numeric.U256.t i replacement stack =
      Some (displaced, stack') ->
    (0 <= displaced < 2 ^ 256)%Z /\
    Forall (fun word : MonadVM.Numeric.U256.t =>
      (0 <= word < 2 ^ 256)%Z) stack'.
  Proof.
    revert i displaced stack'.
    induction stack as [|head tail IH];
      intros i displaced stack' Hreplacement Hstack Hreplace.
    - destruct i; cbn in Hreplace; discriminate.
    - cbn in Hreplace.
      inversion Hstack as [|? ? Hhead Htail]; subst.
      destruct i as [|positive|negative]; cbn -[Z.sub] in Hreplace.
      + inversion Hreplace; subst. split; [exact Hhead|].
        now constructor.
      + destruct (@MonadVM.Vm.Make.Executor.replace_list Host_t F E
          MonadVM.Numeric.U256.t (Z.pos positive - 1) replacement tail)
        as [[old rest]|] eqn:Htail_replace; try discriminate.
        inversion Hreplace; subst.
        specialize (IH _ _ _ Hreplacement Htail Htail_replace)
          as [Hold Hrest].
        split; [exact Hold|]. now constructor.
      + destruct (@MonadVM.Vm.Make.Executor.replace_list Host_t F E
          MonadVM.Numeric.U256.t (Z.neg negative - 1) replacement tail)
        as [[old rest]|] eqn:Htail_replace; try discriminate.
        inversion Hreplace; subst.
        specialize (IH _ _ _ Hreplacement Htail Htail_replace)
          as [Hold Hrest].
        split; [exact Hold|]. now constructor.
  Qed.

  Definition swap_lookup_action
      {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}
      (index : int) (first : MonadVM.Numeric.U256.t) :
      @MonadVM.Vm.Make.M.t Host_t F
        (MonadVM.Numeric.U256.t * list MonadVM.Numeric.U256.t) :=
    MonadVM.Vm.Make.M.op_gtgteq
      (MonadVM.Vm.Make.M.fmap
        (MonadVM.Vm.Make.Executor.replace_list index first)
        (MonadVM.Vm.Make.M.op_exclamation
          MonadVM.Vm.Make.MachineState.stack))
      (MonadVM.Vm.Make.M.Option.or_fail
        MonadVM.Evmc.Result.StatusCode.Stack_underflow).

  Lemma swap_lookup_action_preserves_valid_words
      {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}
      (index : int) (first displaced : MonadVM.Numeric.U256.t)
      (stack' : list MonadVM.Numeric.U256.t)
      (state next : State) :
    valid_stack_words state ->
    (0 <= first < 2 ^ 256)%Z ->
    @swap_lookup_action E index first state =
      ((inl (displaced, stack') :
        sum (MonadVM.Numeric.U256.t * list MonadVM.Numeric.U256.t)
          MonadVM.Evmc.Result.StatusCode.t), next) ->
    (0 <= displaced < 2 ^ 256)%Z /\
    Forall (fun word : MonadVM.Numeric.U256.t =>
      (0 <= word < 2 ^ 256)%Z) stack' /\
    next = state.
  Proof.
    intros Hstack Hfirst Hlookup.
    unfold swap_lookup_action in Hlookup.
    cbn in Hlookup.
    destruct (@MonadVM.Vm.Make.Executor.replace_list Host_t F E
      MonadVM.Numeric.U256.t index first
      state.(MonadVM.Vm.Make.MachineState.t.stack))
      as [[found rest]|] eqn:Hreplace.
    all: cbn in Hlookup.
    - pose proof (replace_list_preserves_valid_words
        index first found
        state.(MonadVM.Vm.Make.MachineState.t.stack) rest
        Hfirst Hstack Hreplace) as [Hfound Hrest].
      inversion Hlookup; subst.
      split; [exact Hfound|].
      split; [exact Hrest|reflexivity].
    - discriminate.
  Qed.

  Lemma assign_valid_stack_words
      (stack' : list MonadVM.Numeric.U256.t)
      (state next : State) :
    Forall (fun word : MonadVM.Numeric.U256.t =>
      (0 <= word < 2 ^ 256)%Z) stack' ->
    MonadVM.Vm.Make.M.op_coloneq
      MonadVM.Vm.Make.MachineState.stack stack' state =
      ((inl tt : sum unit MonadVM.Evmc.Result.StatusCode.t), next) ->
    valid_stack_words next.
  Proof.
    intros Hwords Hassign.
    unfold MonadVM.Vm.Make.M.op_coloneq in Hassign.
    cbn in Hassign.
    inversion Hassign; subst next.
    unfold valid_stack_words.
    cbn. exact Hwords.
  Qed.

  (** [DUP] obtains its new word from a nonnegative stack index. *)
  Lemma nth_opt_returns_valid_word
      `{Uoption : RocqOfOCaml.Basics.Unreachable
        (option MonadVM.Numeric.U256.t)}
      (index : int) (stack : list MonadVM.Numeric.U256.t)
      (word : MonadVM.Numeric.U256.t) :
    (0 <= index)%Z ->
    Forall (fun value : MonadVM.Numeric.U256.t =>
      (0 <= value < 2 ^ 256)%Z) stack ->
    @MonadVM.Vm.Make.M.List.nth_opt Host_t F
      MonadVM.Numeric.U256.t Uoption stack index = Some word ->
    (0 <= word < 2 ^ 256)%Z.
  Proof.
    revert index word.
    induction stack as [|head tail IH];
      intros index word Hindex Hstack Hlookup.
    - change (@RocqOfOCaml.OCamlList.nth_opt
        MonadVM.Numeric.U256.t Uoption Datatypes.nil index = Some word)
        in Hlookup.
      unfold RocqOfOCaml.OCamlList.nth_opt in Hlookup.
      cbn in Hlookup.
      assert (Hnegative : (index <? 0) = false)
        by (apply Z.ltb_ge; lia).
      now rewrite Hnegative in Hlookup.
    - inversion Hstack as [|? ? Hhead Htail]; subst.
      change (@RocqOfOCaml.OCamlList.nth_opt
        MonadVM.Numeric.U256.t Uoption (head :: tail) index = Some word)
        in Hlookup.
      unfold RocqOfOCaml.OCamlList.nth_opt in Hlookup.
      cbn in Hlookup.
      assert (Hnegative : (index <? 0) = false)
        by (apply Z.ltb_ge; lia).
      rewrite Hnegative in Hlookup.
      destruct (equiv_decb index 0) eqn:Hzero.
      + inversion Hlookup; subst. exact Hhead.
      + assert (Hnonzero : index <> 0%Z).
        { intro Heq. subst index. cbn in Hzero. discriminate. }
        assert (Hnext_negative : (index - 1 <? 0) = false)
          by (apply Z.ltb_ge; lia).
        assert (Htail_lookup :
          @MonadVM.Vm.Make.M.List.nth_opt Host_t F
            MonadVM.Numeric.U256.t Uoption tail (index - 1) =
            Some word).
        { change (@RocqOfOCaml.OCamlList.nth_opt
            MonadVM.Numeric.U256.t Uoption tail (index - 1) =
            Some word).
          unfold RocqOfOCaml.OCamlList.nth_opt.
          rewrite Hnext_negative.
          exact Hlookup. }
        apply (IH (index - 1) word); [lia | exact Htail | exact Htail_lookup].
  Qed.

  Definition dup_lookup_action
      `{Uoption : RocqOfOCaml.Basics.Unreachable
        (option MonadVM.Numeric.U256.t)}
      (index : int) :
      @MonadVM.Vm.Make.M.t Host_t F MonadVM.Numeric.U256.t :=
    MonadVM.Vm.Make.M.op_gtgteq
      (MonadVM.Vm.Make.M.fmap
        (fun stack => MonadVM.Vm.Make.M.List.nth_opt stack index)
        (MonadVM.Vm.Make.M.op_exclamation
          MonadVM.Vm.Make.MachineState.stack))
      (MonadVM.Vm.Make.M.Option.or_fail
        MonadVM.Evmc.Result.StatusCode.Stack_underflow).

  Lemma dup_lookup_action_preserves_valid_words
      `{Uoption : RocqOfOCaml.Basics.Unreachable
        (option MonadVM.Numeric.U256.t)}
      (index : int) (state next : State)
      (word : MonadVM.Numeric.U256.t) :
    (0 <= index)%Z ->
    valid_stack_words state ->
    dup_lookup_action index state =
      ((inl word : sum MonadVM.Numeric.U256.t
        MonadVM.Evmc.Result.StatusCode.t), next) ->
    (0 <= word < 2 ^ 256)%Z /\
    next = state.
  Proof.
    intros Hindex Hstack Hlookup.
    unfold dup_lookup_action in Hlookup.
    cbn in Hlookup.
    destruct (MonadVM.Vm.Make.M.List.nth_opt
      state.(MonadVM.Vm.Make.MachineState.t.stack) index)
      as [found|] eqn:Hfound.
    all: cbn in Hlookup.
    - inversion Hlookup; subst.
      split.
      + eapply nth_opt_returns_valid_word; eauto.
      + reflexivity.
    - discriminate.
  Qed.

  Lemma spend_preserves_valid_stack_words
      `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}
      (amount : MonadVM.Gas.t) (state next : State) :
    valid_stack_words state ->
    @MonadVM.Vm.Make.spend Host_t F Ugas amount state =
      ((inl tt : sum unit MonadVM.Evmc.Result.StatusCode.t), next) ->
    valid_stack_words next.
  Proof.
    intros Hstack Hspend.
    unfold MonadVM.Vm.Make.spend in Hspend.
    destruct (MonadVM.Gas.op_lt
      state.(MonadVM.Vm.Make.MachineState.t.gas) amount);
      try discriminate.
    inversion Hspend; subst next.
    unfold valid_stack_words in *.
    cbn. exact Hstack.
  Qed.

  Lemma increase_pc_preserves_valid_stack_words
      `{U256 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}
      (state next : State) (continued : bool) :
    valid_stack_words state ->
    @MonadVM.Vm.Make.increase_pc_and_continue Host_t F U256 state =
      ((inl continued : sum bool MonadVM.Evmc.Result.StatusCode.t),
        next) ->
    valid_stack_words next.
  Proof.
    intros Hstack Hcontinue.
    unfold MonadVM.Vm.Make.increase_pc_and_continue,
      MonadVM.Vm.Make.update_pc_and_continue in Hcontinue.
    inversion Hcontinue; subst next.
    unfold valid_stack_words in *.
    cbn. exact Hstack.
  Qed.

  Lemma update_pc_preserves_valid_stack_words
      (update : MonadVM.Numeric.U256.t -> MonadVM.Numeric.U256.t)
      (state next : State) (continued : bool) :
    valid_stack_words state ->
    @MonadVM.Vm.Make.update_pc_and_continue Host_t F update state =
      ((inl continued : sum bool MonadVM.Evmc.Result.StatusCode.t),
        next) ->
    valid_stack_words next.
  Proof.
    intros Hstack Hcontinue.
    unfold MonadVM.Vm.Make.update_pc_and_continue in Hcontinue.
    inversion Hcontinue; subst next.
    unfold valid_stack_words in *.
    cbn. exact Hstack.
  Qed.

  Definition push_pc_read_action
      `{Uint : RocqOfOCaml.Basics.Unreachable int} :
      @MonadVM.Vm.Make.M.t Host_t F int :=
    MonadVM.Vm.Make.M.op_ltdollargt
      (MonadVM.Numeric.U256.to_int (_rocq_assumption_0 := Uint))
      (MonadVM.Vm.Make.M.op_exclamation
        MonadVM.Vm.Make.MachineState.pc).

  Lemma push_pc_read_preserves_state
      `{Uint : RocqOfOCaml.Basics.Unreachable int}
      (state next : State) (here : int) :
    push_pc_read_action state =
      ((inl here : sum int MonadVM.Evmc.Result.StatusCode.t), next) ->
    next = state.
  Proof.
    intro Hread.
    unfold push_pc_read_action in Hread.
    cbn in Hread.
    now inversion Hread.
  Qed.

  Lemma dup_preserves_valid_stack_words
      {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}
      `{U256 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}
      `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}
      `{Uoption_m : RocqOfOCaml.Basics.Unreachable
        (@MonadVM.Vm.Make.M.Option.t Host_t F MonadVM.Numeric.U256.t)}
      `{Uunit : RocqOfOCaml.Basics.Unreachable unit}
      `{Uoption : RocqOfOCaml.Basics.Unreachable
        (option MonadVM.Numeric.U256.t)}
      (i : int) (state next : State) (continued : bool) :
    (1 <= i <= 16)%Z ->
    valid_stack_words state ->
    @MonadVM.Vm.Make.Executor.dup Host_t F E
      U256 Ugas Uoption_m Uunit Uoption i state =
      ((inl continued : sum bool MonadVM.Evmc.Result.StatusCode.t),
        next) ->
    valid_stack_words next.
  Proof.
    intros Hi Hstack Hdup.
    unfold MonadVM.Vm.Make.Executor.dup in Hdup.
    cbn beta iota zeta in Hdup.
    change
      (MonadVM.Vm.Make.M.op_letdollar
        (@dup_lookup_action Uoption_m (i - 1))
        (fun word => MonadVM.Vm.Make.M.op_letdollar
          (MonadVM.Vm.Make.spend MonadVM.Gas.very_low)
          (fun _ => MonadVM.Vm.Make.M.op_letdollar
            (MonadVM.Vm.Make.push word)
            (fun _ => MonadVM.Vm.Make.increase_pc_and_continue)))
        state = (inl continued, next)) in Hdup.
    destruct (bind_success_decompose _ _ _ _ _ Hdup)
      as [after_lookup [word [Hlookup Hrest]]].
    pose proof
      (@dup_lookup_action_preserves_valid_words Uoption_m (i - 1)
        state after_lookup word ltac:(lia) Hstack Hlookup)
      as [Hword Hsame].
    subst after_lookup.
    destruct (bind_success_decompose _ _ _ _ _ Hrest)
      as [after_spend [spent_unit [Hspend Hafter_spend]]].
    destruct spent_unit.
    pose proof (spend_preserves_valid_stack_words
      MonadVM.Gas.very_low state after_spend Hstack Hspend)
      as Hstack_spent.
    destruct (bind_success_decompose _ _ _ _ _ Hafter_spend)
      as [after_push [pushed_unit [Hpush Hcontinue]]].
    destruct pushed_unit.
    pose proof (push_preserves_valid_stack_words
      after_spend after_push word Hstack_spent Hword Hpush)
      as Hstack_pushed.
    eapply increase_pc_preserves_valid_stack_words; eauto.
  Qed.

  Lemma swap_preserves_valid_stack_words
      {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}
      `{U256 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}
      `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}
      `{Uunit : RocqOfOCaml.Basics.Unreachable unit}
      (i : int) (state next : State) (continued : bool) :
    (1 <= i <= 16)%Z ->
    valid_stack_words state ->
    @MonadVM.Vm.Make.Executor.swap Host_t F E
      U256 Ugas Uunit i state =
      ((inl continued : sum bool MonadVM.Evmc.Result.StatusCode.t),
        next) ->
    valid_stack_words next.
  Proof.
    intros Hi Hstack Hswap.
    unfold MonadVM.Vm.Make.Executor.swap in Hswap.
    cbn beta iota zeta in Hswap.
    change
      (MonadVM.Vm.Make.M.op_letdollar MonadVM.Vm.Make.pop
        (fun first => MonadVM.Vm.Make.M.op_letdollar
          (@swap_lookup_action E (i - 1) first)
          (fun pair => let '(displaced, stack') := pair in
            MonadVM.Vm.Make.M.op_letdollar
              (MonadVM.Vm.Make.M.op_coloneq
                MonadVM.Vm.Make.MachineState.stack stack')
              (fun _ => MonadVM.Vm.Make.M.op_letdollar
                (MonadVM.Vm.Make.spend MonadVM.Gas.very_low)
                (fun _ => MonadVM.Vm.Make.M.op_letdollar
                  (MonadVM.Vm.Make.push displaced)
                  (fun _ => MonadVM.Vm.Make.increase_pc_and_continue)))))
        state = (inl continued, next)) in Hswap.
    destruct (bind_success_decompose _ _ _ _ _ Hswap)
      as [after_pop [first [Hpop Hrest]]].
    pose proof (pop_returns_valid_word state after_pop first Hstack Hpop)
      as Hfirst.
    pose proof (pop_preserves_valid_stack_words
      state after_pop first Hstack Hpop) as Hstack_pop.
    destruct (bind_success_decompose _ _ _ _ _ Hrest)
      as [after_lookup [[displaced stack'] [Hlookup Hafter_lookup]]].
    pose proof (@swap_lookup_action_preserves_valid_words E
      (i - 1) first displaced stack' after_pop after_lookup
      Hstack_pop Hfirst Hlookup) as [Hdisplaced [Hstack' Hsame]].
    subst after_lookup.
    destruct (bind_success_decompose _ _ _ _ _ Hafter_lookup)
      as [after_assign [assigned_unit [Hassign Hafter_assign]]].
    destruct assigned_unit.
    pose proof (assign_valid_stack_words
      stack' after_pop after_assign Hstack' Hassign) as Hstack_assign.
    destruct (bind_success_decompose _ _ _ _ _ Hafter_assign)
      as [after_spend [spent_unit [Hspend Hafter_spend]]].
    destruct spent_unit.
    pose proof (spend_preserves_valid_stack_words
      MonadVM.Gas.very_low after_assign after_spend
      Hstack_assign Hspend) as Hstack_spent.
    destruct (bind_success_decompose _ _ _ _ _ Hafter_spend)
      as [after_push [pushed_unit [Hpush Hcontinue]]].
    destruct pushed_unit.
    pose proof (push_preserves_valid_stack_words
      after_spend after_push displaced Hstack_spent Hdisplaced Hpush)
      as Hstack_pushed.
    eapply increase_pc_preserves_valid_stack_words; eauto.
  Qed.

  Lemma pop_opcode_preserves_valid_stack_words
      {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}
      `{U256 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}
      `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}
      (state next : State) (continued : bool) :
    valid_stack_words state ->
    @MonadVM.Vm.Make.Executor.pop_ Host_t F E
      U256 Ugas state =
      ((inl continued : sum bool MonadVM.Evmc.Result.StatusCode.t),
        next) ->
    valid_stack_words next.
  Proof.
    intros Hstack Hpop_opcode.
    unfold MonadVM.Vm.Make.Executor.pop_ in Hpop_opcode.
    change
      (MonadVM.Vm.Make.M.op_letdollar MonadVM.Vm.Make.pop
        (fun _ => MonadVM.Vm.Make.M.op_letdollar
          (MonadVM.Vm.Make.spend MonadVM.Gas.base)
          (fun _ => MonadVM.Vm.Make.increase_pc_and_continue))
        state = (inl continued, next)) in Hpop_opcode.
    destruct (bind_success_decompose _ _ _ _ _ Hpop_opcode)
      as [after_pop [word [Hpop Hrest]]].
    pose proof (pop_preserves_valid_stack_words
      state after_pop word Hstack Hpop) as Hstack_pop.
    destruct (bind_success_decompose _ _ _ _ _ Hrest)
      as [after_spend [spent_unit [Hspend Hcontinue]]].
    destruct spent_unit.
    pose proof (spend_preserves_valid_stack_words
      MonadVM.Gas.base after_pop after_spend
      Hstack_pop Hspend) as Hstack_spent.
    eapply increase_pc_preserves_valid_stack_words; eauto.
  Qed.

  Lemma push_opcode_preserves_valid_stack_words
      {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}
      `{Uuint : RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}
      `{U256 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}
      `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}
      `{Ubytes : RocqOfOCaml.Basics.Unreachable
        MonadVM.Byte_string.Bytes.t}
      `{Uunit : RocqOfOCaml.Basics.Unreachable unit}
      `{Uint : RocqOfOCaml.Basics.Unreachable int}
      `{Uascii : RocqOfOCaml.Basics.Unreachable ascii}
      (i : int) (state next : State) (continued : bool) :
    (0 <= i <= 32)%Z ->
    valid_stack_words state ->
    @MonadVM.Vm.Make.Executor.push_ Host_t F E
      Uuint U256 Ugas Ubytes Uunit Uint Uascii i state =
      ((inl continued : sum bool MonadVM.Evmc.Result.StatusCode.t),
        next) ->
    valid_stack_words next.
  Proof.
    intros Hi Hstack Hpush_opcode.
    unfold MonadVM.Vm.Make.Executor.push_ in Hpush_opcode.
    cbn beta iota zeta in Hpush_opcode.
    destruct (bind_success_decompose _ _ _ _ _ Hpush_opcode)
      as [after_spend [spent_unit [Hspend Hrest]]].
    destruct spent_unit.
    pose proof (spend_preserves_valid_stack_words
      (if equiv_decb i 0 then MonadVM.Gas.base
       else MonadVM.Gas.very_low)
      state after_spend Hstack Hspend) as Hstack_spent.
    cbn beta iota zeta in Hrest.
    destruct (bind_success_decompose _ _ _ _ _ Hrest)
      as [after_read [here [Hread Hafter_read]]].
    assert (Hread_state : after_read = after_spend).
    { eapply push_pc_read_preserves_state.
      exact Hread. }
    subst after_read.
    cbn beta iota zeta in Hafter_read.
    destruct (bind_success_decompose _ _ _ _ _ Hafter_read)
      as [after_push [pushed_unit [Hpush Hcontinue]]].
    destruct pushed_unit.
    pose proof (@push_immediate_in_range Ubytes Uascii Uuint U256
      (MonadVM.Vm.Make.Executor.C.(MonadVM.Vm.Make.Executor_C_signature.execution_environment)
        .(MonadVM.Vm.Make.ExecutionEnvironment.t.bytecode))
      here i Hi) as Hword.
    cbn zeta in Hword.
    assert (Hstack_pushed : valid_stack_words after_push).
    { eapply push_preserves_valid_stack_words;
        [exact Hstack_spent | exact Hword | exact Hpush]. }
    eapply update_pc_preserves_valid_stack_words; eauto.
  Qed.

  Lemma fetch_environment_word_preserves_valid_stack_words
      {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}
      `{U256 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}
      `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}
      (value : MonadVM.Numeric.U256.t)
      (state next : State) (continued : bool) :
    (0 <= value < 2 ^ 256)%Z ->
    valid_stack_words state ->
    @MonadVM.Vm.Make.Executor.fetch_environment_variable_opcode_impl
      Host_t F E U256 Ugas value state =
      ((inl continued : sum bool MonadVM.Evmc.Result.StatusCode.t),
        next) ->
    valid_stack_words next.
  Proof.
    intros Hvalue Hstack Hfetch.
    unfold MonadVM.Vm.Make.Executor.fetch_environment_variable_opcode_impl
      in Hfetch.
    destruct (bind_success_decompose _ _ _ _ _ Hfetch)
      as [after_spend [spent_unit [Hspend Hrest]]].
    destruct spent_unit.
    pose proof (spend_preserves_valid_stack_words
      MonadVM.Gas.base state after_spend Hstack Hspend)
      as Hstack_spent.
    cbn beta iota zeta in Hrest.
    destruct (bind_success_decompose _ _ _ _ _ Hrest)
      as [after_push [pushed_unit [Hpush Hcontinue]]].
    destruct pushed_unit.
    pose proof (push_preserves_valid_stack_words
      after_spend after_push value Hstack_spent Hvalue Hpush)
      as Hstack_pushed.
    eapply increase_pc_preserves_valid_stack_words; eauto.
  Qed.

  Lemma callvalue_preserves_valid_stack_words
      {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}
      `{U256 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}
      `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}
      (state next : State) (continued : bool) :
    let value := (@MonadVM.Vm.Make.Executor.C Host_t F E).(
      MonadVM.Vm.Make.Executor_C_signature.execution_environment).(
      MonadVM.Vm.Make.ExecutionEnvironment.t.value) in
    (0 <= value < 2 ^ 256)%Z ->
    valid_stack_words state ->
    @MonadVM.Vm.Make.Executor.callvalue Host_t F E U256 Ugas state =
      ((inl continued : sum bool MonadVM.Evmc.Result.StatusCode.t),
        next) ->
    valid_stack_words next.
  Proof.
    cbn zeta.
    intros Hvalue Hstack Hcallvalue.
    unfold MonadVM.Vm.Make.Executor.callvalue in Hcallvalue.
    eapply fetch_environment_word_preserves_valid_stack_words; eauto.
  Qed.

  Lemma fetch_environment_action_preserves_valid_stack_words
      {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}
      `{U256 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}
      `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}
      (value_action : @MonadVM.Vm.Make.M.t Host_t F
        MonadVM.Numeric.U256.t)
      (state next : State) (continued : bool) :
    (forall before after value,
      valid_stack_words before ->
      value_action before =
        ((inl value : sum MonadVM.Numeric.U256.t
          MonadVM.Evmc.Result.StatusCode.t), after) ->
      valid_stack_words after /\ (0 <= value < 2 ^ 256)%Z) ->
    valid_stack_words state ->
    @MonadVM.Vm.Make.Executor.fetch_environment_variable_opcode_impl'
      Host_t F E U256 Ugas value_action state =
      ((inl continued : sum bool MonadVM.Evmc.Result.StatusCode.t),
        next) ->
    valid_stack_words next.
  Proof.
    intros Hvalue Hstack Hfetch.
    unfold MonadVM.Vm.Make.Executor.fetch_environment_variable_opcode_impl'
      in Hfetch.
    destruct (bind_success_decompose _ _ _ _ _ Hfetch)
      as [after_spend [spent_unit [Hspend Hrest]]].
    destruct spent_unit.
    pose proof (spend_preserves_valid_stack_words
      MonadVM.Gas.base state after_spend Hstack Hspend)
      as Hstack_spent.
    cbn beta iota zeta in Hrest.
    destruct (bind_success_decompose _ _ _ _ _ Hrest)
      as [after_value [value [Haction Hafter_value]]].
    pose proof (Hvalue after_spend after_value value
      Hstack_spent Haction) as [Hstack_value Hword].
    destruct (bind_success_decompose _ _ _ _ _ Hafter_value)
      as [after_push [pushed_unit [Hpush Hcontinue]]].
    destruct pushed_unit.
    pose proof (push_preserves_valid_stack_words
      after_value after_push value Hstack_value Hword Hpush)
      as Hstack_pushed.
    eapply increase_pc_preserves_valid_stack_words; eauto.
  Qed.

  Let host_get_balance :=
    (@MonadVM.Vm.Make.Host Host_t F).(MonadVM.Evmc.HOST.get_balance).

  Definition host_balance_words_bounded : Prop :=
    forall (address : MonadVM.Vm.Make.Address.t) (host : Host_t),
      let '(balance, _) := host_get_balance address host in
      (0 <= balance < 2 ^ 256)%Z.

  Lemma host_api_get_balance_preserves_valid_words
      (Hhost : host_balance_words_bounded)
      (address : MonadVM.Vm.Make.Address.t)
      (state next : State) (balance : MonadVM.Numeric.U256.t) :
    valid_stack_words state ->
    @MonadVM.Vm.Make.M.HostAPI.get_balance Host_t F address state =
      ((inl balance : sum MonadVM.Numeric.U256.t
        MonadVM.Evmc.Result.StatusCode.t), next) ->
    valid_stack_words next /\ (0 <= balance < 2 ^ 256)%Z.
  Proof.
    intros Hstack Hcall.
    change (@MonadVM.Vm.Make.M.HostAPI.lift Host_t F
      MonadVM.Numeric.U256.t (host_get_balance address) state =
      (inl balance, next)) in Hcall.
    unfold MonadVM.Vm.Make.M.HostAPI.lift in Hcall.
    destruct (host_get_balance address
      state.(MonadVM.Vm.Make.MachineState.t.host))
      as [actual host'] eqn:Hbase.
    inversion Hcall; subst.
    split.
    - unfold valid_stack_words in *.
      cbn. exact Hstack.
    - specialize (Hhost address
        state.(MonadVM.Vm.Make.MachineState.t.host)).
      rewrite Hbase in Hhost.
      exact Hhost.
  Qed.

  Lemma host_lift_preserves_valid_stack_words
      {A : Set} (action : Host_t -> A * Host_t)
      (state next : State) (result : A) :
    valid_stack_words state ->
    @MonadVM.Vm.Make.M.HostAPI.lift Host_t F A action state =
      ((inl result : sum A MonadVM.Evmc.Result.StatusCode.t), next) ->
    valid_stack_words next.
  Proof.
    intros Hstack Hlift.
    unfold MonadVM.Vm.Make.M.HostAPI.lift in Hlift.
    destruct (action state.(MonadVM.Vm.Make.MachineState.t.host))
      as [actual host'].
    inversion Hlift; subst next.
    unfold valid_stack_words in *.
    cbn. exact Hstack.
  Qed.

  Lemma host_api_access_account_preserves_valid_stack_words
      (address : MonadVM.Vm.Make.Address.t)
      (state next : State)
      (access : MonadVM.Support.Variants.AccessStatus.t) :
    valid_stack_words state ->
    @MonadVM.Vm.Make.M.HostAPI.access_account Host_t F address state =
      ((inl access : sum MonadVM.Support.Variants.AccessStatus.t
        MonadVM.Evmc.Result.StatusCode.t), next) ->
    valid_stack_words next.
  Proof.
    intros Hstack Haccess.
    change (@MonadVM.Vm.Make.M.HostAPI.lift Host_t F
      MonadVM.Support.Variants.AccessStatus.t
      ((@MonadVM.Vm.Make.Host Host_t F).(
        MonadVM.Evmc.HOST.access_account) address) state =
      (inl access, next)) in Haccess.
    eapply host_lift_preserves_valid_stack_words; eauto.
  Qed.

  Lemma map_pop_preserves_valid_stack_words
      {A : Set} (convert : MonadVM.Numeric.U256.t -> A)
      (state next : State) (result : A) :
    valid_stack_words state ->
    @MonadVM.Vm.Make.M.op_ltdollargt Host_t F
      MonadVM.Numeric.U256.t A convert
      (@MonadVM.Vm.Make.pop Host_t F) state =
      ((inl result : sum A MonadVM.Evmc.Result.StatusCode.t), next) ->
    valid_stack_words next.
  Proof.
    intros Hstack Hmap.
    unfold MonadVM.Vm.Make.M.op_ltdollargt in Hmap.
    cbn in Hmap.
    destruct (@MonadVM.Vm.Make.pop Host_t F state)
      as [[word|error] middle] eqn:Hpop; cbn in Hmap;
      try discriminate.
    inversion Hmap; subst next.
    eapply pop_preserves_valid_stack_words; eauto.
  Qed.

  Lemma map_action_preserves_valid_stack_words
      {A B : Set} (convert : A -> B)
      (action : @MonadVM.Vm.Make.M.t Host_t F A)
      (state next : State) (result : B) :
    (forall before after value,
      valid_stack_words before ->
      action before =
        ((inl value : sum A MonadVM.Evmc.Result.StatusCode.t), after) ->
      valid_stack_words after) ->
    valid_stack_words state ->
    @MonadVM.Vm.Make.M.op_ltdollargt Host_t F A B
      convert action state =
      ((inl result : sum B MonadVM.Evmc.Result.StatusCode.t), next) ->
    valid_stack_words next.
  Proof.
    intros Haction Hstack Hmap.
    unfold MonadVM.Vm.Make.M.op_ltdollargt in Hmap.
    cbn in Hmap.
    destruct (action state) as [[value|error] middle] eqn:Hleft;
      cbn in Hmap; try discriminate.
    inversion Hmap; subst next.
    eapply Haction; eauto.
  Qed.

  Lemma balance_preserves_valid_stack_words
      {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}
      `{Urepr : RocqOfOCaml.Basics.Unreachable
        MonadVM.Numeric.U256.Repr.t}
      `{U256 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}
      `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}
      `{Uaddress : RocqOfOCaml.Basics.Unreachable
        MonadVM.Chain.Ethereum.Address.t}
      `{Uunit : RocqOfOCaml.Basics.Unreachable unit}
      `{Uint : RocqOfOCaml.Basics.Unreachable int}
      `{Uascii : RocqOfOCaml.Basics.Unreachable ascii}
      `{UintPair : RocqOfOCaml.Basics.Unreachable (int * int)}
      (Hhost : host_balance_words_bounded)
      (state next : State) (continued : bool) :
    valid_stack_words state ->
    @MonadVM.Vm.Make.Executor.balance Host_t F E
      Urepr U256 Ugas Uaddress Uunit Uint Uascii UintPair state =
      ((inl continued : sum bool MonadVM.Evmc.Result.StatusCode.t),
        next) ->
    valid_stack_words next.
  Proof.
    intros Hstack Hbalance.
    unfold MonadVM.Vm.Make.Executor.balance in Hbalance.
    destruct (bind_success_decompose _ _ _ _ _ Hbalance)
      as [after_pop [address [Hpop Hrest]]].
    assert (Hstack_pop : valid_stack_words after_pop).
    { eapply map_pop_preserves_valid_stack_words; eauto. }
    destruct (bind_success_decompose _ _ _ _ _ Hrest)
      as [after_access [access_gas [Haccess Hafter_access]]].
    assert (Hstack_access : valid_stack_words after_access).
    { eapply map_action_preserves_valid_stack_words;
        [|exact Hstack_pop|exact Haccess].
      intros before after access Hbefore Haction.
      eapply host_api_access_account_preserves_valid_stack_words;
        eauto. }
    destruct (bind_success_decompose _ _ _ _ _ Hafter_access)
      as [after_spend [spent_unit [Hspend Hafter_spend]]].
    destruct spent_unit.
    pose proof (spend_preserves_valid_stack_words
      access_gas after_access after_spend Hstack_access Hspend)
      as Hstack_spent.
    cbn beta iota zeta in Hafter_spend.
    destruct (bind_success_decompose _ _ _ _ _ Hafter_spend)
      as [after_value [balance [Hget Hafter_value]]].
    pose proof (host_api_get_balance_preserves_valid_words Hhost
      address after_spend after_value balance Hstack_spent Hget)
      as [Hstack_value Hword].
    destruct (bind_success_decompose _ _ _ _ _ Hafter_value)
      as [after_push [pushed_unit [Hpush Hcontinue]]].
    destruct pushed_unit.
    pose proof (push_preserves_valid_stack_words
      after_value after_push balance Hstack_value Hword Hpush)
      as Hstack_pushed.
    eapply increase_pc_preserves_valid_stack_words; eauto.
  Qed.

  Lemma selfbalance_preserves_valid_stack_words
      {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}
      `{U256 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}
      `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}
      (Hhost : host_balance_words_bounded)
      (state next : State) (continued : bool) :
    valid_stack_words state ->
    @MonadVM.Vm.Make.Executor.selfbalance Host_t F E U256 Ugas state =
      ((inl continued : sum bool MonadVM.Evmc.Result.StatusCode.t),
        next) ->
    valid_stack_words next.
  Proof.
    intros Hstack Hselfbalance.
    unfold MonadVM.Vm.Make.Executor.selfbalance in Hselfbalance.
    destruct (bind_success_decompose _ _ _ _ _ Hselfbalance)
      as [after_spend [spent_unit [Hspend Hafter_spend]]].
    destruct spent_unit.
    pose proof (spend_preserves_valid_stack_words
      MonadVM.Gas.low state after_spend Hstack Hspend)
      as Hstack_spent.
    cbn beta iota zeta in Hafter_spend.
    destruct (bind_success_decompose _ _ _ _ _ Hafter_spend)
      as [after_value [balance [Hget Hafter_value]]].
    pose proof (host_api_get_balance_preserves_valid_words Hhost
      (@MonadVM.Vm.Make.Executor.self Host_t F E)
      after_spend after_value balance Hstack_spent Hget)
      as [Hstack_value Hword].
    destruct (bind_success_decompose _ _ _ _ _ Hafter_value)
      as [after_push [pushed_unit [Hpush Hcontinue]]].
    destruct pushed_unit.
    pose proof (push_preserves_valid_stack_words
      after_value after_push balance Hstack_value Hword Hpush)
      as Hstack_pushed.
    eapply increase_pc_preserves_valid_stack_words; eauto.
  Qed.

  Lemma pop3_preserves_copy_size_range
      (state next : State)
      (dst_start src_start size_bytes : MonadVM.Numeric.U256.t) :
    valid_stack_words state ->
    @MonadVM.Vm.Make.pop3 Host_t F state =
      ((inl (dst_start, src_start, size_bytes) :
        sum (MonadVM.Numeric.U256.t * MonadVM.Numeric.U256.t *
          MonadVM.Numeric.U256.t)
          MonadVM.Evmc.Result.StatusCode.t), next) ->
    (0 <= size_bytes < 2 ^ 256)%Z.
  Proof.
    intros Hstack Hpop.
    unfold valid_stack_words in Hstack.
    unfold MonadVM.Vm.Make.pop3 in Hpop.
    destruct state.(MonadVM.Vm.Make.MachineState.t.stack)
      as [|dst [|src [|size tail]]]; try discriminate.
    inversion Hpop; subst.
    apply Forall_inv_tail in Hstack.
    apply Forall_inv_tail in Hstack.
    now apply Forall_inv in Hstack.
  Qed.

  Lemma extcodecopy_stack_prefix_size_range
      (state after_address after_args : State)
      (address dst_start src_start size_bytes : MonadVM.Numeric.U256.t) :
    valid_stack_words state ->
    @MonadVM.Vm.Make.pop Host_t F state =
      ((inl address : sum MonadVM.Numeric.U256.t
        MonadVM.Evmc.Result.StatusCode.t), after_address) ->
    @MonadVM.Vm.Make.pop3 Host_t F after_address =
      ((inl (dst_start, src_start, size_bytes) :
        sum (MonadVM.Numeric.U256.t * MonadVM.Numeric.U256.t *
          MonadVM.Numeric.U256.t)
          MonadVM.Evmc.Result.StatusCode.t), after_args) ->
    (0 <= size_bytes < 2 ^ 256)%Z.
  Proof.
    intros Hstack Haddress Hargs.
    eapply pop3_preserves_copy_size_range; [|exact Hargs].
    eapply pop_preserves_valid_stack_words; eassumption.
  Qed.
End StackWordRange.

Local Open Scope N_scope.

Section ExternalCodeCopy.
  Context {Host_t : Set} {F : @MonadVM.Vm.Make.FArgs Host_t}.
  Context {E : @MonadVM.Vm.Make.Executor.FArgs Host_t F}.
  Context `{Uuint :
    RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t}.
  Context `{Urepr :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.Repr.t}.
  Context `{U256 :
    RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.U256.t}.
  Context `{Ugas : RocqOfOCaml.Basics.Unreachable MonadVM.Gas.t}.
  Context `{Uaddress :
    RocqOfOCaml.Basics.Unreachable MonadVM.Chain.Ethereum.Address.t}.
  Context `{Ubytes :
    RocqOfOCaml.Basics.Unreachable MonadVM.Byte_string.Bytes.t}.
  Context `{Uunit : RocqOfOCaml.Basics.Unreachable unit}.
  Context `{Ustring : RocqOfOCaml.Basics.Unreachable string}.
  Context `{UlistInt : RocqOfOCaml.Basics.Unreachable (list int)}.
  Context `{Uint : RocqOfOCaml.Basics.Unreachable int}.
  Context `{Uascii : RocqOfOCaml.Basics.Unreachable ascii}.
  Context `{UintPair : RocqOfOCaml.Basics.Unreachable (int * int)}.
  Context `{UuintFunction :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Support.UintN.t -> MonadVM.Support.UintN.t)}.
  Context `{Ub32 :
    RocqOfOCaml.Basics.Unreachable
      MonadVM.Byte_string.B32.(MonadVM.Byte_string.Fixed.Fixed_result.t)}.
  Context `{Uextend :
    RocqOfOCaml.Basics.Unreachable
      (MonadVM.Numeric.U256.t -> MonadVM.Numeric.U256.t ->
        @MonadVM.Vm.Make.Memory.t Host_t F ->
        @MonadVM.Vm.Make.M.Option.t Host_t F
          (@MonadVM.Vm.Make.Memory.t Host_t F))}.

  Let State := @MonadVM.Vm.Make.MachineState.t Host_t F.

  Lemma extcodecopy_prefix_preserves_range_and_cap
      (state0 state1 state2 state3 state4 : State)
      (address_word dst_start src_start size_bytes :
        MonadVM.Numeric.U256.t)
      (address : MonadVM.Vm.Make.Address.t)
      (access : MonadVM.Support.Variants.AccessStatus.t)
      (memory_extension_gas : MonadVM.Gas.t) :
    valid_stack_words state0 ->
    (Z.of_N state0.(MonadVM.Vm.Make.MachineState.t.gas)
      <= 30_000_000)%Z ->
    @MonadVM.Vm.Make.pop Host_t F state0 =
      ((inl address_word : sum MonadVM.Numeric.U256.t
        MonadVM.Evmc.Result.StatusCode.t), state1) ->
    @MonadVM.Vm.Make.pop3 Host_t F state1 =
      ((inl (dst_start, src_start, size_bytes) :
        sum (MonadVM.Numeric.U256.t * MonadVM.Numeric.U256.t *
          MonadVM.Numeric.U256.t)
          MonadVM.Evmc.Result.StatusCode.t), state2) ->
    @MonadVM.Vm.Make.M.HostAPI.access_account Host_t F address state2 =
      ((inl access : sum MonadVM.Support.Variants.AccessStatus.t
        MonadVM.Evmc.Result.StatusCode.t), state3) ->
    @MonadVM.Vm.Make.Executor.extend_memory_to Host_t F E
      Uuint U256 Ugas UuintFunction Uextend
      dst_start size_bytes state3 =
      ((inl memory_extension_gas :
        sum MonadVM.Gas.t MonadVM.Evmc.Result.StatusCode.t), state4) ->
    (0 <= size_bytes < 2 ^ 256)%Z /\
    (Z.of_N state4.(MonadVM.Vm.Make.MachineState.t.gas)
      <= 30_000_000)%Z.
  Proof.
    intros Hstack Hcap Hpop Hpop3 Haccess Hextend.
    split.
    - eapply extcodecopy_stack_prefix_size_range; eassumption.
    - pose proof
        (@pop_nonincreasing Host_t F state0 address_word state1 Hpop)
        as H01.
      pose proof
        (@pop3_nonincreasing Host_t F state1
          (dst_start, src_start, size_bytes) state2 Hpop3) as H12.
      pose proof
        (@access_account_nonincreasing Host_t F address
          state2 access state3 Haccess) as H23.
      pose proof
        (@extend_memory_to_nonincreasing Host_t F E
          Uuint U256 Ugas UuintFunction Uextend dst_start size_bytes
          state3 memory_extension_gas state4 Hextend) as H34.
      apply N2Z.inj_le in H01.
      apply N2Z.inj_le in H12.
      apply N2Z.inj_le in H23.
      apply N2Z.inj_le in H34.
      lia.
  Qed.

  Lemma extcodecopy_conversion_size_fits_after_spend
      (state0 state1 state2 state3 state4 state5 : State)
      (address_word dst_start src_start size_bytes :
        MonadVM.Numeric.U256.t)
      (address : MonadVM.Vm.Make.Address.t)
      (access : MonadVM.Support.Variants.AccessStatus.t)
      (memory_extension_gas : MonadVM.Gas.t) :
    valid_stack_words state0 ->
    (Z.of_N state0.(MonadVM.Vm.Make.MachineState.t.gas)
      <= 30_000_000)%Z ->
    @MonadVM.Vm.Make.pop Host_t F state0 =
      ((inl address_word : sum MonadVM.Numeric.U256.t
        MonadVM.Evmc.Result.StatusCode.t), state1) ->
    @MonadVM.Vm.Make.pop3 Host_t F state1 =
      ((inl (dst_start, src_start, size_bytes) :
        sum (MonadVM.Numeric.U256.t * MonadVM.Numeric.U256.t *
          MonadVM.Numeric.U256.t)
          MonadVM.Evmc.Result.StatusCode.t), state2) ->
    @MonadVM.Vm.Make.M.HostAPI.access_account Host_t F address state2 =
      ((inl access : sum MonadVM.Support.Variants.AccessStatus.t
        MonadVM.Evmc.Result.StatusCode.t), state3) ->
    @MonadVM.Vm.Make.Executor.extend_memory_to Host_t F E
      Uuint U256 Ugas UuintFunction Uextend
      dst_start size_bytes state3 =
      ((inl memory_extension_gas :
        sum MonadVM.Gas.t MonadVM.Evmc.Result.StatusCode.t), state4) ->
    @MonadVM.Vm.Make.spend Host_t F Ugas
      (@MonadVM.Gas.op_plus Ugas
        (@MonadVM.Gas.op_plus Ugas
          (@MonadVM.Gas.op_star Ugas
            (@MonadVM.Numeric.U256.to_uint Uuint
              (@MonadVM.Numeric.U256.bytes_to_whole_words U256
                size_bytes))
            (@MonadVM.Gas.copy_cost_per_word Ugas))
          memory_extension_gas)
        (@MonadVM.Gas.account_access_cost Ugas access)) state4 =
      ((inl tt : sum unit MonadVM.Evmc.Result.StatusCode.t), state5) ->
    exists native_size,
      @MonadVM.Numeric.U256.to_int_opt Uint size_bytes =
        Some native_size.
  Proof.
    intros Hstack Hcap Hpop Hpop3 Haccess Hextend Hspent.
    pose proof
      (extcodecopy_prefix_preserves_range_and_cap
        state0 state1 state2 state3 state4 address_word
        dst_start src_start size_bytes address access
        memory_extension_gas Hstack Hcap Hpop Hpop3 Haccess Hextend)
      as [Hsize Hcap4].
    eapply (@extcodecopy_successful_spend_size_fits
      U256 Uuint Uint Ugas Host_t F size_bytes memory_extension_gas
      (@MonadVM.Gas.account_access_cost Ugas access) state4 state5);
      eassumption.
  Qed.

  Lemma copy_code_nonincreasing
      (address : MonadVM.Vm.Make.Address.t)
      (offset size : int) :
    gas_nonincreasing
      (@MonadVM.Vm.Make.M.HostAPI.copy_code Host_t F
        address offset size).
  Proof.
    unfold MonadVM.Vm.Make.M.HostAPI.copy_code.
    apply host_lift_nonincreasing.
  Qed.

  Lemma extcodecopy_opcode_compositional_decreasing :
    gas_decreasing
      (@MonadVM.Vm.Make.Executor.extcodecopy Host_t F E
        Uuint Urepr U256 Ugas Uaddress Ubytes Uunit Ustring
        UlistInt Uint Uascii UintPair UuintFunction Ub32 Uextend).
  Proof.
    unfold MonadVM.Vm.Make.Executor.extcodecopy.
    eapply bind_decrease_after_preserve.
    { apply map_nonincreasing. apply pop_nonincreasing. }
    intro address.
    eapply bind_decrease_after_preserve.
    { apply pop3_nonincreasing. }
    intros [[dst_start src_start] size_bytes].
    eapply (bind_decrease_after_preserve_if _ _
      (fun access_gas => 0 < access_gas)).
    { apply map_nonincreasing. apply access_account_nonincreasing. }
    { intros state access_gas next Hsuccess.
      eapply (@access_charge_success_positive Host_t F Ugas);
        exact Hsuccess. }
    intros access_gas Hpositive.
    eapply bind_decrease_after_preserve.
    { apply extend_memory_to_nonincreasing. }
    intro memory_extension_gas.
    eapply spend_then_preserving_decreases.
    { unfold MonadVM.Gas.op_plus, MonadVM.Support.UintN.op_plus.
      lia. }
    intros [].
    eapply bind_nonincreasing.
    { destruct (@MonadVM.Numeric.U256.to_int_opt Uint src_start)
        as [offset|] eqn:Hoffset;
      destruct (@MonadVM.Numeric.U256.to_int_opt Uint size_bytes)
        as [size|] eqn:Hsize.
      - destruct size.
        + apply return_nonincreasing.
        + apply map_nonincreasing. apply copy_code_nonincreasing.
        + apply map_nonincreasing. apply copy_code_nonincreasing.
      - apply fail_nonincreasing.
      - destruct size; apply return_nonincreasing.
      - apply fail_nonincreasing. }
    intros [size block].
    eapply bind_nonincreasing.
    { apply memory_update_nonincreasing. }
    intros [].
    eapply bind_nonincreasing.
    { destruct (Z.ltb (MonadVM.Byte_string.Bytes.length block) size);
        [apply memory_update_nonincreasing |
         apply return_nonincreasing]. }
    intros []. apply increase_pc_nonincreasing.
  Qed.
End ExternalCodeCopy.
