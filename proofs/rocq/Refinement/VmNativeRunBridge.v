(** A finite-step bridge for the native VM's gas guard.

    The native and generated dispatchers are parameters here. Instantiating
    [dispatch_encoding] for the actual OCaml VM, including host callbacks and
    exceptional paths, is the outstanding native/model refinement obligation.
    The result below does not assume that obligation has been discharged. *)

From Stdlib Require Import NArith ZArith Lia.

Section NativeRunBridge.
  Context {NativeState ModelState Error : Type}.
  Variable encode : NativeState -> ModelState.
  Variable native_gas : NativeState -> Z.
  Variable model_gas : ModelState -> N.
  Variable native_dispatch : NativeState -> (bool + Error) * NativeState.
  Variable model_dispatch : ModelState -> (bool + Error) * ModelState.

  Definition bounded (state : ModelState) : Prop :=
    (Z.of_N (model_gas state) < 2 ^ 63)%Z.

  Hypothesis gas_encoding : forall state,
    native_gas state = Z.of_N (model_gas (encode state)).

  Hypothesis dispatch_encoding : forall state result next,
    native_dispatch state = (result, next) ->
    model_dispatch (encode state) = (result, encode next).

  Hypothesis model_progress : forall state next,
    bounded state ->
    model_dispatch state = (inl true, next) ->
    (model_gas next < model_gas state)%N /\ bounded next.

  (** [inr tt] records the native guard's exceptional branch. [None] means
      that the finite observation ran out of fuel. *)
  Fixpoint native_run_fuel (fuel : nat) (state : NativeState) :
      option (((unit + Error) * NativeState) + unit) :=
    match fuel with
    | O => None
    | S remaining =>
        let '(result, next) := native_dispatch state in
        match result with
        | inl true =>
            if Z.ltb (native_gas next) (native_gas state)
            then native_run_fuel remaining next
            else Some (inr tt)
        | inl false => Some (inl (inl tt, next))
        | inr error => Some (inl (inr error, next))
        end
    end.

  Fixpoint model_run_fuel (fuel : nat) (state : ModelState) :
      option ((unit + Error) * ModelState) :=
    match fuel with
    | O => None
    | S remaining =>
        let '(result, next) := model_dispatch state in
        match result with
        | inl true => model_run_fuel remaining next
        | inl false => Some (inl tt, next)
        | inr error => Some (inr error, next)
        end
    end.

  Theorem finite_run_correspondence : forall fuel state,
    bounded (encode state) ->
    match native_run_fuel fuel state with
    | None => model_run_fuel fuel (encode state) = None
    | Some (inl (result, next)) =>
        model_run_fuel fuel (encode state) =
          Some (result, encode next)
    | Some (inr tt) => False
    end.
  Proof.
    induction fuel as [|fuel IH]; intros state Hbound; simpl.
    - reflexivity.
    - destruct (native_dispatch state) as [[continue | error] next]
        eqn:Hnative; simpl.
      + pose proof (dispatch_encoding state (inl continue) next Hnative)
          as Hmodel.
        rewrite Hmodel.
        destruct continue.
        * pose proof (model_progress (encode state) (encode next)
            Hbound Hmodel) as [Hdecrease Hnext_bound].
          assert (Hguard :
            Z.ltb (native_gas next) (native_gas state) = true).
          { apply Z.ltb_lt. rewrite !gas_encoding.
            apply N2Z.inj_lt. exact Hdecrease. }
          rewrite Hguard. apply IH. exact Hnext_bound.
        * reflexivity.
      + pose proof (dispatch_encoding state (inr error) next Hnative)
          as Hmodel.
        rewrite Hmodel. reflexivity.
  Qed.

  Corollary native_guard_unreachable_within_fuel : forall fuel state,
    bounded (encode state) ->
    native_run_fuel fuel state <> Some (inr tt).
  Proof.
    intros fuel state Hbound Hguard.
    pose proof (finite_run_correspondence fuel state Hbound) as Hsim.
    rewrite Hguard in Hsim. exact Hsim.
  Qed.

  Lemma model_run_fuel_terminates : forall fuel state,
    bounded state ->
    (N.to_nat (model_gas state) < fuel)%nat ->
    exists result, model_run_fuel fuel state = Some result.
  Proof.
    induction fuel as [|fuel IH]; intros state Hbound Hfuel.
    - lia.
    - simpl.
      destruct (model_dispatch state) as [[continue | error] next]
        eqn:Hdispatch.
      + destruct continue.
        * pose proof (model_progress state next Hbound Hdispatch)
            as [Hdecrease Hnext_bound].
          apply IH.
          -- exact Hnext_bound.
          -- assert (Hdecrease_nat :
               (N.to_nat (model_gas next) <
                 N.to_nat (model_gas state))%nat).
             { apply Nat.compare_lt_iff.
               rewrite <- N2Nat.inj_compare.
               apply N.compare_lt_iff. exact Hdecrease. }
             lia.
        * eexists. reflexivity.
      + eexists. reflexivity.
  Qed.

  Theorem native_run_fuel_terminates : forall fuel state,
    bounded (encode state) ->
    (N.to_nat (model_gas (encode state)) < fuel)%nat ->
    exists result next,
      native_run_fuel fuel state = Some (inl (result, next)).
  Proof.
    intros fuel state Hbound Hfuel.
    pose proof (model_run_fuel_terminates fuel (encode state)
      Hbound Hfuel) as [result Hmodel].
    pose proof (finite_run_correspondence fuel state Hbound) as Hsim.
    destruct (native_run_fuel fuel state) as [[[[stop | error] next] | []] |]
      eqn:Hnative; simpl in Hsim.
    - exists (inl stop), next. reflexivity.
    - exists (inr error), next. reflexivity.
    - contradiction.
    - rewrite Hmodel in Hsim. discriminate.
  Qed.

  Corollary native_run_entry_gas_fuel_terminates : forall state,
    bounded (encode state) ->
    exists result next,
      native_run_fuel (S (N.to_nat (model_gas (encode state)))) state =
        Some (inl (result, next)).
  Proof.
    intros state Hbound.
    apply native_run_fuel_terminates.
    - exact Hbound.
    - lia.
  Qed.

  Corollary native_run_entry_gas_fuel_corresponds : forall state,
    bounded (encode state) ->
    exists result next,
      native_run_fuel (S (N.to_nat (model_gas (encode state)))) state =
        Some (inl (result, next)) /\
      model_run_fuel (S (N.to_nat (model_gas (encode state))))
        (encode state) = Some (result, encode next).
  Proof.
    intros state Hbound.
    destruct (native_run_entry_gas_fuel_terminates state Hbound)
      as [result [next Hnative]].
    exists result, next.
    split; [exact Hnative |].
    pose proof (finite_run_correspondence
      (S (N.to_nat (model_gas (encode state)))) state Hbound) as Hsim.
    rewrite Hnative in Hsim.
    exact Hsim.
  Qed.
End NativeRunBridge.
