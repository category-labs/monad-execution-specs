(** Gas safety of generated elliptic-curve precompile parsers. *)

Require Import RocqOfOCaml.RocqOfOCaml.
Require Import MonadExecutionSpecs.Termination.VmPrecompileGasInvariant.
Require MonadVM.Precompiles.Utils.
Require MonadVM.Support.UintN.

Section EcReaders.
Context {coord_repr curve_point field_extension curve2_point : Set}.
Context `{F : @MonadVM.Precompiles.Utils.Ec_precompile_utils.FArgs
  coord_repr curve_point field_extension curve2_point}.
Context `{UCount : RocqOfOCaml.Basics.Unreachable
  MonadVM.Support.UintN.t}.
Context `{UAscii : RocqOfOCaml.Basics.Unreachable ascii}.
Context `{UFp2Fallback : RocqOfOCaml.Basics.Unreachable
  (MonadVM.Precompiles.Utils.Precompile.t field_extension)}.

Lemma ec_field_element_gas_safe :
  precompile_gas_safe
    (MonadVM.Precompiles.Utils.Ec_precompile_utils.f_p
      (_rocq_assumption_0 := UCount)
      (_rocq_assumption_1 := UAscii)).
Proof.
  unfold MonadVM.Precompiles.Utils.Ec_precompile_utils.f_p.
  eapply precompile_bind_gas_safe.
  - apply precompile_fmap_gas_safe.
    apply precompile_fmap_gas_safe.
    apply precompile_byte_reader_gas_safe.
  - intro value. apply precompile_option_or_fail_gas_safe.
Qed.

Lemma ec_curve_point_gas_safe :
  precompile_gas_safe
    (MonadVM.Precompiles.Utils.Ec_precompile_utils.point_c1
      (_rocq_assumption_0 := UCount)
      (_rocq_assumption_1 := UAscii)).
Proof.
  unfold MonadVM.Precompiles.Utils.Ec_precompile_utils.point_c1.
  eapply precompile_bind_gas_safe.
  - exact ec_field_element_gas_safe.
  - intro x.
    eapply precompile_bind_gas_safe.
    + exact ec_field_element_gas_safe.
    + intro y. apply precompile_option_or_fail_gas_safe.
Qed.

Lemma ec_subgroup_point_gas_safe :
  precompile_gas_safe
    (MonadVM.Precompiles.Utils.Ec_precompile_utils.point_g1
      (_rocq_assumption_0 := UCount)
      (_rocq_assumption_1 := UAscii)).
Proof.
  unfold MonadVM.Precompiles.Utils.Ec_precompile_utils.point_g1.
  eapply precompile_bind_gas_safe.
  - exact ec_curve_point_gas_safe.
  - intro point. apply precompile_option_or_fail_gas_safe.
Qed.

Definition complex_encoding_tag
    (encoding : RocqOfOCaml.Basics.Variant.t) : string :=
  match encoding with
  | RocqOfOCaml.Basics.Variant.Build tag _ _ => tag
  end.

Definition supported_complex_encoding : Prop :=
  let tag := complex_encoding_tag
    (@MonadVM.Precompiles.Utils.Ec_precompile_utils.M
      coord_repr curve_point field_extension curve2_point F)
      .(MonadVM.Precompiles.Utils.Ec_precompile_utils_M_signature.complex_encoding) in
  String.eqb tag "Real_first" = true \/
  String.eqb tag "Imaginary_first" = true.

Lemma ec_extension_field_gas_safe :
  supported_complex_encoding ->
  precompile_gas_safe
    (MonadVM.Precompiles.Utils.Ec_precompile_utils.f_p2
      (_rocq_assumption_0 := UCount)
      (_rocq_assumption_1 := UAscii)).
Proof.
  unfold supported_complex_encoding,
    MonadVM.Precompiles.Utils.Ec_precompile_utils.f_p2.
  destruct
    (@MonadVM.Precompiles.Utils.Ec_precompile_utils.M
      coord_repr curve_point field_extension curve2_point F)
      .(MonadVM.Precompiles.Utils.Ec_precompile_utils_M_signature.complex_encoding)
    as [tag payload_type payload].
  cbn.
  intro Htag.
  destruct (String.eqb tag "Real_first") eqn:Hreal.
  - eapply precompile_bind_gas_safe.
    + exact ec_field_element_gas_safe.
    + intro first.
      eapply precompile_bind_gas_safe.
      * exact ec_field_element_gas_safe.
      * intro second. apply precompile_return_gas_safe.
  - destruct (String.eqb tag "Imaginary_first") eqn:Himag.
    + eapply precompile_bind_gas_safe.
      * exact ec_field_element_gas_safe.
      * intro first.
        eapply precompile_bind_gas_safe.
        -- exact ec_field_element_gas_safe.
        -- intro second. apply precompile_return_gas_safe.
    + destruct Htag as [Htag | Htag]; congruence.
Qed.

Lemma ec_extension_curve_point_gas_safe :
  supported_complex_encoding ->
  precompile_gas_safe
    (MonadVM.Precompiles.Utils.Ec_precompile_utils.point_c2
      (_rocq_assumption_0 := UCount)
      (_rocq_assumption_1 := UAscii)).
Proof.
  intro Htag.
  unfold MonadVM.Precompiles.Utils.Ec_precompile_utils.point_c2.
  eapply precompile_bind_gas_safe.
  - apply ec_extension_field_gas_safe. exact Htag.
  - intro x.
    eapply precompile_bind_gas_safe.
    + apply ec_extension_field_gas_safe. exact Htag.
    + intro y. apply precompile_option_or_fail_gas_safe.
Qed.

Lemma ec_extension_subgroup_point_gas_safe :
  supported_complex_encoding ->
  precompile_gas_safe
    (MonadVM.Precompiles.Utils.Ec_precompile_utils.point_g2
      (_rocq_assumption_0 := UCount)
      (_rocq_assumption_1 := UAscii)).
Proof.
  intro Htag.
  unfold MonadVM.Precompiles.Utils.Ec_precompile_utils.point_g2.
  eapply precompile_bind_gas_safe.
  - apply ec_extension_curve_point_gas_safe. exact Htag.
  - intro point. apply precompile_option_or_fail_gas_safe.
Qed.
End EcReaders.
