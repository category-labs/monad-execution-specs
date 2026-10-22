From Stdlib Require Import Bool List String ZArith.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import MonadVM.Ec.Bls12_381.
Require Import MonadVM.Numeric.
Require Import MonadVM.Support.UintN.

Import ListNotations.
Open Scope string_scope.

(** The 77 hexadecimal strings used by the generated BLS12-381 map-to-curve
    definitions, in their generated source order. The companion inventory
    check prevents this finite proof from silently omitting a new literal. *)
Definition bls_map_hex_literals : list string :=
[
  "0x144698A3B8E9433D693A02C96D4982B0EA985383EE66A8D8E8981AEFD881AC98936F8DA0E0F97F5CF428082D584C1D"
  ; "0x12E2908D11688030018B12E8753EEE3B2016C1F0F24F4070A0B9C14FCEF35EF55A23215A316CEAA5D1CC48E98E172BE0"
  ; "0x11A05F2B1E833340B809101DD99815856B303E88A2D7005FF2627B56CDB4E2C85610C2D5F2E62D6EAEAC1662734649B7"
  ; "0x17294ED3E943AB2F0588BAB22147A81C7C17E75B2F6A8417F565E33C70D1E86B4838F2A6F318C356E834EEF1B3CB83BB"
  ; "0xD54005DB97678EC1D1048C5D10A9A1BCE032473295983E56878E501EC68E25C958C3E3D2A09729FE0179F9DAC9EDCB0"
  ; "0x1778E7166FCC6DB74E0609D307E55412D7F5E4656A8DBF25F1B33289F1B330835336E25CE3107193C5B388641D9B6861"
  ; "0xE99726A3199F4436642B4B3E4118E5499DB995A1257FB3F086EEB65982FAC18985A286F301E77C451154CE9AC8895D9"
  ; "0x1630C3250D7313FF01D1201BF7A74AB5DB3CB17DD952799B9ED3AB9097E68F90A0870D2DCAE73D19CD13C1C66F652983"
  ; "0xD6ED6553FE44D296A3726C38AE652BFB11586264F0F8CE19008E218F9C86B2A8DA25128C1052ECADDD7F225A139ED84"
  ; "0x17B81E7701ABDBE2E8743884D1117E53356DE5AB275B4DB1A682C62EF0F2753339B7C8F8C8F475AF9CCB5618E3F0C88E"
  ; "0x80D3CF1F9A78FC47B90B33563BE990DC43B756CE79F5574A2C596C928C5D1DE4FA295F296B74E956D71986A8497E317"
  ; "0x169B1F8E1BCFA7C42E0C37515D138F22DD2ECB803A0C5C99676314BAF4BB1B7FA3190B2EDC0327797F241067BE390C9E"
  ; "0x10321DA079CE07E272D8EC09D2565B0DFA7DCCDDE6787F96D50AF36003B14866F69B771F8C285DECCA67DF3F1605FB7B"
  ; "0x6E08C248E260E70BD1E962381EDEE3D31D79D7E22C837BC23C0BF1BC24C6B68C24B1B80B64D391FA9C8BA2E8BA2D229"
  ; "0x8CA8D548CFF19AE18B2E62F4BD3FA6F01D5EF4BA35B48BA9C9588617FC8AC62B558D681BE343DF8993CF9FA40D21B1C"
  ; "0x12561A5DEB559C4348B4711298E536367041E8CA0CF0800C0126C2588C48BF5713DAA8846CB026E9E5C8276EC82B3BFF"
  ; "0xB2962FE57A3225E8137E629BFF2991F6F89416F5A718CD1FCA64E00B11ACEACD6A3D0967C94FEDCFCC239BA5CB83E19"
  ; "0x3425581A58AE2FEC83AAFEF7C40EB545B08243F16B1655154CCA8ABC28D6FD04976D5243EECF5C4130DE8938DC62CD8"
  ; "0x13A8E162022914A80A6F1D5F43E7A07DFFDFC759A12062BB8D6B44E833B306DA9BD29BA81F35781D539D395B3532A21E"
  ; "0xE7355F8E4E667B955390F7F0506C6E9395735E9CE9CAD4D0A43BCEF24B8982F7400D24BC4228F11C02DF9A29F6304A5"
  ; "0x772CAACF16936190F3E0C63E0596721570F5799AF53A1894E2E073062AEDE9CEA73B3538F0DE06CEC2574496EE84A3A"
  ; "0x14A7AC2A9D64A8B230B3F5B074CF01996E7F63C21BCA68A81996E1CDF9822C580FA5B9489D11E2D311F7D99BBDCC5A5E"
  ; "0xA10ECF6ADA54F825E920B3DAFC7A3CCE07F8D1D7161366B74100DA67F39883503826692ABBA43704776EC3A79A1D641"
  ; "0x95FC13AB9E92AD4476D6E3EB3A56680F682B4EE96F7D03776DF533978F31C1593174E4B4B7865002D6384D168ECDD0A"
  ; "0x90D97C81BA24EE0259D1F094980DCFA11AD138E48A869522B52AF6C956543D3CD0C7AEE9B3BA3C2BE9845719707BB33"
  ; "0x134996A104EE5811D51036D776FB46831223E96C254F383D0F906343EB67AD34D6C56711962FA8BFE097E75A2E41C696"
  ; "0xCC786BAA966E66F4A384C86A3B49942552E2D658A31CE2C344BE4B91400DA7D26D521628B00523B8DFE240C72DE1F6"
  ; "0x1F86376E8981C217898751AD8746757D42AA7B90EEB791C09E4A3EC03251CF9DE405ABA9EC61DECA6355C77B0E5F4CB"
  ; "0x8CC03FDEFE0FF135CAF4FE2A21529C4195536FBE3CE50B879833FD221351ADC2EE7F8DC099040A841B6DAECF2E8FEDB"
  ; "0x16603FCA40634B6A2211E11DB8F0A6A074A7D0D4AFADB7BD76505C3D3AD5544E203F6326C95A807299B23AB13633A5F0"
  ; "0x4AB0B9BCFAC1BBCB2C977D027796B3CE75BB8CA2BE184CB5231413C4D634F3747A87AC2460F415EC961F8855FE9D6F2"
  ; "0x987C8D5333AB86FDE9926BD2CA6C674170A05BFE3BDD81FFD038DA6C26C842642F64550FEDFE935A15E4CA31870FB29"
  ; "0x9FC4018BD96684BE88C9E221E4DA1BB8F3ABD16679DC26C1E8B6E6A1F20CABE69D65201C78607A360370E577BDBA587"
  ; "0xE1BBA7A1186BDB5223ABDE7ADA14A23C42A0CA7915AF6FE06985E7ED1E4D43B9B3F7055DD4EBA6F2BAFAAEBCA731C30"
  ; "0x19713E47937CD1BE0DFD0B8F1D43FB93CD2FCBCB6CAF493FD1183E416389E61031BF3A5CCE3FBAFCE813711AD011C132"
  ; "0x18B46A908F36F6DEB918C143FED2EDCC523559B8AAF0C2462E6BFE7F911F643249D9CDF41B44D606CE07C8A4D0074D8E"
  ; "0xB182CAC101B9399D155096004F53F447AA7B12A3426B08EC02710E807B4633F06C851C1919211F20D4C04F00B971EF8"
  ; "0x245A394AD1ECA9B72FC00AE7BE315DC757B3B080D4C158013E6632D3C40659CC6CF90AD1C232A6442D9D3F5DB980133"
  ; "0x5C129645E44CF1102A159F748C4A3FC5E673D81D7E86568D9AB0F5D396A7CE46BA1049B6579AFB7866B1E715475224B"
  ; "0x15E6BE4E990F03CE4EA50B3B42DF2EB5CB181D8F84965A3957ADD4FA95AF01B2B665027EFEC01C7704B456BE69C8B604"
  ; "0x16112C4C3A9C98B252181140FAD0EAE9601A6DE578980BE6EEC3232B5BE72E7A07F3688EF60C206D01479253B03663C1"
  ; "0x1962D75C2381201E1A0CBD6C43C348B885C84FF731C4D59CA4A10356F453E01F78A4260763529E3532F6102C2E49A03D"
  ; "0x58DF3306640DA276FAAAE7D6E8EB15778C4855551AE7F310C35A5DD279CD2ECA6757CD636F96F891E2538B53DBF67F2"
  ; "0x16B7D288798E5395F20D23BF89EDB4D1D115C5DBDDBCD30E123DA489E726AF41727364F2C28297ADA8D26D98445F5416"
  ; "0xBE0E079545F43E4B00CC912F8228DDCC6D19C9F0F69BBB0542EDA0FC9DEC916A20B15DC0FD2EDEDDA39142311A5001D"
  ; "0x8D9E5297186DB2D9FB266EAAC783182B70152C65550D881C5ECD87B6F0F5A6449F38DB9DFA9CCE202C6477FAAF9B7AC"
  ; "0x166007C08A99DB2FC3BA8734ACE9824B5EECFDFA8D0CF8EF5DD365BC400A0051D5FA9C01A58B1FB93D1A1399126A775C"
  ; "0x16A3EF08BE3EA7EA03BCDDFABBA6FF6EE5A4375EFA1F4FD7FEB34FD206357132B920F5B00801DEE460EE415A15812ED9"
  ; "0x1866C8ED336C61231A1BE54FD1D74CC4F9FB0CE4C6AF5920ABC5750C4BF39B4852CFE2F7BB9248836B233D9D55535D4A"
  ; "0x167A55CDA70A6E1CEA820597D94A84903216F763E13D87BB5308592E7EA7D4FBC7385EA3D529B35E346EF48BB8913F55"
  ; "0x4D2F259EEA405BD48F010A01AD2911D9C6DD039BB61A6290E591B36E636A5C871A5C29F4F83060400F8B49CBA8F6AA8"
  ; "0xACCBB67481D033FF5852C1E48C50C477F94FF8AEFCE42D28C0F9A88CEA7913516F968986F7EBBEA9684B529E2561092"
  ; "0xAD6B9514C767FE3C3613144B45F1496543346D98ADF02267D5CEEF9A00D9B8693000763E3B90AC11E99B138573345CC"
  ; "0x2660400EB2E4F3B628BDD0D53CD76F2BF565B94E72927C1CB748DF27942480E420517BD8714CC80D1FADC1326ED06F7"
  ; "0xE0FA1D816DDC03E6B24255E0D7819C171C40F65E273B853324EFCD6356CAA205CA2F570F13497804415473A1D634B8F"
  ; "0xD201000000010001"
  ; "0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97d6"
  ; "0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97d6"
  ; "0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71a"
  ; "0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71e"
  ; "0x8ab05f8bdd54cde190937e76bc3e447cc27c3d6fbd7063fcd104635a790520c0a395554e5c6aaaa9354ffffffffe38d"
  ; "0x171d6541fa38ccfaed6dea691f5fb614cb14b4e7f4e810aa22d6108f142b85757098e38d0f671c7188e2aaaaaaaa5ed1"
  ; "0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa63"
  ; "0xc"
  ; "0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa9f"
  ; "0x1530477c7ab4113b59a4c18b076d11930f7da5d4a07f649bf54439d87d27e500fc8c25ebf8c92f6812cfc71c71c6d706"
  ; "0x1530477c7ab4113b59a4c18b076d11930f7da5d4a07f649bf54439d87d27e500fc8c25ebf8c92f6812cfc71c71c6d706"
  ; "0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97be"
  ; "0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71c"
  ; "0x8ab05f8bdd54cde190937e76bc3e447cc27c3d6fbd7063fcd104635a790520c0a395554e5c6aaaa9354ffffffffe38f"
  ; "0x124c9ad43b6cf79bfbf7043de3811ad0761b0f37a1e26286b0e977c69aa274524e79097a56dc4bd9e1b371c71c718b10"
  ; "0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa8fb"
  ; "0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa8fb"
  ; "0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa9d3"
  ; "0x12"
  ; "0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa99"
  ; "0xbc69f08f2ee75b3584c6a0ea91b352888e2a8e9145ad7689986ff031508ffe1329c2f178731db956d82bf015d1212b02ec0ec69d7477c1ae954cbc06689f6a359894c0adebbf6b4e8020005aaa95551"
].

Definition every_bls_map_hex_literal_parses : bool :=
  forallb
    (fun literal =>
      match RocqOfOCaml.OCamlZ.of_string_opt literal with
      | Some _ => true
      | None => false
      end)
    bls_map_hex_literals.

Lemma every_bls_map_hex_literal_parses_true :
  every_bls_map_hex_literal_parses = true.
Proof. vm_compute. reflexivity. Qed.

Lemma bls_map_hex_literal_parser_independent
    (literal : string)
    (U1 U2 : RocqOfOCaml.Basics.Unreachable Z)
    (H : In literal bls_map_hex_literals) :
  @RocqOfOCaml.OCamlZ.of_string U1 literal =
  @RocqOfOCaml.OCamlZ.of_string U2 literal.
Proof.
  pose proof every_bls_map_hex_literal_parses_true as Hparse.
  unfold every_bls_map_hex_literal_parses in Hparse.
  pose proof
    (proj1
      (@forallb_forall string
        (fun value =>
          match RocqOfOCaml.OCamlZ.of_string_opt value with
          | Some _ => true
          | None => false
          end)
        bls_map_hex_literals)
      Hparse literal H) as Hsuccess.
  cbn beta in Hsuccess.
  unfold RocqOfOCaml.OCamlZ.of_string.
  destruct (RocqOfOCaml.OCamlZ.of_string_opt literal).
  - reflexivity.
  - discriminate Hsuccess.
Qed.

Print Assumptions bls_map_hex_literal_parser_independent.

(** Each generated F_p string-to-field conversion also has a stable value
    across all five fallback instances in its signature. This checks the
    field boundary used by the map tables, beyond the raw integer parser. *)
Definition field_literal_independent (literal : string) : Prop :=
  forall
    (UZ1 UZ2 : RocqOfOCaml.Basics.Unreachable Z.t)
    (UN1 UN2 : RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t)
    (UB1 UB2 : RocqOfOCaml.Basics.Unreachable
      MonadVM.Numeric.IntegerBase.(MonadVM.Numeric.Make.Make_result.t))
    (UX1 UX2 : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.Integer.t)
    (UF1 : RocqOfOCaml.Basics.Unreachable
      (@MonadVM.Ec.Bls12_381.F_p.t UZ1 UN1 UB1))
    (UF2 : RocqOfOCaml.Basics.Unreachable
      (@MonadVM.Ec.Bls12_381.F_p.t UZ2 UN2 UB2)),
  @MonadVM.Ec.Bls12_381.F_p.op_tildeat UZ1 UN1 UX1 UB1 UF1 literal =
  @MonadVM.Ec.Bls12_381.F_p.op_tildeat UZ2 UN2 UX2 UB2 UF2 literal.

Lemma every_bls_field_literal_independent :
  Forall field_literal_independent bls_map_hex_literals.
Proof.
  unfold bls_map_hex_literals.
  repeat constructor; unfold field_literal_independent; intros;
    vm_compute; reflexivity.
Qed.

Print Assumptions every_bls_field_literal_independent.

(** The generated field conversion has the expected reduced integer value,
    not only the same value under two choices of fallback parameters. The
    modulus is the BLS12-381 field prime checked separately by
    [GeneratedConstantAudit.bls12_381_field_prime]. *)
Definition bls_map_field_modulus : Z :=
  4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787.

Lemma bls_map_field_modulus_matches_generated_prime
    `{UZ : RocqOfOCaml.Basics.Unreachable Z.t}
    `{UN : RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t} :
  Z.of_N MonadVM.Ec.Bls12_381.p_value = bls_map_field_modulus.
Proof. vm_compute. reflexivity. Qed.

Definition field_literal_matches_modulus (literal : string) : Prop :=
  forall
    (UZ : RocqOfOCaml.Basics.Unreachable Z.t)
    (UN : RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t)
    (UB : RocqOfOCaml.Basics.Unreachable
      MonadVM.Numeric.IntegerBase.(MonadVM.Numeric.Make.Make_result.t))
    (UX : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.Integer.t)
    (UF : RocqOfOCaml.Basics.Unreachable
      (@MonadVM.Ec.Bls12_381.F_p.t UZ UN UB)),
  @MonadVM.Ec.Bls12_381.F_p.op_tildeat UZ UN UX UB UF literal =
  match RocqOfOCaml.OCamlZ.of_string_opt literal with
  | Some value => Z.modulo value bls_map_field_modulus
  | None => 0%Z
  end.

Lemma every_bls_field_literal_matches_modulus :
  Forall field_literal_matches_modulus bls_map_hex_literals.
Proof.
  unfold bls_map_hex_literals.
  repeat constructor; unfold field_literal_matches_modulus,
    bls_map_field_modulus; intros; vm_compute; reflexivity.
Qed.

Print Assumptions every_bls_field_literal_matches_modulus.

(** The final string coefficient of each G1 and G2 isogeny polynomial is
    nonzero after generated field conversion. The denominator tables end in
    ["1"]; the other strings are their final numerator coefficients. *)
Definition bls_g1_isogeny_final_literals : list string :=
  ["0x6E08C248E260E70BD1E962381EDEE3D31D79D7E22C837BC23C0BF1BC24C6B68C24B1B80B64D391FA9C8BA2E8BA2D229";
   "1";
   "0x15E6BE4E990F03CE4EA50B3B42DF2EB5CB181D8F84965A3957ADD4FA95AF01B2B665027EFEC01C7704B456BE69C8B604";
   "1"].

Definition bls_g2_isogeny_final_literals : list string :=
  ["0x171d6541fa38ccfaed6dea691f5fb614cb14b4e7f4e810aa22d6108f142b85757098e38d0f671c7188e2aaaaaaaa5ed1";
   "1";
   "0x124c9ad43b6cf79bfbf7043de3811ad0761b0f37a1e26286b0e977c69aa274524e79097a56dc4bd9e1b371c71c718b10";
   "1"].

Definition g1_isogeny_final_nonzero (literal : string) : Prop :=
  forall
    (UZ : RocqOfOCaml.Basics.Unreachable Z.t)
    (UN : RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t)
    (UB : RocqOfOCaml.Basics.Unreachable
      MonadVM.Numeric.IntegerBase.(MonadVM.Numeric.Make.Make_result.t))
    (UX : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.Integer.t)
    (UF : RocqOfOCaml.Basics.Unreachable
      (@MonadVM.Ec.Bls12_381.F_p.t UZ UN UB)),
  @MonadVM.Ec.Bls12_381.F_p.op_eq UZ UN UB
    (@MonadVM.Ec.Bls12_381.F_p.op_tildeat UZ UN UX UB UF literal)
    (@MonadVM.Ec.Bls12_381.F_p.zero UZ UN UX UB UF) = false.

Definition g2_isogeny_final_nonzero (literal : string) : Prop :=
  forall
    (UZ : RocqOfOCaml.Basics.Unreachable Z.t)
    (UN : RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t)
    (UB : RocqOfOCaml.Basics.Unreachable
      MonadVM.Numeric.IntegerBase.(MonadVM.Numeric.Make.Make_result.t))
    (UX : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.Integer.t)
    (UF : RocqOfOCaml.Basics.Unreachable
      (@MonadVM.Ec.Bls12_381.F_p.t UZ UN UB)),
  @MonadVM.Ec.Bls12_381.F_p2.op_eq UZ UN UX UB UF
    (@MonadVM.Ec.Bls12_381.F_p2.op_tildeat UZ UN UX UB UF literal)
    (@MonadVM.Ec.Bls12_381.F_p2.zero UZ UN UX UB UF) = false.

Lemma every_g1_isogeny_final_literal_nonzero :
  Forall g1_isogeny_final_nonzero bls_g1_isogeny_final_literals.
Proof.
  unfold bls_g1_isogeny_final_literals.
  repeat constructor; unfold g1_isogeny_final_nonzero; intros;
    vm_compute; reflexivity.
Qed.

Lemma every_g2_isogeny_final_literal_nonzero :
  Forall g2_isogeny_final_nonzero bls_g2_isogeny_final_literals.
Proof.
  unfold bls_g2_isogeny_final_literals.
  repeat constructor; unfold g2_isogeny_final_nonzero; intros;
    vm_compute; reflexivity.
Qed.

Print Assumptions every_g1_isogeny_final_literal_nonzero.
Print Assumptions every_g2_isogeny_final_literal_nonzero.

(** The first G1 numerator isogeny polynomial is a complete table-level
    check. The 77-literal inventory places its twelve coefficient strings
    immediately after the two SWU-curve parameters. The generated
    [of_coeffs] computation agrees with their parsed, reduced values for
    every typed fallback instance. *)
Definition parsed_bls_field_literal (literal : string) : Z :=
  match RocqOfOCaml.OCamlZ.of_string_opt literal with
  | Some value => Z.modulo value bls_map_field_modulus
  | None => 0%Z
  end.

Lemma generated_g1_x_num_matches_literals
    (UZ : RocqOfOCaml.Basics.Unreachable Z.t)
    (UN : RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t)
    (UB : RocqOfOCaml.Basics.Unreachable
      MonadVM.Numeric.IntegerBase.(MonadVM.Numeric.Make.Make_result.t))
    (UX : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.Integer.t)
    (UF : RocqOfOCaml.Basics.Unreachable
      (@MonadVM.Ec.Bls12_381.F_p.t UZ UN UB))
    (UA : RocqOfOCaml.Basics.Unreachable
      (RocqOfOCaml.OCamlIarray.t
        (@MonadVM.Ec.Bls12_381.F_p.t UZ UN UB))) :
  @MonadVM.Ec.Bls12_381.F_p_SWU_curve.x_num UZ UN UB UA UX UF =
    map parsed_bls_field_literal
      (firstn 12 (skipn 2 bls_map_hex_literals)).
Proof. vm_compute. reflexivity. Qed.

Print Assumptions generated_g1_x_num_matches_literals.

Lemma generated_g1_x_den_matches_literals
    (UZ : RocqOfOCaml.Basics.Unreachable Z.t)
    (UN : RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t)
    (UB : RocqOfOCaml.Basics.Unreachable
      MonadVM.Numeric.IntegerBase.(MonadVM.Numeric.Make.Make_result.t))
    (UX : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.Integer.t)
    (UF : RocqOfOCaml.Basics.Unreachable
      (@MonadVM.Ec.Bls12_381.F_p.t UZ UN UB))
    (UA : RocqOfOCaml.Basics.Unreachable
      (RocqOfOCaml.OCamlIarray.t
        (@MonadVM.Ec.Bls12_381.F_p.t UZ UN UB))) :
  @MonadVM.Ec.Bls12_381.F_p_SWU_curve.x_den UZ UN UB UA UX UF =
    map parsed_bls_field_literal
      (firstn 10 (skipn 14 bls_map_hex_literals) ++ ["1"]).
Proof. vm_compute. reflexivity. Qed.

Lemma generated_g1_y_num_matches_literals
    (UZ : RocqOfOCaml.Basics.Unreachable Z.t)
    (UN : RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t)
    (UB : RocqOfOCaml.Basics.Unreachable
      MonadVM.Numeric.IntegerBase.(MonadVM.Numeric.Make.Make_result.t))
    (UX : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.Integer.t)
    (UF : RocqOfOCaml.Basics.Unreachable
      (@MonadVM.Ec.Bls12_381.F_p.t UZ UN UB))
    (UA : RocqOfOCaml.Basics.Unreachable
      (RocqOfOCaml.OCamlIarray.t
        (@MonadVM.Ec.Bls12_381.F_p.t UZ UN UB))) :
  @MonadVM.Ec.Bls12_381.F_p_SWU_curve.y_num UZ UN UB UA UX UF =
    map parsed_bls_field_literal
      (firstn 16 (skipn 24 bls_map_hex_literals)).
Proof. vm_compute. reflexivity. Qed.

Lemma generated_g1_y_den_matches_literals
    (UZ : RocqOfOCaml.Basics.Unreachable Z.t)
    (UN : RocqOfOCaml.Basics.Unreachable MonadVM.Support.UintN.t)
    (UB : RocqOfOCaml.Basics.Unreachable
      MonadVM.Numeric.IntegerBase.(MonadVM.Numeric.Make.Make_result.t))
    (UX : RocqOfOCaml.Basics.Unreachable MonadVM.Numeric.Integer.t)
    (UF : RocqOfOCaml.Basics.Unreachable
      (@MonadVM.Ec.Bls12_381.F_p.t UZ UN UB))
    (UA : RocqOfOCaml.Basics.Unreachable
      (RocqOfOCaml.OCamlIarray.t
        (@MonadVM.Ec.Bls12_381.F_p.t UZ UN UB))) :
  @MonadVM.Ec.Bls12_381.F_p_SWU_curve.y_den UZ UN UB UA UX UF =
    map parsed_bls_field_literal
      (firstn 15 (skipn 40 bls_map_hex_literals) ++ ["1"]).
Proof. vm_compute. reflexivity. Qed.

Print Assumptions generated_g1_x_den_matches_literals.
Print Assumptions generated_g1_y_num_matches_literals.
Print Assumptions generated_g1_y_den_matches_literals.
