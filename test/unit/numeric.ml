open Monad_lib.Numeric
open Test_utils.Utils
open QCheck2

let () =
  let open Alcotest in
  run "Unit tests on Word"
    [ (* Conversions *)
      ( "Round-trip Z"
      , [ check_prop ~print:Print.u256 ~name:"w = of_z (to_z_signed w)" Gen.u256 (fun w ->
              U256.(of_z_truncating (to_z w) = w) )
        ; check_prop ~print:Print.z ~name:"(in unsigned range) x = to_z_unsigned (of_z_truncating x)" Gen.z
            (fun x ->
              assume (U256.in_range x) ;
              U256.(to_z (of_z_truncating x)) = x ) ] )
    ; ( "Two's complement round-trip"
      , [ check_prop ~print:Print.u256 ~name:"x = as_unsigned (as_signed x)" Gen.u256 (fun x ->
              I256.as_unsigned (U256.as_signed x) = x )
        ; check_prop ~print:Print.i256 ~name:"x = as_signed (as_unsigned x)" Gen.i256 (fun x ->
              U256.as_signed (I256.as_unsigned x) = x ) ] )
    ; ( "Round-trip to repr"
      , [ check_prop ~print:Print.u256 ~name:"x = of_repr (to_repr x)" Gen.u256 (fun x ->
              x = U256.(of_repr (to_repr x)) ) ] )
      (* Operations *)
    ; ( "Byte extraction"
      , [ check_prop ~print:Print.u256 ~name:"x = ∑ (byte i x)" Gen.u256 (fun x ->
              let all_bytes : U256.t Seq.t =
                Seq.(
                  take 32 (ints 0)
                  |> map (fun i -> U256.(shift_left (of_byte (byte ~index_le:i x)) Stdlib.(8 * i))) )
              in
              x = Seq.fold_left U256.( + ) U256.zero all_bytes ) ] ) ]
