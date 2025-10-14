open Utils
open QCheck2

let modulus = Z.(shift_left one 256)

let () =
  let open Alcotest in
  run "Unit tests on Word"
    [ ( "Round-trip Z"
      , [ check_prop ~print:Print.word ~name:"w = of_z (to_z_signed w)" Gen.word (fun w ->
              Word.(of_z (to_z_signed w) = w) )
        ; check_prop ~print:Print.word ~name:"w = of_z (to_z_unsigned w)" Gen.word (fun w ->
              Word.(of_z (to_z_unsigned w) = w) )
        ; check_prop ~print:Print.z ~name:"(in unsigned range) x = to_z_unsigned (of_z x)" Gen.z (fun x ->
              assume (Word.is_representable_unsigned x) ;
              Word.(to_z_unsigned (of_z x)) = x )
        ; check_prop ~print:Print.z ~name:"(in signed range) x = to_z_signed (of_z x)" Gen.z (fun x ->
              assume (Word.is_representable_signed x) ;
              Word.(to_z_signed (of_z x)) = x )
        ; check_prop ~print:Print.z ~name:"(positive) x -> to_z_unsigned (of_z x)" Gen.z (fun x ->
              assume Z.(x >= zero) ;
              Word.(to_z_unsigned (of_z x)) = Z.(rem x modulus) ) ] ) ]
