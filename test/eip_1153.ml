open Utils
open Alcotest

module Word = Monad_lib.Word

let key_0 = Program.Lit Word.zero
let key_1 = Program.Lit Word.one
let key_2 = Program.Lit Word.(of_int 2)
let key_3 = Program.Lit Word.(one ** 128)
let key_4 = Program.Lit Word.max_unsigned_t

let () =
  run "EIP-1153: Transient storage opcodes"
    [ ( "Unset values"
      , [ test_case "Slot 0" `Quick (test_program_pure ~push:[] Program.(tload key_0) ~pop:[Word.zero])
        ; test_case "Slot 1" `Quick (test_program_pure ~push:[] Program.(tload key_1) ~pop:[Word.zero])
        ; test_case "Slot 2" `Quick (test_program_pure ~push:[] Program.(tload key_2) ~pop:[Word.zero])
        ; test_case "Slot 2**128" `Quick (test_program_pure ~push:[] Program.(tload key_3) ~pop:[Word.zero])
        ; test_case "Slot 2**256-1" `Quick (test_program_pure ~push:[] Program.(tload key_4) ~pop:[Word.zero])
        ] )
    ; ( "TLOAD after TSTORE"
      , [ test_case "Slot 0" `Quick
            (test_program_pure ~push:[]
               Program.(
                 tstore key_0 key_0
                 @ tstore key_1 key_1
                 @ tstore key_2 key_2
                 @ tstore key_3 key_3
                 @ tstore key_4 key_4
                 @ tload key_0 )
               ~pop:[Word.zero] )
        ; test_case "Slot 1" `Quick
            (test_program_pure ~push:[]
               Program.(
                 tstore key_0 key_0
                 @ tstore key_1 key_1
                 @ tstore key_2 key_2
                 @ tstore key_3 key_3
                 @ tstore key_4 key_4
                 @ tload key_1 )
               ~pop:[Word.one] )
        ; test_case "Slot 2" `Quick
            (test_program_pure ~push:[]
               Program.(
                 tstore key_0 key_0
                 @ tstore key_1 key_1
                 @ tstore key_2 key_2
                 @ tstore key_3 key_3
                 @ tstore key_4 key_4
                 @ tload key_2 )
               ~pop:[Word.of_int 2] )
        ; test_case "Slot 2**128" `Quick
            (test_program_pure ~push:[]
               Program.(
                 tstore key_0 key_0
                 @ tstore key_1 key_1
                 @ tstore key_2 key_2
                 @ tstore key_3 key_3
                 @ tstore key_4 key_4
                 @ tload key_3 )
               ~pop:[Word.(one ** 128)] )
        ; test_case "Slot 2**256-1" `Quick
            (test_program_pure ~push:[]
               Program.(
                 tstore key_0 key_0
                 @ tstore key_1 key_1
                 @ tstore key_2 key_2
                 @ tstore key_3 key_3
                 @ tstore key_4 key_4
                 @ tload key_4 )
               ~pop:[Word.max_unsigned_t] ) ] )
    ; ( "TLOAD after SSTORE"
      (* Check that transient storage is distinct from storage *)
      , [ test_case "Slot 0" `Quick
            (test_program_pure ~push:[]
               Program.(
                 sstore key_0 key_0
                 @ sstore key_1 key_1
                 @ sstore key_2 key_2
                 @ sstore key_3 key_3
                 @ sstore key_4 key_4
                 @ tload key_0 )
               ~pop:[Word.zero] )
        ; test_case "Slot 1" `Quick
            (test_program_pure ~push:[]
               Program.(
                 sstore key_0 key_0
                 @ sstore key_1 key_1
                 @ sstore key_2 key_2
                 @ sstore key_3 key_3
                 @ sstore key_4 key_4
                 @ tload key_1 )
               ~pop:[Word.zero] )
        ; test_case "Slot 2" `Quick
            (test_program_pure ~push:[]
               Program.(
                 sstore key_0 key_0
                 @ sstore key_1 key_1
                 @ sstore key_2 key_2
                 @ sstore key_3 key_3
                 @ sstore key_4 key_4
                 @ tload key_2 )
               ~pop:[Word.zero] )
        ; test_case "Slot 2**128" `Quick
            (test_program_pure ~push:[]
               Program.(
                 sstore key_0 key_0
                 @ sstore key_1 key_1
                 @ sstore key_2 key_2
                 @ sstore key_3 key_3
                 @ sstore key_4 key_4
                 @ tload key_3 )
               ~pop:[Word.zero] )
        ; test_case "Slot 2**256-1" `Quick
            (test_program_pure ~push:[]
               Program.(
                 sstore key_0 key_0
                 @ sstore key_1 key_1
                 @ sstore key_2 key_2
                 @ sstore key_3 key_3
                 @ sstore key_4 key_4
                 @ tload key_4 )
               ~pop:[Word.zero] ) ] )
    ; ("TLOAD after TSTORE is zero", []) ]
