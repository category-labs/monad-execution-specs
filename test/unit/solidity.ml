open Monad_lib
open Byte_string
open Test_utils.Utils
open QCheck2
module Codec = Contract.Type
open Abi_reference

type e_typ = Pack_typ : 'a typ -> e_typ
type e_tup = Pack_tup : 'a Tuple.t tup -> e_tup
type e_val = Pack_val : 'a typ * 'a -> e_val

let gen_typ ~static : e_typ Gen.t =
  let open Gen in
  fix
    (fun (self : bool * int -> e_typ Gen.t) ((static, depth) : bool * int) : e_typ Gen.t ->
      if depth < 0 then failwith (Format.sprintf "Depth is %d" depth) ;
      let gen_tuple =
        let* len = tiny_nat in
        let rec loop (i : int) : e_tup Gen.t =
          if i = 0 then return (Pack_tup [])
          else
            let* (Pack_typ hd) = self (static, depth + 1) in
            let* (Pack_tup tl) = loop (i - 1) in
            return (Pack_tup (hd :: tl))
        in
        let* (Pack_tup tup) = loop len in
        return (Pack_typ (Tuple tup))
      in
      let gen_packed =
        let* (Pack_typ typ) = self (true, depth + 1) in
        return (Pack_typ (Packed.t typ))
      in
      let gen_fixed_bytes =
        let* byte_width = small_nat in
        let* alignment = frequency [(1, return Left); (1, return Right)] in
        return (Pack_typ (Fixed_bytes {alignment; byte_width}))
      in
      let gen_bytes = return (Pack_typ Bytes) in
      let gen_array =
        let* (Pack_typ typ) = self (static, depth + 1) in
        return (Pack_typ (Array typ))
      in
      if depth > 1 then if static then gen_fixed_bytes else frequency [(1, gen_fixed_bytes); (1, gen_bytes)]
      else if static then frequency [(3 + (2 * depth), gen_fixed_bytes); (1, gen_tuple)]
      else
        frequency
          [ (1 + (2 * depth), gen_fixed_bytes)
          ; (1 + (2 * depth), gen_bytes)
          ; (2, gen_packed)
          ; (2, gen_tuple)
          ; (2, gen_array) ] )
    (static, 0)

let rec gen_val : type a. a typ -> a Gen.t =
  Gen.(
    function
    | Tuple [] -> return Tuple.[]
    | Tuple (typ :: tys) ->
        let* hd = gen_val typ in
        let* tl = gen_val (Tuple tys) in
        return Tuple.(hd :: tl)
    | Array typ -> list_size tiny_nat (gen_val typ)
    | Fixed_bytes {byte_width; _} -> string_size (return byte_width)
    | Bytes -> string ~nonempty:false
    | Map {repr; decode; _} ->
        let* repr = gen_val repr in
        return (Result.get_ok (decode repr)) )

let gen_e_val ~static : e_val Gen.t =
  Gen.(
    let* (Pack_typ typ) = gen_typ ~static in
    let* v = gen_val typ in
    return (Pack_val (typ, v)) )

let list_to_string (elt_to_string : 'a -> string) (elts : 'a list) : string =
  Format.sprintf "[%s]" (String.concat ", " (List.map elt_to_string elts))

let rec val_to_string : type a. a typ -> a -> string =
 fun typ ->
  match typ with
  | Tuple tup ->
      let rec loop : type b. b tup -> b -> string list =
       fun tup v ->
        match (tup, v) with [], [] -> [] | typ :: tys, v :: vs -> val_to_string typ v :: loop tys vs
      in
      fun v -> Format.sprintf "[%s]" (String.concat ", " (loop tup v))
  | Array typ -> list_to_string (val_to_string typ)
  | Fixed_bytes _ -> fun v -> Format.sprintf "\"0x%s\"" (Bytes.to_hex_string v)
  | Bytes -> fun v -> Format.sprintf "\"0x%s\"" (Bytes.to_hex_string v)
  | Map m -> fun v -> val_to_string m.repr (m.encode v)

let e_val_to_string (Pack_val (typ, v)) = Format.sprintf "%s : %s" (val_to_string typ v) (type_name typ)

(* Interpret the frozen descriptor into the new codec API, preserving the
   original OCaml value type only inside this test oracle. *)
let rec codec : type a. a typ -> a Codec.typ = function
  | Tuple tup -> Codec.tuple (tuple_codec tup)
  | Fixed_bytes {alignment; byte_width} ->
      Codec.fixed_bytes
        {alignment = (match alignment with Left -> Codec.Left | Right -> Codec.Right); byte_width}
  | Bytes -> Codec.bytes
  | Array typ -> Codec.array (codec typ)
  | Map m -> Codec.mapped {name = m.name; repr = codec m.repr; encode = m.encode; decode = m.decode}

and tuple_codec : type a. a tup -> a Codec.tup = function
  | [] -> Codec.map_tuple ~encode:(fun Tuple.[] -> ()) ~decode:(fun () -> Tuple.[]) Codec.tup0
  | hd :: tl ->
      Codec.map_tuple
        ~encode:(fun Tuple.(v :: vs) -> (v, vs))
        ~decode:(fun (v, vs) -> Tuple.(v :: vs))
        (Codec.cons (codec hd) (tuple_codec tl))

let old_error = function
  | Input_too_short -> `Short
  | Input_too_long -> `Long
  | Length_overflow -> `Overflow
  | Map_error {name; message} -> `Map (name, message)
let new_error = function
  | Codec.Input_too_short -> `Short
  | Codec.Input_too_long -> `Long
  | Codec.Length_overflow -> `Overflow
  | Codec.Map_error {name; message} -> `Map (name, message)
let same_result old fresh = Result.map_error old_error old = Result.map_error new_error fresh

let round_trip (Pack_val (typ, v)) =
  let fresh = codec typ in
  let encoded = enc_bytes typ v in
  let fresh_encoded = Codec.enc_bytes fresh v in
  let old = dec_bytes typ encoded in
  let decoded = Codec.dec_bytes fresh encoded in
  let same_layout =
    match (kind typ, Codec.kind fresh) with
    | Static a, Codec.Static b -> a.word_width = b.word_width
    | Dynamic, Codec.Dynamic -> true
    | _ -> false
  in
  same_layout
  && type_name typ = Codec.type_name fresh
  && encoded = fresh_encoded
  && old = Ok v
  && same_result old decoded
  && same_result (dec_bytes typ (encoded ^ "x")) (Codec.dec_bytes fresh (encoded ^ "x"))
  && same_result
       (dec_bytes ~allow_trailing:true typ (encoded ^ "x"))
       (Codec.dec_bytes ~allow_trailing:true fresh (encoded ^ "x"))
  && ( String.length encoded = 0
     ||
     let truncated = String.sub encoded 0 (String.length encoded - 1) in
     same_result (dec_bytes typ truncated) (Codec.dec_bytes fresh truncated) )

let check_same_decode typ input =
  Alcotest.(check bool)
    "same value or exact decode error" true
    (same_result (dec_bytes typ input) (Codec.dec_bytes (codec typ) input))

let word n = Numeric.U256.(to_repr ~$n) |> B32.to_bytes

let test_boundaries () =
  List.iter
    (fun width ->
      List.iter
        (fun alignment ->
          let fixed = Fixed_bytes {alignment; byte_width = width} in
          let typ = Tuple [fixed; Bytes; Array fixed] in
          let v = String.make width 'a' in
          let value = Tuple.[v; "dynamic"; List.[v; v]] in
          Alcotest.(check bool) "word boundary" true (round_trip (Pack_val (typ, value))) ;
          let encoded = enc_bytes typ value in
          for n = 0 to String.length encoded do
            check_same_decode typ (String.sub encoded 0 n)
          done ;
          let packed = Packed.t (Tuple [fixed; fixed]) in
          Alcotest.(check bool) "packed word boundary" true (round_trip (Pack_val (packed, Tuple.[v; v]))) )
        [Left; Right] )
    [0; 1; 31; 32; 33; 63; 64; 65]

let test_tuple_offsets () =
  let typ = Tuple [Bytes; Bytes] in
  let encoded = enc_bytes typ Tuple.["abc"; "def"] in
  (* The existing ABI ignores in-range offsets, rather than seeking to them. *)
  let altered = word 0 ^ word 1 ^ String.sub encoded 64 (String.length encoded - 64) in
  Alcotest.(check bool)
    "original accepts altered offsets" true
    (dec_bytes typ altered = Ok Tuple.["abc"; "def"]) ;
  check_same_decode typ altered ;
  let overflow = String.make 32 '\255' ^ String.sub encoded 32 (String.length encoded - 32) in
  Alcotest.(check bool)
    "offset overflow remains an error" true
    (dec_bytes typ overflow = Error Length_overflow) ;
  check_same_decode typ overflow

let test_length_errors () =
  let samples : string list =
    [""; "x"; String.make 31 '\000'; word 1; word 33 ^ word 0; String.make 32 '\255']
  in
  List.iter (check_same_decode Bytes) samples ;
  List.iter (check_same_decode (Array U64.t)) samples

let test_mapping_errors () =
  let typ =
    Map
      { name = "nonzero"
      ; repr = U8.t
      ; encode = Fun.id
      ; decode = (fun n -> if Numeric.U8.(n = zero) then Error "zero is invalid" else Ok n) }
  in
  let zero = word 0 in
  Alcotest.(check bool)
    "mapped error retains name and message" true
    (dec_bytes typ zero = Error (Map_error {name = "nonzero"; message = "zero is invalid"})) ;
  check_same_decode typ zero ;
  check_same_decode (Packed.t typ) zero ;
  check_same_decode (Map {name = "outer"; repr = typ; encode = Fun.id; decode = (fun n -> Ok n)}) zero

let test_padding_and_bool () =
  let dirty = String.make 32 '\255' in
  check_same_decode (Fixed_bytes {alignment = Left; byte_width = 1}) dirty ;
  check_same_decode (Fixed_bytes {alignment = Right; byte_width = 1}) dirty ;
  List.iter (fun n -> check_same_decode bool (word n)) [0; 1; 2; 255] ;
  List.iter (fun n -> check_same_decode U64.t_option (word n)) [0; 1; 255]

let test_packed_failure () =
  let failure f =
    try
      ignore (f ()) ;
      None
    with Failure message -> Some message
  in
  Alcotest.(check (option string))
    "packing dynamic bytes still fails"
    (failure (fun () -> Packed.t Bytes))
    (failure (fun () -> Codec.Packed.t Codec.bytes)) ;
  Alcotest.(check (option string))
    "packing a dynamic tuple still fails"
    (failure (fun () -> Packed.t (Tuple [U64.t; Bytes])))
    (failure (fun () -> Codec.Packed.t (Codec.tuple (Codec.tup2 (Codec.U64.t, Codec.bytes)))))

let test_flat_tuple_and_topics () =
  let old_types = [U64.t; Address.t] in
  let fresh_types = Codec.tup2 (Codec.U64.t, Codec.Address.t) in
  let n = Numeric.U64.of_int 17 and a = Chain.Ethereum.Address.zero in
  Alcotest.(check string)
    "flat tuple encoding"
    (enc_bytes (Tuple old_types) Tuple.[n; a])
    (Codec.enc_bytes (Codec.tuple fresh_types) (n, a)) ;
  Alcotest.(check (list string))
    "canonical names" ["uint64"; "address"]
    (Codec.tuple_to_canonical_type_names fresh_types) ;
  Alcotest.(check (list string))
    "indexed topics"
    (List.map B32.to_bytes (enc U64.t n @ enc Address.t a))
    (List.map B32.to_bytes (Codec.encode_indexed_parameters fresh_types (n, a))) ;
  let asserts f =
    try
      ignore (f ()) ;
      false
    with Assert_failure _ -> true
  in
  Alcotest.(check bool)
    "multiword indexed topic remains unsupported" true
    (asserts (fun () -> Codec.encode_indexed_parameters (Codec.tup1 Codec.bytes) "abc")) ;
  Alcotest.(check string)
    "nested tuple layout"
    (enc_bytes (Tuple [Tuple old_types; Bytes]) Tuple.[Tuple.[n; a]; "tail"])
    (Codec.enc_bytes (Codec.tuple (Codec.tup2 (Codec.tuple fresh_types, Codec.bytes))) ((n, a), "tail"))

let () =
  let open Alcotest in
  run "Unit tests on Solidity-encoded data"
    [ ( "Original versus typed codecs"
      , [ check_prop ~count:100_000 ~print:e_val_to_string
            ~name:"same layout, bytes, values and decoding errors" (gen_e_val ~static:false) round_trip ] )
    ; ( "ABI compatibility boundaries"
      , List.map
          (fun (name, test) -> test_case name `Quick test)
          [ ("word boundaries and every truncation", test_boundaries)
          ; ("ignored tuple offsets and overflow", test_tuple_offsets)
          ; ("length errors", test_length_errors)
          ; ("mapped decoding errors", test_mapping_errors)
          ; ("padding, bool and optional values", test_padding_and_bool)
          ; ("reject dynamic packed types", test_packed_failure)
          ; ("flat tuples, nested layout and indexed topics", test_flat_tuple_and_topics) ] ) ]
