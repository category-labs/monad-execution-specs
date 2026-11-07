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
  | Map _ -> assert false

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
  | Input_too_short -> "short"
  | Input_too_long -> "long"
  | Length_overflow -> "overflow"
  | Map_error {name; message} -> name ^ ":" ^ message
let new_error = function
  | Codec.Input_too_short -> "short"
  | Codec.Input_too_long -> "long"
  | Codec.Length_overflow -> "overflow"
  | Codec.Map_error {name; message} -> name ^ ":" ^ message
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

let () =
  let open Alcotest in
  run "Unit tests on Solidity-encoded data"
    [ ( "Original versus typed codecs"
      , [ check_prop ~count:100_000 ~print:e_val_to_string
            ~name:"same layout, bytes, values and decoding errors" (gen_e_val ~static:false) round_trip ] ) ]
