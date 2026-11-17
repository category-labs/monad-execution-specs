open Monad_lib
open Byte_string
open Test_utils.Utils
open QCheck2
open Contract.Type

(* Types implemented as GADTs. *)

type 'a tuple_descr = Nil : unit tuple_descr | Cons : 'a descr * 'b tuple_descr -> ('a * 'b) tuple_descr

and 'a descr =
  | Tuple : 'a tuple_descr -> 'a descr
  | Fixed_bytes : {byte_width : int; alignment : alignment} -> Bytes.t descr
  | Bytes : Bytes.t descr
  | Array : 'a descr -> 'a list descr
  | Packed : 'a descr -> 'a descr

let rec type_of : type a. a descr -> a typ = function
  | Tuple tup -> tuple (tuple_of tup)
  | Fixed_bytes {byte_width; alignment} ->
      let module M = struct
        type t = Bytes.t
        let byte_width = byte_width
        let of_bytes_exn bs = bs
        let to_bytes bs = bs
      end in
      fixed_bytes (module M) alignment
  | Bytes -> bytes
  | Array elt -> array (type_of elt)
  | Packed elt -> packed (type_of elt)

and tuple_of : type a. a tuple_descr -> a tup = function
  | Nil -> nil
  | Cons (ty, tys) -> type_of ty @: tuple_of tys

type e_typ = Pack_typ : 'a descr -> e_typ
type e_tup = Pack_tup : 'a tuple_descr -> e_tup
type e_val = Pack_val : 'a descr * 'a -> e_val

let rec equal : type a. a descr -> a -> a -> bool = function
  | Tuple tys -> equal_tup tys
  | Fixed_bytes _ -> Bytes.equal
  | Bytes -> Bytes.equal
  | Array elt_typ -> List.equal (equal elt_typ)
  | Packed elt_typ -> equal elt_typ

and equal_tup : type a. a tuple_descr -> a -> a -> bool = function
  | Nil -> fun () () -> true
  | Cons (typ, tys) -> fun (x, xs) (y, ys) -> equal typ x y && equal_tup tys xs ys

let gen_typ ~static : e_typ Gen.t =
  let open Gen in
  fix
    (fun (self : bool * int -> e_typ Gen.t) ((static, depth) : bool * int) : e_typ Gen.t ->
      if depth < 0 then failwith (Format.sprintf "Depth is %d" depth) ;
      let gen_tuple =
        let* len = tiny_nat in
        let rec loop (i : int) : e_tup Gen.t =
          if i = 0 then return (Pack_tup Nil)
          else
            let* (Pack_typ hd) = self (static, depth + 1) in
            let* (Pack_tup tl) = loop (i - 1) in
            return (Pack_tup (Cons (hd, tl)))
        in
        let* (Pack_tup tup) = loop len in
        return (Pack_typ (Tuple tup))
      in
      let gen_packed =
        let* (Pack_typ typ) = self (true, depth + 1) in
        return (Pack_typ (Packed typ))
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

let rec gen_val : type a. a descr -> a Gen.t =
  Gen.(
    function
    | Tuple Nil -> return ()
    | Tuple (Cons (typ, tys)) ->
        let* hd = gen_val typ in
        let* tl = gen_val (Tuple tys) in
        return (hd, tl)
    | Array typ -> list_size tiny_nat (gen_val typ)
    | Fixed_bytes {byte_width; _} -> string_size (return byte_width)
    | Bytes -> string ~nonempty:false
    | Packed elt -> gen_val elt )

let gen_e_val ~static : e_val Gen.t =
  Gen.(
    let* (Pack_typ typ) = gen_typ ~static in
    let* v = gen_val typ in
    return (Pack_val (typ, v)) )

let list_to_string (elt_to_string : 'a -> string) (elts : 'a list) : string =
  Format.sprintf "[%s]" (String.concat ", " (List.map elt_to_string elts))

let rec val_to_string : type a. a descr -> a -> string =
 fun typ ->
  match typ with
  | Tuple tup ->
      let rec loop : type b. b tuple_descr -> b -> string list =
       fun tup v ->
        match (tup, v) with Nil, () -> [] | Cons (typ, tys), (v, vs) -> val_to_string typ v :: loop tys vs
      in
      fun v -> Format.sprintf "[%s]" (String.concat ", " (loop tup v))
  | Array typ -> list_to_string (val_to_string typ)
  | Fixed_bytes _ -> fun v -> Format.sprintf "\"0x%s\"" (Bytes.to_hex_string v)
  | Bytes -> fun v -> Format.sprintf "\"0x%s\"" (Bytes.to_hex_string v)
  | Packed typ -> fun v -> Format.sprintf "packed(%s)" (val_to_string typ v)

let e_val_to_string (Pack_val (descr, v)) =
  Format.sprintf "%s : %s" (val_to_string descr v) (name (type_of descr))

let round_trip (Pack_val (descr, v)) =
  let typ = type_of descr in
  let encoded = Bytes.(concat empty (List.map B32.to_bytes (enc typ v))) in
  match dec_bytes typ encoded with Ok decoded -> equal descr v decoded | Error _ -> false

let () =
  let open Alcotest in
  run "Unit tests on Solidity-encoded data"
    [ ( "Round-trip encode-decode"
      , [ check_prop ~count:100_000 ~print:e_val_to_string ~name:"x = dec (enc x)" (gen_e_val ~static:false)
            round_trip ] ) ]
