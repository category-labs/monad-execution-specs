open Utils

module Impl : sig
  type t

  val zero : t
  val one : t
  val max_t : t

  val init : (int -> char) -> t

  val byte : int -> t -> char

  val of_string : string -> t
  val to_string : t -> string

  val of_bytes : Bytes.t -> t
  val to_bytes : t -> Bytes.t

  val of_byte : char -> t
  val ( .$() ) : t -> int -> char

  val to_z : t -> Z.t
  val of_z : Z.t -> t

  val of_int : int -> t
  val to_int : t -> int
  val to_int_opt : t -> int option
  val of_uint64 : Uint64.t -> t
  val to_uint64 : t -> Uint64.t

  val compare : t -> t -> int

  val equal : t -> t -> bool
  val hash : t -> int

  val logand : t -> t -> t
  val logor : t -> t -> t
  val logxor : t -> t -> t
  val lognot : t -> t

  val sign_bit : t -> bool

  val least_significant_byte : t -> t
  val byte_width : t -> int
end = struct
  type t = string

  let check (x : t) =
    assert (String.length x = 32) ;
    x

  let reverse (x : t) =
    ignore (check x) ;
    String.init 32 (fun i -> x.[31 - i])

  let max_unsigned_word_z = Z.(sub (shift_left one 256) one)

  let to_z (x : t) = Z.of_bits (reverse x)
  let of_z (x : Z.t) =
    let result =
      (* Unfortunately Z.to_bits gives the Big Endian representation of abs(x) so we may need to invert x in Z *)
      let x = if Z.(x >= zero) then x else Z.(sub max_unsigned_word_z x) in
      let repr = Z.to_bits x in
      let l = String.length repr in
      if l >= 32 then String.init 32 (fun i -> repr.[31 - i])
      else String.init 32 (fun i -> if 31 - i >= l then '\x00' else repr.[31 - i])
    in
    check result

  let zero = of_z Z.zero
  let one = of_z Z.one
  let max_t = String.init 32 (fun _ -> '\xff')

  let init fn = String.init 32 fn

  let byte i x = x.[i]

  let of_string s = of_z (Z.of_string s)
  let to_string x = Z.to_string (to_z x)

  let of_bytes s =
    let l = String.length s in
    (* Do not truncate silently *)
    if l > 32 then raise Internal_error;
    if l = 32 then s
    else (Bytes.init (32 - l) (fun _ -> '\x00')) ^ s

  let to_bytes x = x

  let of_byte c = String.init 32 (fun i -> if i = 31 then c else '\x00')
  let ( .$() ) x i = if i >= 32 then '\x00' else x.[31 - i]

  module Conversion (T : sig
    type t
    val logand : t -> t -> t
    val of_int : int -> t
    val to_int : t -> int
    val shift_right_logical : t -> int -> t
  end) =
  struct
    let byte i x = Char.chr (T.to_int (T.logand (T.shift_right_logical x (i * 8)) (T.of_int 0xff)))
    let of_t (x : T.t) : t = String.init 32 (fun i -> byte (31 - i) x)
  end

  let of_int =
    let module M = Conversion (struct
      include Int
      let to_int x = x
      let of_int x = x
    end) in
    M.of_t

  let of_uint64 =
    let module M = Conversion (Uint64) in
    M.of_t

  let to_int x = Z.to_int (to_z x)
  let to_int_opt (x : t) : int option =
    let x = to_z x in
    if Z.fits_int x then Some (Z.to_int x) else None
  let to_uint64 x = Z.to_int64_unsigned (to_z x)

  let compare (w1 : t) (w2 : t) =
    let s1 = String.to_seq w1 in
    let s2 = String.to_seq w2 in
    (* Compare the strings characterwise and keep the first non-zero *)
    Seq.map2 compare s1 s2
    |> Seq.drop_while (( = ) 0)
    |> Seq.uncons
    |> function None -> 0 | Some (d, _) -> d

  let equal = String.equal
  let hash = String.hash

  let bitwise f s1 s2 = String.init 32 (fun i -> Char.unsafe_chr (f (Char.code s1.[i]) (Char.code s2.[i])))

  let logand = bitwise Int.logand
  let logor = bitwise Int.logor
  let logxor = bitwise Int.logxor
  let lognot s = String.init 32 (fun i -> Char.unsafe_chr (Int.lognot (Char.code s.[i])))

  let sign_bit s = s.[0] > '\x7f'

  let least_significant_byte s = String.init 32 (fun i -> if i = 31 then s.[i] else '\x00')

  let byte_width (x : t) =
    let rec loop i =
      (* Invariant: x[0 .. i) = 0 *)
      if i >= 32 || x.[i] <> '\x00' then 32 - i else loop (i + 1)
    in
    loop 0
end

include Impl
include Comparable.Make (Impl)

module Map = struct
  include Map
  include Lens.DerivedMap (Map)
end

module Hashtbl = Hashtbl.Make (Impl)

let of_bool b = if b then one else zero

let lift_binop_z f x y = of_z (f (to_z x) (to_z y))

let ( + ) = lift_binop_z Z.( + )
let ( - ) = lift_binop_z Z.( - )
let ( * ) = lift_binop_z Z.( * )
let ( / ) = lift_binop_z Z.( / )

let div_signed _x _y = todo ()

let modulo = lift_binop_z Z.rem

let modulo_signed _x _y = todo ()

let addmod x y m = of_z Z.(rem (to_z x + to_z y) (to_z m))
let mulmod x y m = of_z Z.(rem (to_z x * to_z y) (to_z m))

let ( ** ) base exp = of_z (Z.pow (to_z base) exp)

let exp _x _y = todo ()
let sign_extend _i _x = todo ()

let signed_compare x y =
  let sgn_x = if sign_bit x then -1 else 1 in
  let sgn_y = if sign_bit y then -1 else 1 in
  if Stdlib.(sgn_x = sgn_y) then compare x y else Stdlib.(compare sgn_x sgn_y)

let ( ~$ ) = of_int

let incr x = x + ~$1
