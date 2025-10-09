open Utils

module Impl : sig
  type t

  val max_unsigned : t
  val max_signed : t

  val of_z : Z.t -> t

  val to_z_unsigned : t -> Z.t
  val to_z_signed : t -> Z.t
end = struct
  type t = Z.t

  let max_unsigned = Z.(shift_left one 256 - one)
  let max_signed = Z.(shift_left one 255 - one)

  let of_z (x : Z.t) = Z.extract x 0 32

  let to_z_unsigned x = x
  let to_z_signed x =
    Z.(
      assert (leq x max_unsigned) ;
      if gt x max_signed then max_unsigned + one - x else x )
end

include Impl

let zero = of_z Z.zero
let one = of_z Z.one

let reverse (bs : Bytes.t) : Bytes.t =
  let l = Bytes.length bs in
  Bytes.init l (fun i -> bs.[l - i - 1])

let of_bytes_be (bs : Bytes.t) =
  (* Do not truncate silently *)
  if Bytes.length bs > 32 then raise Internal_error else of_z (Z.of_bits (reverse bs))
let to_bytes32_be (x : t) =
  let be_bytes = reverse (Z.to_bits (to_z_unsigned x)) in
  let len = Bytes.length be_bytes in
  assert (len <= 32) ;
  let padding = Bytes.init (32 - len) (fun _ -> '\x00') in
  padding ^ be_bytes

let byte i x = (Z.to_bits (to_z_unsigned x)).[i]

let of_string s = of_z (Z.of_string s)
let to_string x = Z.to_string (to_z_unsigned x)

let of_bool b = if b then one else zero

let of_byte c = of_z (Z.of_int (Char.code c))

let of_int i = of_z (Z.of_int i)
let to_int x = Z.to_int (to_z_unsigned x)
let to_int_opt x =
  let x = to_z_unsigned x in
  if Z.fits_int x then Some (Z.to_int x) else None

let ( ~$ ) = of_int
let of_uint64 i = of_z (Z.of_int64_unsigned i)
let to_uint64 x = Z.to_int64_unsigned (to_z_unsigned x)

let compare (x : t) (y : t) = Z.compare (to_z_unsigned x) (to_z_unsigned y)

let compare_signed (x : t) (y : t) = Z.compare (to_z_signed x) (to_z_signed y)

let equal x y = Z.equal (to_z_unsigned x) (to_z_unsigned y)
let hash x = Z.hash (to_z_unsigned x)

let lift_1 f x = of_z (f (to_z_unsigned x))
let lift_2 f x y = of_z (f (to_z_unsigned x) (to_z_unsigned y))

let logand = lift_2 Z.logand
let logor = lift_2 Z.logor
let logxor = lift_2 Z.logxor
let lognot = lift_1 Z.lognot

let ( + ) = lift_2 Z.( + )
let ( - ) = lift_2 Z.( - )
let ( * ) = lift_2 Z.( * )
let ( / ) = lift_2 Z.( / )

let div_signed _x _y = todo ()

let byte_width (x : t) = Z.numbits (to_z_unsigned x)

let shift_left x shift =  of_z (Z.shift_left (to_z_unsigned x) shift)

(* Zarith's shift right is arithmetic, however to_z_unsigned always results in a positive number *)
let shift_right x shift = of_z (Z.shift_right (to_z_unsigned x) shift)
let shift_right_arith x shift = of_z (Z.shift_right (to_z_signed x) shift)

(* Comparisons, Map, Set *)
include Comparable.Make (struct
  type t_outer = t
  type t = t_outer
  let compare = compare
end)

let is_zero x = x = zero

module Hashtbl = Hashtbl.Make (struct
  type t_outer = t
  type t = t_outer
  let hash = hash
  let equal = equal
end)

let modulo = lift_2 Z.rem

let modulo_signed _x _y = todo ()

let addmod x y m = of_z Z.(rem (to_z_unsigned x + to_z_unsigned y) (to_z_unsigned m))
let mulmod x y m = of_z Z.(rem (to_z_unsigned x * to_z_unsigned y) (to_z_unsigned m))

let ( ** ) base exp = of_z (Z.pow (to_z_unsigned base) exp)

let exp _x _y = todo ()
let sign_extend _i _x = todo ()

let signed_compare x y = Z.compare (to_z_signed x) (to_z_signed y)

let is_negative x = Stdlib.(signed_compare x zero = -1)

let incr x = x + ~$1
