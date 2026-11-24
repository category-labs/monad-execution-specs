(** Random choices for fuzzers, ported from the C++ [category/vm/fuzzing/choice.hpp]. *)

open Monad_lib
open Numeric

(* A uniformly random float in [0, 1). *)
let cutoff rng = Random.State.float rng 1.0

(** [discrete_choice rng ~default choices] runs the first of [choices] whose probability, added to the
    probabilities of the choices before it, reaches a uniformly random cutoff, or [default] if there is none. *)
let discrete_choice rng ~(default : unit -> 'a) (choices : (float * (unit -> 'a)) list) : 'a =
  let cutoff = cutoff rng in
  let rec pick cumulative = function
    | [] -> default ()
    | (probability, action) :: choices ->
        let cumulative = cumulative +. probability in
        if Float.compare cumulative cutoff >= 0 then action () else pick cumulative choices
  in
  pick 0.0 choices

(** [true] with probability [p]. *)
let with_probability rng p = Float.compare p (cutoff rng) >= 0

(** A uniformly random element of a non-empty list. *)
let sample rng (l : 'a list) : 'a = List.nth l (Random.State.int rng (List.length l))

(** [n] uniformly random bytes. *)
let bytes rng n = String.init n (fun _ -> Char.chr (Random.State.int rng 256))

let u64 rng = U64.of_z_exn (Z.of_bits (bytes rng 8))
let u256 rng = U256.of_z_exn (Z.of_bits (bytes rng 32))

(** A random number between [lower] and [upper] inclusive, biased towards [lower], [lower + 1], [upper - 1]
    and [upper]. *)
let bound_biased_u256 rng ~lower ~upper =
  assert (U256.(lower <= upper)) ;
  discrete_choice rng
    ~default:(fun () ->
      let x = u256 rng in
      (* Wraps around to zero when the range is the whole of U256. *)
      let m = U256.(upper - lower + one) in
      if U256.(m = zero) then x else U256.(lower + rem x m) )
    [ (0.05, fun () -> if U256.(lower = upper) then lower else U256.(lower + one))
    ; (0.05, fun () -> if U256.(lower = upper) then upper else U256.(upper - one))
    ; (0.05, fun () -> lower)
    ; (0.05, fun () -> upper) ]
