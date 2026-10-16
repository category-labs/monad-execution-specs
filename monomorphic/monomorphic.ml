(** Shadows the polymorphic comparison functions of [Stdlib] with versions specialised to [int].

    This module is opened in every module of [monad_lib] via [-open Monomorphic]. Any [=], [compare], [min],
    etc. on a type other than [int] is a type error.

    Shadow [Stdlib] itself too so [Stdlib.( ... )] and [open Stdlib] do not include the polymorphic versions. *)

module Int_comparisons = struct
  let ( = ) : int -> int -> bool = Int.equal
  let ( <> ) (x : int) (y : int) : bool = not (Int.equal x y)
  let ( == ) : int -> int -> bool = Int.equal
  let ( != ) (x : int) (y : int) : bool = not (Int.equal x y)
  let ( < ) (x : int) (y : int) : bool = Stdlib.( < ) x y
  let ( <= ) (x : int) (y : int) : bool = Stdlib.( <= ) x y
  let ( > ) (x : int) (y : int) : bool = Stdlib.( > ) x y
  let ( >= ) (x : int) (y : int) : bool = Stdlib.( >= ) x y
  let compare : int -> int -> int = Int.compare
  let min : int -> int -> int = Int.min
  let max : int -> int -> int = Int.max
end

module Stdlib = struct
  include Stdlib
  include Int_comparisons
end

include Int_comparisons
