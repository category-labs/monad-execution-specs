Require Import RocqOfOCaml.RocqOfOCaml.
Require Import RocqOfOCaml.OCamlIarray.
Require Import RocqOfOCaml.OCamlInt64.

Import ListNotations.
Local Open Scope Z_scope.

(** Pure model of the imperative [Crypto.blake2f] implementation.  Mutable
    OCaml arrays are represented by immutable lists threaded through each
    assignment.  [rounds_nat] executes exactly [max rounds 0] rounds, matching
    the source loop [for i = 0 to rounds - 1]. *)

Definition word := OCamlInt64.t.
Definition words := list word.

(** The exceptional branches in the list-based array model require a fallback
    [words] value.  This instance is constructive: unlike an arbitrary result
    type, [words] is inhabited by the empty list. *)
#[global] Instance unreachable_words : Unreachable words :=
  {| unreachable := [] |}.

(** Signed 64-bit representations of the IV used by [Crypto.blake2b_iv]. *)
Definition iv : words :=
  [ 7640891576956012808;
    -4942790177534073029;
    4354685564936845355;
    -6534734903238641935;
    5840696475078001361;
    -7276294671716946913;
    2270897969802886507;
    6620516959819538809 ].

Definition sigma : list (list int) :=
  [ [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15];
    [14; 10; 4; 8; 9; 15; 13; 6; 1; 12; 0; 2; 11; 7; 5; 3];
    [11; 8; 12; 0; 5; 2; 15; 13; 10; 14; 3; 6; 7; 1; 9; 4];
    [7; 9; 3; 1; 13; 12; 11; 14; 2; 6; 5; 10; 4; 0; 15; 8];
    [9; 0; 5; 7; 2; 4; 10; 15; 14; 1; 11; 12; 6; 8; 3; 13];
    [2; 12; 6; 10; 0; 11; 8; 3; 4; 13; 7; 5; 15; 14; 1; 9];
    [12; 5; 1; 15; 14; 13; 4; 10; 0; 7; 6; 3; 9; 2; 8; 11];
    [13; 11; 7; 14; 12; 1; 3; 9; 5; 0; 15; 4; 8; 6; 2; 10];
    [6; 15; 14; 9; 11; 3; 0; 8; 12; 2; 13; 7; 1; 4; 10; 5];
    [10; 2; 8; 4; 7; 6; 1; 5; 15; 11; 9; 14; 3; 12; 13; 0] ].

Definition get {A : Set} `{Unreachable A} (values : list A) (index : int) : A :=
  OCamlIarray.get values index.

Fixpoint set_nat {A : Set} (values : list A) (index : nat) (value : A)
    : option (list A) :=
  match values, index with
  | [], _ => None
  | _ :: values, O => Some (value :: values)
  | head :: values, S index =>
      match set_nat values index value with
      | Some values => Some (head :: values)
      | None => None
      end
  end.

Definition set {A : Set} `{Unreachable (list A)}
    (values : list A) (index : int) (value : A) : list A :=
  if Z.ltb index 0 then unreachable
  else
    match set_nat values (Z.to_nat index) value with
    | Some values => values
    | None => unreachable
    end.

Definition rotr64 (value : word) (count : int) : word :=
  OCamlInt64.logor
    (OCamlInt64.shift_right_logical value count)
    (OCamlInt64.shift_left value (64 - count)).

Definition g `{Unreachable word} `{Unreachable words}
    (a b c d : int) (x y : word) (state : words) : words :=
  let state := set state a (OCamlInt64.add (OCamlInt64.add (get state a) (get state b)) x) in
  let state := set state d (rotr64 (OCamlInt64.logxor (get state d) (get state a)) 32) in
  let state := set state c (OCamlInt64.add (get state c) (get state d)) in
  let state := set state b (rotr64 (OCamlInt64.logxor (get state b) (get state c)) 24) in
  let state := set state a (OCamlInt64.add (OCamlInt64.add (get state a) (get state b)) y) in
  let state := set state d (rotr64 (OCamlInt64.logxor (get state d) (get state a)) 16) in
  let state := set state c (OCamlInt64.add (get state c) (get state d)) in
  set state b (rotr64 (OCamlInt64.logxor (get state b) (get state c)) 63).

Definition round `{Unreachable word} `{Unreachable words}
    (message schedule state : words) : words :=
  let mix state a b c d x y :=
    g a b c d (get message (get schedule x)) (get message (get schedule y)) state in
  let state := mix state 0 4 8 12 0 1 in
  let state := mix state 1 5 9 13 2 3 in
  let state := mix state 2 6 10 14 4 5 in
  let state := mix state 3 7 11 15 6 7 in
  let state := mix state 0 5 10 15 8 9 in
  let state := mix state 1 6 11 12 10 11 in
  let state := mix state 2 7 8 13 12 13 in
  mix state 3 4 9 14 14 15.

Fixpoint rounds_nat `{Unreachable word} `{Unreachable words}
    (remaining index : nat) (message state : words) : words :=
  match remaining with
  | O => state
  | S remaining =>
      let schedule := get sigma (Z.of_nat (index mod 10)) in
      rounds_nat remaining (S index) message (round message schedule state)
  end.

Fixpoint output_nat `{Unreachable word}
    (remaining index : nat) (hash state : words) : words :=
  match remaining with
  | O => []
  | S remaining =>
      let i := Z.of_nat index in
      OCamlInt64.logxor
        (OCamlInt64.logxor (get hash i) (get state i))
        (get state (i + 8))
      :: output_nat remaining (S index) hash state
  end.

Definition blake2f `{Unreachable word} `{Unreachable words}
    (rounds : int) (hash message : words) (t0 t1 : word)
    (final_block : bool) : words :=
  let state := hash ++ iv in
  let state := set state 12 (OCamlInt64.logxor (get state 12) t0) in
  let state := set state 13 (OCamlInt64.logxor (get state 13) t1) in
  let state :=
    if final_block then set state 14 (OCamlInt64.lognot (get state 14))
    else state in
  let state := rounds_nat (Z.to_nat rounds) O message state in
  output_nat 8 O hash state.
