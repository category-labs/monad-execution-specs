(** Monad definition and associated operators. *)

(** The signature of a module defining a monad. Note that this is a "thin" signature, defining only a type and
    bind and return operations. Additional operations are provided by the {!Monad.Make} functor.
 *)
module type SIG = sig
  type 'a t
  val return : 'a -> 'a t
  val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t
end

(** The signature of a module defining a parameterized monad. Additional operations are provided by the {!Monad.Make2}
    functor. *)
module type SIG2 = sig
  type ('a, 'k) t
  val return : 'a -> ('a, 'k) t
  val ( >>= ) : ('a, 'k) t -> ('a -> ('b, 'k) t) -> ('b, 'k) t
end

(* Alias to avoid shadowing SIG from child modules. *)
module type SIG_MONAD = SIG

(** Useful combinators for any monad. *)
module Make (M : SIG) = struct
  include M

  let ( let$ ) x f = M.(x >>= f)

  let fmap f x = M.(x >>= fun x -> return (f x))
  let ( <$> ) f x = fmap f x
  let ( <*> ) (f : ('a -> 'b) M.t) (x : 'a M.t) : 'b M.t =
    let$ f = f in
    let$ x = x in
    return (f x)

  let ( >> ) (mx : unit M.t) (y : 'a M.t) : 'a M.t = M.(mx >>= fun _ -> y)

  let when_ cond mx = if cond then mx else M.return ()

  module Option = struct
    include Option

    let iterM (x : 'a option) ~(f : 'a -> unit M.t) : unit M.t =
      match x with Some x -> f x | None -> M.return ()
  end

  module List = struct
    include List

    let rec sequence (l : 'a M.t list) : 'a list M.t =
      let open M in
      match l with
      | [] -> return []
      | mx :: mxs ->
          let$ x = mx in
          let$ xs = sequence mxs in
          return (x :: xs)

    let rec fold_leftM ~(f : 'acc -> 'a -> 'acc M.t) (acc : 'acc) (l : 'a list) : 'acc M.t =
      match l with
      | hd :: tl ->
          let$ acc = f acc hd in
          fold_leftM ~f acc tl
      | [] -> return acc

    let rec iterM ~(f : 'a -> unit M.t) (l : 'a list) : unit M.t =
      let open M in
      match l with
      | [] -> return ()
      | x :: xs ->
          let$ () = f x in
          iterM ~f xs

    let rec mapM ~(f : 'a -> 'b M.t) (l : 'a list) : 'b list M.t =
      match l with
      | [] -> M.return []
      | x :: xs ->
          M.(
            let$ x' = f x in
            let$ xs' = mapM ~f xs in
            return (x' :: xs') )
  end

  module Seq = struct
    include Seq

    let rec sequence (seq : 'a M.t Seq.t) : 'a Seq.t M.t =
      let open M in
      match Seq.uncons seq with
      | None -> return Seq.empty
      | Some (mx, mxs) ->
          let$ x = mx in
          let$ xs = sequence mxs in
          M.return (Seq.cons x xs)

    let mapM ~(f : 'a -> 'b M.t) (seq : 'a Seq.t) : 'b Seq.t M.t = sequence (map f seq)

    let rec fold_leftM ~(f : 'acc -> 'a -> 'acc M.t) (acc : 'acc) (seq : 'a t) : 'acc M.t =
      match Seq.uncons seq with
      | Some (hd, tl) ->
          let$ acc = f acc hd in
          fold_leftM ~f acc tl
      | None -> M.return acc

    let rec iterM ~(f : 'a -> unit M.t) (seq : 'a Seq.t) : unit M.t =
      let open M in
      match Seq.uncons seq with
      | None -> return ()
      | Some (x, xs) ->
          let$ () = f x in
          iterM ~f xs

    let rec foldM ~(f : 'acc -> 'x -> 'acc M.t) (acc : 'acc) (seq : 'a Seq.t) : 'acc M.t =
      let open M in
      match Seq.uncons seq with
      | None -> return acc
      | Some (x, xs) ->
          let$ acc = f acc x in
          foldM ~f acc xs

    include Seq
  end
end
[@@inline]

(* Alias to avoid shadowing Make from child modules. *)
module Make_Monad = Make

(** Useful combinators for any monad, parametric version. *)
module Make2 (M : SIG2) = struct
  include M

  let ( let$ ) x f = M.(x >>= f)

  let fmap f x = M.(x >>= fun x -> return (f x))
  let ( <$> ) f x = fmap f x
  let ( <*> ) f x =
    let$ f = f in
    let$ x = x in
    return (f x)

  let ( >> ) mx y = M.(mx >>= fun () -> y)

  let when_ cond mx = if cond then mx else M.return ()

  module Option = struct
    include Option

    let iterM (x : 'a option) ~f = match x with Some x -> f x | None -> M.return ()
  end

  module List = struct
    include List

    let rec sequence l =
      let open M in
      match l with
      | [] -> return []
      | mx :: mxs ->
          let$ x = mx in
          let$ xs = sequence mxs in
          return (x :: xs)

    let rec fold_leftM ~(f : 'acc -> 'a -> ('acc, 't) M.t) (acc : 'acc) (l : 'a list) : ('acc, 't) M.t =
      match l with
      | hd :: tl ->
          let$ acc = f acc hd in
          fold_leftM ~f acc tl
      | [] -> return acc

    let rec iterM ~f l =
      let open M in
      match l with
      | [] -> return ()
      | x :: xs ->
          let$ () = f x in
          iterM ~f xs

    let rec mapM ~f l =
      match l with
      | [] -> M.return []
      | x :: xs ->
          M.(
            let$ x' = f x in
            let$ xs' = mapM ~f xs in
            return (x' :: xs') )

    let rec filter_mapM ~f l =
      match l with
      | [] -> M.return []
      | x :: xs -> (
          M.(
            let$ x' = f x in
            match x' with
            | None -> filter_mapM ~f xs
            | Some x' ->
                let$ xs' = filter_mapM ~f xs in
                return (x' :: xs') ) )
  end

  module Seq = struct
    include Seq

    let rec sequence seq =
      let open M in
      match Seq.uncons seq with
      | None -> return Seq.empty
      | Some (mx, mxs) ->
          let$ x = mx in
          let$ xs = sequence mxs in
          M.return (Seq.cons x xs)

    let mapM ~f seq = sequence (map (fun x -> x >>= f) seq)

    let rec iterM ~f seq =
      let open M in
      match Seq.uncons seq with
      | None -> return ()
      | Some (x, xs) ->
          let$ () = f x in
          iterM ~f xs

    let rec foldM ~f (acc : 'acc) (seq : 'a Seq.t) =
      let open M in
      match Seq.uncons seq with
      | None -> return acc
      | Some (x, xs) ->
          let$ acc = f acc x in
          foldM ~f acc xs

    include Seq
  end
end
[@@inline]

(** A monad transformer is a module defining a monad, an inner monad [Inner], and a transformation
    [lift] which lifts a computation in the inner monad to the monad transformer *)
module type TRANS = sig
  include SIG
  module Inner : SIG
  val lift : 'a Inner.t -> 'a t
end

module Identity = struct
  module Impl = struct
    type 'a t = 'a
    let return x = x
    let ( >>= ) x f = f x
  end
  include Impl
  include Make (Impl)
end

module State (T : sig
  type t
end) =
struct
  module type SIG = sig
    include SIG
    type state = T.t
    val get : state t
    val put : state -> unit t
  end

  module Make (S : SIG) = struct
    include S
    include Make (S)
    type state = T.t
    let update (f : state -> state) : unit t = get >>= fun s -> put (f s)

    let ( := ) (l : (state, 'x) Lens.t) (x : 'x) =
      let$ state = get in
      put (l.set x state)

    let ( ! ) (l : (state, 'x) Lens.t) : 'x t =
      let$ state = get in
      return (l.get state)

    let update_field (l : (state, 'x) Lens.t) (f : 'x -> 'x) : unit t =
      let$ v = !l in
      l := f v
  end
  [@@inline]

  module Trans (Inner : SIG_MONAD) = struct
    module Inner = Make_Monad (Inner)

    include Make (struct
      type 'a t = T.t -> ('a * T.t) Inner.t
      let[@inline] return (x : 'a) : 'a t = fun s -> Inner.return (x, s)
      let[@inline] ( >>= ) (x : 'a t) (f : 'a -> 'b t) =
       fun s ->
        Inner.(
          let$ x, s = x s in
          f x s )

      type state = T.t
      let get : T.t t = fun s -> Inner.return (s, s)
      let put (s : T.t) : unit t = fun _ -> Inner.return ((), s)
    end)

    (* Specialize lens ops. *)
    let ( := ) (l : (state, 'x) Lens.t) (x : 'x) : unit t = fun state -> Inner.return ((), l.set x state)

    let ( ! ) (l : (state, 'x) Lens.t) : 'x t = fun state -> Inner.return (l.get state, state)

    let update_field (l : (state, 'x) Lens.t) (f : 'x -> 'x) : unit t =
     fun state -> Inner.return ((), l.set (f (l.get state)) state)

    let lower (x : state -> 'a * state) : 'a t = fun s -> Inner.return (x s)
    let lift (x : 'a Inner.t) : 'a t = fun s -> Inner.fmap (fun x -> (x, s)) x
  end
  [@@inline]

  module Lift (MT : TRANS) (M : SIG with type 'a t = 'a MT.Inner.t) = struct
    include Make (struct
      include MT
      type state = T.t
      let get : T.t MT.t = (MT.lift [@inlined]) M.get
      let put x = (MT.lift [@inlined]) (M.put x)
    end)
  end
  [@@inline]

  include Trans (Identity)
end
[@@inline]

module Result (T : sig
  type t
end) =
struct
  module type SIG = sig
    include SIG_MONAD
    type error = T.t
    val fail : error -> 'a t
  end

  module Make (S : SIG) = struct
    include S
    include Make_Monad (S)
    type error = T.t

    module Option = struct
      include Option

      let or_fail (err : error) = function None -> S.fail err | Some x -> S.return x
    end
  end
  [@@inline]

  module Lift (MT : TRANS) (M : SIG with type 'a t = 'a MT.Inner.t) : SIG = struct
    include Make (struct
      include MT
      type error = T.t
      let fail (x : T.t) : 'a MT.t = MT.lift (M.fail x)
    end)
  end
  [@@inline]

  module Trans (Inner : SIG_MONAD) = struct
    module Inner = Make_Monad (Inner)

    include Make (struct
      type 'a t = ('a, T.t) result Inner.t
      let return (x : 'a) : 'a t = Inner.return (Ok x)
      let ( >>= ) (x : 'a t) (f : 'a -> 'b t) =
        Inner.(x >>= function Error err -> Inner.return (Error err) | Ok x -> f x)

      type error = T.t
      let fail (err : T.t) = Inner.return (Error err)
    end)

    let lower (x : ('a, T.t) result) : 'a t = Inner.return x
    let lift (x : 'a Inner.t) : 'a t = Inner.fmap Stdlib.Result.ok x
  end
  [@@inline]

  include Trans (Identity)
end
[@@inline]

(** A monad that produces either a state change or an error. Note that this provides the capabilities of both
    State and Result but is not equal to their composition. *)
module StErr = struct
  module Make (T : sig
    type state
    type error
  end) =
  struct
    module Trans (Inner : SIG_MONAD) = struct
      module Impl = struct
        module Inner = Make_Monad (Inner)
        type 'a t = T.state -> ('a * T.state, T.error) Stdlib.Result.t Inner.t
        let return (x : 'a) : 'a t = fun s -> Inner.return (Ok (x, s))
        let ( >>= ) (x : 'a t) (f : 'a -> 'b t) =
         fun s -> Inner.(x s >>= function Error err -> Inner.return (Error err) | Ok (x, s') -> f x s')

        type state = T.state
        type error = T.error

        let fail (err : T.error) : 'a t = fun _s -> Inner.return (Error err)
        let get = fun s -> Inner.return (Ok (s, s))
        let put s' = fun _s -> Inner.return (Ok ((), s'))
      end

      module State = State (struct
        type t = T.state
      end)
      module Result = Result (struct
        type t = T.error
      end)
      include Impl
      include Make_Monad (Impl)
      include State.Make (Impl)
      include Result.Make (Impl)
    end

    include Trans (Identity)
  end
  [@@inline]
end

(* A classic (no Codensity) state+error monad. *)
module State_error = struct
  module Make (P : sig
    type state
    type error
  end) =
  struct
    module State = State (struct
      type t = P.state
    end)
    module Result = Result (struct
      type t = P.error
    end)
    module type SIG = sig
      include SIG
      include State.SIG with type 'a t := 'a t
      include Result.SIG with type 'a t := 'a t
    end

    module Make (S : SIG) = struct
      include S
      include Make (S)
      include State.Make (S)
      include Result.Make (S)
    end
    [@@inline]

    module Trans (Inner : SIG_MONAD) = struct
      module Inner = Make_Monad (Inner)

      include Make (struct
        include P
        type 'a t = state -> (('a, error) result * state) Inner.t
        let[@inline] return (v : 'a) state = (Inner.return [@inlined]) (Ok v, state)
        let[@inline] ( >>= ) (v : 'a t) (f : 'a -> 'b t) =
         fun state ->
          Inner.(
            let$ res, state = (v [@inlined]) state in
            match res with Error err -> (Inner.return [@inlined]) (Error err, state) | Ok v -> f v state )

        let get : state t = fun state -> Inner.return (Ok state, state)
        let put (state' : state) = fun _state -> Inner.return (Ok (), state')

        let fail (err : error) = fun state -> Inner.return (Error err, state)
      end)

      (* Specialized lens stuff, faster. *)
      let[@inline] ( := ) (l : (state, 'x) Lens.t) (x : 'x) =
       fun state ->
        let state = l.set x state in
        Inner.return (Ok (), state)
      let[@inline] ( ! ) (l : (state, 'x) Lens.t) = fun state -> Inner.return (Ok (l.get state), state)
      let[@inline] update_field (l : (state, 'x) Lens.t) (f : 'x -> 'x) =
       fun state -> Inner.return (Ok (), l.set (f (l.get state)) state)

      let[@inline] lower (x : state -> ('a, error) result * state) : 'a t = fun s -> Inner.return (x s)
      let[@inline] lift (x : 'a Inner.t) : 'a t = fun s -> Inner.fmap (fun x -> (Ok x, s)) x
    end
    [@@inline]

    module Lift (MT : TRANS) (M : SIG with type 'a t = 'a MT.Inner.t) = Make (struct
      include MT
      include P
      let get = (MT.lift [@inlined]) M.get
      let put x = (MT.lift [@inlined]) ((M.put [@inlined]) x)
      let fail err = (MT.lift [@inlined]) ((M.fail [@inlined]) err)
    end)
    [@@inline]

    include Trans (Identity)
  end
end

(*
  module Product (P1 : sig
    type state
    type error
  end) (P2 : sig
    type state
    type error
  end) =
  struct
    module P = struct
      type state = P1.state * P2.state
      type error = Left of P1.error | Right of P2.error
    end
    include Make (P)

    module Left = Make (P1)
    module Right = Make (P2)

    let run_left (v : 'a t) : P1.state -> (('a, P1.error) result * P1.state) Right.t =
     fun s_1 ->
      fun s_2 ->
       match v (s_1, s_2) with
       | Ok result, (s_1, s_2) -> (Ok (Ok result, s_1), s_2)
       | Error (Left e_1), (s_1, s_2) -> (Ok (Error e_1, s_1), s_2)
       | Error (Right e_2), (_s_1, s_2) -> (Error e_2, s_2)

    let run_right (v : 'a t) : P2.state -> (('a, P2.error) result * P2.state) Left.t =
     fun s_2 ->
      fun s_1 ->
       match v (s_1, s_2) with
       | Ok result, (s_1, s_2) -> (Ok (Ok result, s_2), s_1)
       | Error (Right e_2), (s_1, s_2) -> (Ok (Error e_2, s_2), s_1)
       | Error (Left e_1), (s_1, _s_2) -> (Error e_1, s_1)
  end
 *)

module Impure (P : sig
  type state
  type error
end) =
struct
  exception Failure of P.error
  type some_ref_type = {x : int; y : int}
  let state : P.state ref = Obj.magic (ref {x = 0; y = 0})
  module Impl = struct
    include P
    type 'a t = unit -> 'a
    let[@inline] return (v : 'a) : 'a t = fun () -> v
    let[@inline] ( >>= ) (v : 'a t) (f : 'a -> 'b t) : 'b t = fun () -> f (v ()) ()

    let get : state t = fun () -> !state
    let put (state' : state) = fun () -> state := state'

    let fail (err : error) = fun () -> raise (Failure err)
  end
  include Impl
  include Make (Impl)
  module S = State (struct
    type t = state
  end)
  include S.Make (Impl)
  module R = Result (struct
    type t = error
  end)
  include R.Make (Impl)
end

(* A codensity-transformed (CPS) state+error monad.

   The codensity transform of a monad [M] is [Codensity M a = ∀r. (a -> M r) -> M r].
   Applied here to the classic state+error monad [M a = state -> ('a, error) result * state]
   it yields a continuation-passing encoding where:

   - [>>=] is O(1) and right-associates the bind tree for free: [c >>= f] just composes
     continuations, so deeply left-nested binds no longer pay the quadratic re-traversal
     cost they incur in the direct {!State_error} representation;
   - no intermediate [('a, error) result * state] pair is allocated per bind — the state is
     threaded as a plain argument through the continuation, and a [result] cell is only
     built at [run] (on success) or at [fail] (on error).

   [get]/[put]/[fail] below are exactly the [lift] of the corresponding {!State_error}
   operations into the codensity monad. *)
module State_error_codensity = struct
  module Make (P : sig
    type state
    type error
  end) =
  struct
    module State = State (struct
      type t = P.state
    end)
    module Result = Result (struct
      type t = P.error
    end)
    module type SIG = sig
      include SIG
      include State.SIG with type 'a t := 'a t
      include Result.SIG with type 'a t := 'a t
    end

    module Make (S : SIG) = struct
      include S
      include Make (S)
      include State.Make (S)
      include Result.Make (S)
    end
    [@@inline]

    module Trans (Inner : SIG_MONAD) = struct
      module Inner = Make_Monad (Inner)

      module Impl = struct
        include P

        type 'a t =
          { run_k :
              'r.
                 ('a -> state -> (('r, error) result * state) Inner.t)
              -> state
              -> (('r, error) result * state) Inner.t }
        [@@unboxed]

        let[@inline] return (x : 'a) : 'a t =
          let[@inline] run_k k = (k [@inlined]) x in
          {run_k}

        let[@inline] ( >>= ) (c : 'a t) (f : 'a -> 'b t) : 'b t =
          let[@inline] run_k k s =
            let[@inline] r a = (((f [@inlined]) a).run_k [@inlined]) k in
            (c.run_k [@inlined]) r s
          in
          {run_k}

        (* lift get  = fun k s -> k s s *)
        let get : state t =
          let[@inline] run_k k s = (k [@inlined]) s s in
          {run_k}

        (* lift (put s') = fun k _ -> k () s' *)
        let[@inline] put (state' : state) : unit t =
          let[@inline] run_k k _s = (k [@inlined]) () state' in
          {run_k}

        (* lift (fail e) short-circuits: the continuation is discarded. *)
        let[@inline] fail (err : error) : 'a t = {run_k = (fun _k state -> Inner.return (Error err, state))}

        let lift (x : 'a Inner.t) : 'a t =
          {run_k = (fun k s -> Inner.(x >>= fun a -> k a s))}
      end
      include Make (Impl)
      include Impl

    (* Feed in the trivial continuation to recover the underlying state+error computation. *)
      let run (x : 'a t) (s : state) : (('a, error) result * state) Inner.t =
        x.run_k (fun v state -> Inner.return (Ok v, state)) s
    end

    include Trans(Identity)
  end
  [@@inline]
end

(* A codensity-transformed (CPS) state+error monad.

   The codensity transform of a monad [M] is [Codensity M a = ∀r. (a -> M r) -> M r].
   Applied here to the classic state+error monad [M a = state -> ('a, error) result * state]
   it yields a continuation-passing encoding where:

   - [>>=] is O(1) and right-associates the bind tree for free: [c >>= f] just composes
     continuations, so deeply left-nested binds no longer pay the quadratic re-traversal
     cost they incur in the direct {!State_error} representation;
   - no intermediate [('a, error) result * state] pair is allocated per bind — the state is
     threaded as a plain argument through the continuation, and a [result] cell is only
     built at [run] (on success) or at [fail] (on error).

   [get]/[put]/[fail] below are exactly the [lift] of the corresponding {!State_error}
   operations into the codensity monad. *)
module State_error_codensity_double_barrel = struct
  module Make (P : sig
    type state
    type error
  end) =
  struct
    module Impl = struct
      include P

      (* [∀r. (a -> M r) -> M r] with [M r = state -> ('r, error) result * state]. The
         universally-quantified ['r] makes this a polymorphic (rank-2) record field. *)
      type 'a t =
        {run_k : 'r. ('a -> state -> ('r, error) result * state) -> state -> ('r, error) result * state}

      let[@inline] return (x : 'a) : 'a t = {run_k = (fun k -> k x)}

      let[@inline] ( >>= ) (c : 'a t) (f : 'a -> 'b t) : 'b t =
        {run_k = (fun k -> c.run_k (fun a -> (f a).run_k k))}

      (* lift get  = fun k s -> k s s *)
      let get : state t = {run_k = (fun k s -> k s s)}

      (* lift (put s') = fun k _ -> k () s' *)
      let put (state' : state) : unit t = {run_k = (fun k _state -> k () state')}

      (* lift (fail e) short-circuits: the continuation is discarded. *)
      let fail (err : error) : 'a t = {run_k = (fun _k state -> (Error err, state))}
    end

    include Impl
    include Make (Impl)
    module S = State (struct
      type t = state
    end)
    include S.Make (Impl)
    module R = Result (struct
      type t = error
    end)
    include R.Make (Impl)

    (* Feed in the trivial continuation to recover the underlying state+error computation. *)
    let run (c : 'a t) (state : state) : ('a, error) result * state =
      c.run_k (fun v state -> (Ok v, state)) state
  end
end
