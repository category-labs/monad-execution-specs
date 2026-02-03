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

  let[@inline] ( let$ ) x f = M.(x >>= f)

  let[@inline] fmap f x = M.(x >>= fun x -> return (f x))
  let[@inline] ( <$> ) f x = fmap f x
  let[@inline] ( <*> ) (f : ('a -> 'b) M.t) (x : 'a M.t) : 'b M.t =
    let$ f = f in
    let$ x = x in
    return (f x)

  let[@inline] ( >> ) (mx : unit M.t) (y : 'a M.t) : 'a M.t = M.(mx >>= fun _ -> y)

  let[@inline] when_ cond mx = if cond then mx else M.return ()

  module Option = struct
    include Option

    let[@inline] iterM (x : 'a option) ~(f : 'a -> unit M.t) : unit M.t =
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
    let[@inline] return x = x
    let[@inline] ( >>= ) x f = f x
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

    (*
    val get : state t
    val put : state -> unit t
     *)
    val get : state t
    val update : (state -> state) -> unit t
  end

  module Make (S : SIG) = struct
    include S
    include Make (S)
    type state = T.t

    open Lens.Infix
    let[@inline] put s = update (fun _ -> s)
    let[@inline] ( := ) (l : (state, 'x) Lens.t) (x : 'x) =
      let[@inline] upd s = (l.set [@inlined]) x s in
      (update [@inlined]) upd
    let[@inline] ( ! ) (l : (state, 'x) Lens.t) : 'x t = l.get <$> get
    let[@inline] update_field (l : (state, 'x) Lens.t) (f : 'x -> 'x) : unit t = update (l ^%= f)
    (*
    let[@inline] update (f : state -> state) : unit t = get >>= fun s -> put (f s)


    let[@inline] ( := ) (l : (state, 'x) Lens.t) (x : 'x) =
      let$ state = get in
      put (l.set x state)

    let[@inline] ( ! ) (l : (state, 'x) Lens.t) : 'x t =
      let$ state = get in
      return (l.get state)

    let[@inline] update_field (l : (state, 'x) Lens.t) (f : 'x -> 'x) : unit t =
      let$ v = !l in
      l := f v
     *)
  end
  [@@inline]

  module Trans (Inner : SIG_MONAD) = struct
    module Inner = Make_Monad (Inner)

    module type IMPL = sig
      type 'a t
      type state = T.t

      val return : 'a -> 'a t
      val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t

      val get : state t
      val update : (state -> state) -> unit t

      val run : 'a t -> state -> ('a * state) Inner.t

      val lift : 'a Inner.t -> 'a t
    end

    module Impl_codensity : IMPL = struct
      type 'a t = {run : 's. T.t -> ('a -> T.t -> 's Inner.t) -> 's Inner.t} [@@unboxed]

      let[@inline] return (x : 'a) : 'a t =
        let run state cont = cont x state in
        {run}
      let[@inline] ( >>= ) (x : 'a t) (f : 'a -> 'b t) =
        let run state cont =
          let cont' x state = (f x).run state cont in
          x.run state cont'
        in
        {run}

      type state = T.t
      let get : T.t t =
        let run state cont = cont state state in
        {run}
      let[@inline] update (f : state -> state) : unit t =
        let run s cont = cont () (f s) in
        {run}

      let[@inline] run (act : 'a t) (s : state) : ('a * state) Inner.t =
        act.run s (fun v s -> Inner.return (v, s))

      let[@inline] lift (x : 'a Inner.t) : 'a t =
        let run state cont =
          Inner.(
            let$ x = x in
            cont x state )
        in
        {run}
    end

    module Impl_classic : IMPL = struct
      type state = T.t
      type 'a t = {run : state -> ('a * state) Inner.t}

      let[@inline] return (x : 'a) : 'a t =
        let run state = Inner.return (x, state) in
        {run}
      let[@inline] ( >>= ) (x : 'a t) (f : 'a -> 'b t) =
        let run state =
          Inner.(
            let$ x, state = x.run state in
            (f x).run state )
        in
        {run}

      let get : state t =
        let run state = Inner.return (state, state) in
        {run}
      let[@inline] update (f : state -> state) : unit t =
        let run state = Inner.return ((), f state) in
        {run}

      let[@inline] run (act : 'a t) (s : state) : ('a * state) Inner.t = act.run s

      let[@inline] lift (x : 'a Inner.t) : 'a t =
        let run state : ('a * state) Inner.t =
          Inner.(
            let$ x = x in
            return (x, state) )
        in
        {run}
    end
    module Impl = Impl_codensity
    include Make (Impl)

    (*
    let[@inline] lower (x : state -> 'a * state) : 'a t = fun s -> Inner.return (x s)
     *)
    let[@inline] lift (x : 'a Inner.t) : 'a t = Impl.lift x
    let[@inline] run x s = Impl.run x s
  end
  [@@inline]

  module Lift (MT : TRANS) (M : SIG with type 'a t = 'a MT.Inner.t) = struct
    include Make (struct
      include MT
      type state = T.t
      let get : T.t MT.t = MT.lift M.get
      let[@inline] update f = MT.lift (M.update f)
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
      let[@inline] return (x : 'a) : 'a t = Inner.return (Ok x)
      let[@inline] ( >>= ) (x : 'a t) (f : 'a -> 'b t) =
        Inner.(x >>= function Error err -> Inner.return (Error err) | Ok x -> f x)

      type error = T.t
      let[@inline] fail (err : T.t) = Inner.return (Error err)
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
        let update f = fun s -> Inner.return (Ok ((), f s))
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
end
