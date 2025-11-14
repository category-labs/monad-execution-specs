(** Monad definition and associated operators. *)

(** The signature of a module defining a monad. Note that this is a "thin" signature, defining only a type and
    bind and return operations. Additional operations are provided by the {!Monad.Make} functor.
 *)
module type SIG = sig
  type 'a t
  val return : 'a -> 'a t
  val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t
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

(* Alias to avoid shadowing Make from child modules. *)
module Make_Monad = Make

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
    val get : T.t t
    val put : T.t -> unit t
  end

  module Make (S : SIG) = struct
    include S
    include Make (S)
    let[@inline] update (f : T.t -> T.t) : unit t = get >>= fun s -> put (f s)

    let[@inline] ( := ) (l : (T.t, 'x) Lens.t) (x : 'x) =
      let$ state = get in
      put (l.set x state)

    let[@inline] ( ! ) (l : (T.t, 'x) Lens.t) : 'x t =
      let$ state = get in
      return (l.get state)

    let[@inline] update_field (l : (T.t, 'x) Lens.t) (f : 'x -> 'x) : unit t =
      let$ v = !l in
      l := f v
  end[@@inline]

  module Trans (Inner : SIG_MONAD) = struct
    module Inner = Make_Monad (Inner)

    module Impl = struct
      type 'a t = {run : 'r. T.t -> (T.t -> 'a -> 'r Inner.t) -> 'r Inner.t} [@@unboxed]

      let[@inline] return (type a) (x : a) : a t = {run = (fun s cont -> cont s x)}
      let[@inline] ( >>= ) (type a b) (x : a t) (f : a -> b t) : b t =
        {run = (fun s cont -> x.run s (fun s xe -> (f xe).run s cont))}

      let[@inline] get : T.t t = {run = (fun s cont -> cont s s)}
      let[@inline] put (s : T.t) : unit t = {run = (fun _s cont -> cont s ())}
    end
    include Make (Impl)

    let[@inline] lift (type a) (x : a Inner.t) : a t = {run = (fun s cont -> Inner.(x >>= cont s))}

    let[@inline] run (x : 'a t) (s : T.t) : ('a * T.t) Inner.t = x.run s (fun s' y -> Inner.return (y, s'))
  end[@@inline]

  module Lift (MT : TRANS) (M : SIG with type 'a t = 'a MT.Inner.t) = struct
    include Make (struct
      include MT
      let get : T.t MT.t = MT.lift M.get
      let put x = MT.lift (M.put x)
    end)
  end[@@inline]

  include Trans (Identity)
end[@@inline]

module Result (T : sig
  type t
end) =
struct
  module type SIG = sig
    include SIG_MONAD
    val fail : T.t -> 'a t
  end

  module Make (S : SIG) = struct
    include S
    include Make_Monad (S)

    module Option = struct
      include Option

      let or_fail (err : T.t) = function None -> S.fail err | Some x -> S.return x
    end
  end[@@inline]

  module Lift (MT : TRANS) (M : SIG with type 'a t = 'a MT.Inner.t) : SIG = struct
    include Make (struct
      include MT
      let fail (x : T.t) : 'a MT.t = MT.lift (M.fail x)
    end)
  end[@@inline]

  module Trans (Inner : SIG_MONAD) = struct
    module Inner = Make_Monad (Inner)

    include Make (struct
      type 'a t = ('a, T.t) result Inner.t
      let[@inline] return (x : 'a) : 'a t = Inner.return (Ok x)
      let[@inline] ( >>= ) (x : 'a t) (f : 'a -> 'b t) =
        Inner.(x >>= function Error err -> Inner.return (Error err) | Ok x -> f x)

      let[@inline] fail (err : T.t) = Inner.return (Error err)
    end)

    let[@inline] lower (x : ('a, T.t) result) : 'a t = Inner.return x
    let[@inline] lift (x : 'a Inner.t) : 'a t = Inner.fmap Result.ok x
  end[@@inline]

  include Trans (Identity)
end[@@inline]

module Reader (T : sig
  type t
end) =
struct
  module type SIG = sig
    include SIG_MONAD
    val read : T.t t
  end

  module Make (S : SIG) = struct
    include S
    include Make_Monad (S)
  end[@@inline]

  module Lift (MT : TRANS) (M : SIG with type 'a t = 'a MT.Inner.t) : SIG = Make (struct
    include MT
    let read = MT.lift M.read
  end)[@@inline]

  module Trans (Inner : SIG_MONAD) = struct
    module Inner = Make_Monad (Inner)

    module Impl = struct
      type 'a t = {run : 'r. T.t -> ('a -> 'r Inner.t) -> 'r Inner.t} [@@unboxed]

      let[@inline] return (x : 'a) : 'a t = {run = (fun _s cont -> cont x)}

      let[@inline] ( >>= ) (x : 'a t) (f : 'a -> 'b t) : 'b t =
        {run = (fun s cont -> x.run s (fun xe -> (f xe).run s cont))}

      let[@inline] read = {run = (fun s cont -> cont s)}
    end
    include Make (Impl)

    let[@inline] lift (x : 'a Inner.t) : 'a t = {run = (fun _s cont -> Inner.(x >>= cont))}

    let[@inline] run (x : 'a t) (s : T.t) : 'a Inner.t = x.run s (fun x -> Inner.return x)
  end[@@inline]

  include Trans (Identity)
end[@@inline]
