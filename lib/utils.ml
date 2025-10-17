exception Unimplemented
exception Internal_error

let todo () = raise Unimplemented

(* Alias for String (immutable byte array) because Bytes.t in the stdlib refers to mutable byte arrays *)
module Bytes = struct
  include String

  (*
   * sub_with_zero_padding bytes i sz returns a sz-length byte array formed by zero-padding
   * the array bytes[i, min(len(bytes), i+sz)) to length sz
   *)
  let sub_with_zero_padding bytes i sz =
    init sz (fun j -> if i + j >= length bytes then '\x00' else bytes.[i + j])

  let to_hex_string bytes =
    to_seq bytes |> Seq.map Char.code |> Seq.map (Format.sprintf "%02x") |> List.of_seq |> String.concat ""

  let of_hex_string str =
    assert (String.length str mod 2 = 0) ;
    (* Optionally discard 0x prefix *)
    let str = if String.starts_with ~prefix:"0x" str then String.sub str 2 (String.length str - 2) else str in
    init
      (String.length str / 2)
      (fun i -> Char.chr (int_of_string (Printf.sprintf "0x%c%c" str.[i * 2] str.[(i * 2) + 1])))

  let reverse (bs : t) : t =
    let l = length bs in
    init l (fun i -> bs.[l - i - 1])
end

module type TY = sig
  type t
end

module Lens = struct
  include Lens

  let get_or_create (create : unit -> 'a) : ('a option, 'a) t =
    {get = (function None -> create () | Some v -> v); set = (fun x _ -> Some x)}

  let get_or_default (default : 'a) : ('a option, 'a) t =
    {get = (function None -> default | Some v -> v); set = (fun x _ -> Some x)}

  let get_or_throw : ('a option, 'a) t = {get = Option.get; set = (fun x _ -> Some x)}
end

(* Lens-aware map *)
module Map = struct
  module type OrderedType = Map.OrderedType
  module type S = sig
    include Map.S
    val at : key -> ('v t, 'v option) Lens.t
  end
  module Make (Ord : OrderedType) = struct
    include Map.Make (Ord)
    let at (k : key) : ('v t, 'v option) Lens.t =
      {get = (fun m -> find_opt k m); set = (fun v m -> update k (fun _ -> v) m)}
  end
end

module Monad0 = struct
  module type SIG = sig
    type 'a t
    val return : 'a -> 'a t
    val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t
  end

  (* Useful combinators for any monad *)
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

      include List
    end

    module Seq = struct
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

  module type TRANS = sig
    include SIG
    module Underlying : SIG
    val lift : 'a Underlying.t -> 'a t
  end
end

module Identity = struct
  type 'a t = 'a
  let return x = x
  let ( >>= ) x f = f x
end

module State (T : TY) = struct
  module type SIG = sig
    include Monad0.SIG
    val get : T.t t
    val put : T.t -> unit t
  end

  module Make (S : SIG) = struct
    open S
    open Monad0.Make (S)
    let update (f : T.t -> T.t) : unit t = get >>= fun s -> put (f s)

    let ( := ) (l : (T.t, 'x) Lens.t) (x : 'x) =
      let$ state = get in
      put (l.set x state)

    let ( ! ) (l : (T.t, 'x) Lens.t) : 'x t =
      let$ state = get in
      return (l.get state)

    let update_field (l : (T.t, 'x) Lens.t) (f : 'x -> 'x) : unit t =
      let$ v = !l in
      l := f v
  end

  module Trans (Underlying : Monad0.SIG) = struct
    module Underlying = struct
      include Monad0.Make (Underlying)
    end
    module Impl = struct
      type 'a t = T.t -> ('a * T.t) Underlying.t
      let return (x : 'a) : 'a t = fun s -> Underlying.return (x, s)
      let ( >>= ) (x : 'a t) (f : 'a -> 'b t) =
       fun s ->
        Underlying.(
          let$ x, s = x s in
          f x s )

      let get : T.t t = fun s -> Underlying.return (s, s)
      let put (s : T.t) : unit t = fun _ -> Underlying.return ((), s)

      let lower (x : T.t -> 'a * T.t) : 'a t = fun s -> Underlying.return (x s)
      let lift (x : 'a Underlying.t) : 'a t = fun s -> Underlying.fmap (fun x -> (x, s)) x
    end

    include Impl
    include Monad0.Make (Impl)
    include Make (Impl)
  end

  module Lift (MT : Monad0.TRANS) (M : SIG with type 'a t = 'a MT.Underlying.t) = struct
    module Impl = struct
      include MT
      let get : T.t MT.t = MT.lift M.get
      let put x = MT.lift (M.put x)
    end
    include Impl
    include Make (Impl)
  end

  include Trans (Identity)
end

module Result (T : TY) = struct
  module type SIG = sig
    include Monad0.SIG
    val fail : T.t -> 'a t
  end

  module Make (S : SIG) = struct
    module Option = struct
      module M = Monad0.Make (S)
      include M.Option

      let or_fail (err : T.t) = function None -> S.fail err | Some x -> S.return x
    end
  end

  module Lift (MT : Monad0.TRANS) (M : SIG with type 'a t = 'a MT.Underlying.t) : SIG = struct
    include MT
    let fail (x : T.t) : 'a MT.t = MT.lift (M.fail x)
  end

  module Trans (M : Monad0.SIG) = struct
    module Underlying = struct
      include Monad0.Make (M)
    end
    module Impl = struct
      type 'a t = ('a, T.t) result M.t
      let return (x : 'a) : 'a t = M.return (Ok x)
      let ( >>= ) (x : 'a t) (f : 'a -> 'b t) =
        M.(x >>= function Error err -> M.return (Error err) | Ok x -> f x)

      let fail (err : T.t) = M.return (Error err)

      let lower (x : ('a, T.t) result) : 'a t = M.return x
      let lift (x : 'a Underlying.t) : 'a t = Underlying.fmap Result.ok x
    end

    include Impl
    include Monad0.Make (Impl)
    include Make (Impl)
  end

  include Trans (Identity)
end

module Monad = struct
  include Monad0
  module State (T : TY) = State (T)
  module Result (T : TY) = Result (T)
end
