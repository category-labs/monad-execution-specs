open Byte_string
open Chain.Ethereum
open State
open Type

module Make (Addr : sig
  val address : Address.t
end) =
struct
  (* In-storage data slot. *)
  module Loc = struct
    open Lens.Infix

    module Impl : sig
      type 'a t = private {typ : 'a typ; kind : kind; offset : U256.t}
      val ( @ ) : 'a typ -> U256.t -> 'a t
      val ( + ) : 'a t -> U256.t -> 'a t
    end = struct
      type 'a t = {typ : 'a typ; kind : kind; offset : U256.t}

      let ( @ ) typ offset =
        let kind = kind typ in
        {typ; kind; offset}

      let ( + ) ({typ; offset; kind} : 'a t) (dx : U256.t) =
        let offset = U256.(offset + dx) in
        {typ; offset; kind}
    end
    include Impl

    let lens {typ; offset; _} : (TransactionState.t, 'a) Lens.t =
      let type_lens =
        let get (s : Storage.t) =
          let view = Input_view.of_storage s ~offset in
          (* This should never happen: if decoding fails, this means some other point of the program has
             written an invalid value to this storage location, which is a programming error. *)
          fst (Result.get_ok (dec typ view))
        in
        let set (v : 'a) (s : Storage.t) =
          let words = enc typ v in
          let s, _ =
            List.fold_left
              (fun (storage, i) value ->
                let key = U256.(to_repr (offset + i)) in
                let storage = Storage.add key value storage in
                let i = U256.(i + one) in
                (storage, i) )
              (s, U256.zero) words
          in
          s
        in
        Lens.{get; set}
      in
      TransactionState.account Addr.address |-- Account.storage |-- type_lens

    let cast ({offset; _} : 'a t) (typ : 'b typ) : 'b t = typ @ offset

    (* Clear the memory occupied by this location. The underlying type must have a static layout. *)
    let clear (loc : 'a t) : unit TransactionState.M.t =
      let word_width = match loc.kind with Static {word_width} -> word_width | Dynamic -> assert false in
      let storage = TransactionState.account Addr.address |-- Account.storage in
      let end_ = U256.(loc.offset + ~$word_width) in
      TransactionState.M.(
        let rec loop (slot : U256.t) =
          if U256.(slot < end_) then
            let$ () = storage |-- Storage.at (U256.to_repr slot) := B32.zeros in
            loop U256.(slot + one)
          else return ()
        in
        loop loc.offset )
  end

  (** [TransactionState.M] extended with higher-level operators for manipulating storage. *)
  module M = struct
    include TransactionState.M

    let ( !$ ) (l : 'a Loc.t) : 'a t = !(Loc.lens l)
    let ( $= ) (l : 'a Loc.t) (v : 'a) : unit t = Loc.lens l := v
  end

  module Mapping = struct
    (* Raw mappings. Note there is no way to determine cardinality. *)
    type ('k, 'v) t = 'k -> 'v Loc.t
    let make (enc : 'k -> U256.t) (typ : 'v typ) : ('k, 'v) t = fun k -> Loc.(typ @ enc k)

    module Index = struct
      type 'a t = 'a -> Bytes.t

      let address : Address.t t = Address.to_bytes
      let u64 : U64.t t = U64.to_repr_bytes
      let u8 : U8.t t = U8.to_repr_bytes

      let pair (i1 : 'a t) (i2 : 'b t) : ('a * 'b) t = fun (a, b) -> i1 a ^ i2 b
      let tuple3 (i1 : 'a t) (i2 : 'b t) (i3 : 'c t) : ('a * 'b * 'c) t = fun (a, b, c) -> i1 a ^ i2 b ^ i3 c

      let namespace (ns : Bytes.t) (index : 'k t) : 'k -> U256.t =
       fun key ->
        let ns_key = ns ^ index key in
        assert (Bytes.length ns_key <= 32) ;
        let padded = B32.sub_with_zero_padding ns_key 0 in
        U256.of_repr padded
    end

    let ( .${} ) (map : ('k, 'v) t) (k : 'k) : 'v Loc.t = map k
  end

  module Array = struct
    let length = Packed.t U64.t

    (* An array backed by storage. The `length` loc holds the length as a 64-bit packed (left-aligned) unsigned
       integer, and the `first` loc points to the first data slot of the array. *)
    type 'a t = {length : U64.t Loc.t; first : 'a Loc.t}

    let make (start : U256.t) (typ : 'a typ) =
      let length = Loc.(length @ start) in
      let first = Loc.(typ @ U256.(start + one)) in
      match first.kind with Static _ -> {length; first} | _ -> assert false

    let ( .$() ) ({first; _} : 'a t) (i : U64.t) : 'a Loc.t =
      let word_width = match first.kind with Static {word_width} -> word_width | Dynamic -> assert false in
      Loc.(first + U256.(~$word_width * of_z_exn (U64.to_z i)))

    (* Monadic API for convenience. *)
    let is_empty (arr : 'a t) : bool M.t =
      M.(
        let$ len = !$(arr.length) in
        return U64.(len = zero) )

    let push (arr : 'a t) (v : 'a) : unit M.t =
      M.(
        let$ len = !$(arr.length) in
        let$ () = arr.$(len) $= v in
        arr.length $= U64.(len + one) )

    let pop (arr : 'a t) : 'a M.t =
      M.(
        let$ len = !$(arr.length) in
        assert (U64.(len > zero)) ;
        let index = U64.(len - one) in
        let$ v = !$(arr.$(index)) in
        let$ () = Loc.clear arr.$(index) in
        let$ () = arr.length $= index in
        return v )

    let read_to_list (arr : 'a t) : 'a list M.t =
      M.(
        let$ len = !$(arr.length) in
        let rec loop (i : U64.t) : 'a list M.t =
          if U64.(i >= len) then return List.[]
          else
            let$ elt : 'a = !$(arr.$(i)) in
            let$ elts : 'a list = loop U64.(i + one) in
            return List.(elt :: elts)
        in
        loop U64.zero )

    let write_of_list (arr : 'a t) (list : 'a list) : unit M.t =
      M.(
        let$ old_len = !$(arr.length) in
        let$ last =
          let rec write_loop i elts =
            match elts with
            | List.[] -> return i
            | List.(elt :: elts) ->
                let$ () = arr.$(i) $= elt in
                write_loop U64.(i + one) elts
          in
          write_loop U64.zero list
        in
        let$ () =
          let rec clear_loop i =
            if U64.(i >= old_len) then return ()
            else
              let$ () = Loc.clear arr.$(i) in
              clear_loop U64.(i + one)
          in
          clear_loop last
        in
        arr.length $= last )

    let clear (arr : 'a t) : unit M.t = write_of_list arr []

    let iteriM (arr : 'a t) ~(f : U64.t -> 'a -> unit M.t) : unit M.t =
      M.(
        let$ len = !$(arr.length) in
        let rec loop i =
          if U64.(i >= len) then return ()
          else
            let$ elt = !$(arr.$(i)) in
            let$ () = f i elt in
            loop U64.(i + one)
        in
        loop U64.zero )
  end
end
