[@@@warning "-8"]

open Monad_lib
open Byte_string
open Numeric
module Address = Chain.Ethereum.Address
open Lens.Infix
let ( .^() ) x lens = lens.Lens.get x
let ( .^()<- ) x lens v' = lens.Lens.set v' x

let n_accounts = int_of_string Sys.argv.(1)
let () = assert (n_accounts < 256)

let n_storage_slots = int_of_string Sys.argv.(2)

let n_updated_slots = int_of_string Sys.argv.(3)
let () = assert (n_updated_slots <= n_storage_slots)

let n_iterations = int_of_string Sys.argv.(4)

let addresses : Address.t list =
  Seq.ints 0 |> Seq.take n_accounts |> Seq.map (fun i -> Address.init (fun _ -> Char.chr i)) |> List.of_seq

let storage_slots : B32.t list =
  Seq.ints 0 |> Seq.take n_storage_slots |> Seq.map (fun i -> U256.(to_repr ~$i)) |> List.of_seq

let updated_slots : B32.t list = List.take n_updated_slots storage_slots

let () =
  Format.printf "n_accounts: %d\n" (List.length addresses) ;
  Format.printf "n_storage_slots: %d\n" (List.length storage_slots) ;
  Format.printf "n_updated_slots: %d\n" (List.length updated_slots) ;
  Format.printf "n_iterations: %d\n" n_iterations

module type MAP_CREATOR = functor
  (Key : sig
     type t
     val compare : t -> t -> int
     val of_bytes_exn : Bytes.t -> t
     val to_bytes : t -> Bytes.t
   end)
  (Value : sig
     type t
     val equal : t -> t -> bool
     val commit : t -> t
     val to_bytes : t -> Bytes.t
     val of_yojson : Yojson.Safe.t -> (t, string) result
     val to_yojson : t -> Yojson.Safe.t
   end)
  -> sig
  type t
  val empty : t
  val at : Key.t -> (t, Value.t option) Lens.t
  val merkleized : t -> t
  val merkle_root : t -> B32.t
  val equal : t -> t -> bool
  val to_yojson : t -> Yojson.Safe.t
  val of_yojson : Yojson.Safe.t -> (t, string) result
end

module Use_mpt_map : MAP_CREATOR = Mpt_map.Make (struct
  let hash_keys = true
  let name = "foo"
end)
module Use_imp_map : MAP_CREATOR = Mpt_lazy_imp.Make (struct
  let hash_keys = true
end)

module Experiment (Make_storage : MAP_CREATOR) (Make_accounts : MAP_CREATOR) = struct
  module Storage =
    Make_storage
      (B32)
      (struct
        include B32
        let commit word = word
        let to_bytes (word : B32.t) = Rlp.encode U256.(to_rlp (of_repr word))
      end)
  module Account = struct
    type t =
      { nonce : U256.t (* σ[a]_n *)
      ; balance : U256.t (* σ[a]_b *)
      ; storage : Storage.t (* σ[a]_s *)
      ; code : Bytes.t (* σ[a]_c *)
      ; code_hash : B32.t }
    [@@deriving lens {submodule = true; prefix = true}]
    include TLens

    module Json = struct
      type repr =
        { nonce : U256.t (* σ[a]_n *)
        ; balance : U256.t (* σ[a]_b *)
        ; storage : Storage.t (* σ[a]_s *)
        ; code : Bytes.t (* σ[a]_c *) }
      [@@deriving lens {submodule = true; prefix = true}, yojson]

      let of_t ({nonce; balance; storage; code; code_hash} : t) : repr = {nonce; balance; storage; code}
      let to_t ({nonce; balance; storage; code} : repr) : t =
        {nonce; balance; storage; code; code_hash = Crypto.keccak_256 code}
    end

    let of_yojson json = Result.map Json.to_t (Json.repr_of_yojson json)
    let to_yojson acc = Json.repr_to_yojson (Json.of_t acc)

    let equal acc_1 acc_2 =
      U256.(acc_1.nonce = acc_2.nonce)
      && U256.(acc_1.balance = acc_2.balance)
      && Storage.(equal acc_1.storage acc_2.storage)
      && B32.(acc_1.code_hash = acc_2.code_hash)
    let ( = ) = equal

    let empty =
      { balance = U256.zero
      ; storage = Storage.empty
      ; code = Bytes.empty
      ; nonce = U256.zero
      ; code_hash = Crypto.keccak_256_empty }

    let is_empty {balance; nonce; code; _} =
      U256.(balance = zero) && U256.(nonce = zero) && Bytes.(code = empty)

    let to_rlp {nonce; balance; storage; code_hash; _} =
      let storage_root = Storage.merkle_root storage in
      Rlp.List [U256.to_rlp nonce; U256.to_rlp balance; Rlp.of_bytes32 storage_root; Rlp.of_bytes32 code_hash]

    let merkleized account = {account with storage = Storage.merkleized account.storage}
  end
  module Accounts =
    Make_accounts
      (Address)
      (struct
        include Account
        let commit acc = merkleized acc
        let to_bytes acc = Rlp.encode (to_rlp acc)
      end)

  let account address = Accounts.at address |-- Option.get_or_default Account.empty

  let slot_content (address : Address.t) (slot : B32.t) (iteration : int) =
    let account = Char.code Address.(address.$(0)) in
    let slot = U256.(to_int (of_repr slot)) in
    U256.(to_repr ~$Stdlib.((account * 100_000) + (slot * 1000) + iteration))

  let initial_storage (address : Address.t) : Storage.t =
    List.fold_left
      (fun storage slot ->
        storage.^(Storage.at slot |-- Option.get_or_default B32.zeros) <- slot_content address slot 0 )
      Storage.empty storage_slots
    |> Storage.merkleized

  let initial_accounts : Accounts.t =
    List.fold_left
      (fun state address ->
        let state = state.^(account address |-- Account.nonce) <- U256.one in
        state.^(account address |-- Account.storage) <- initial_storage address )
      Accounts.empty addresses
    |> Accounts.merkleized

  let account_storage address slot =
    account address |-- Account.storage |-- Storage.at slot |-- Option.get_or_default B32.zeros

  let update_all_accounts (accounts : Accounts.t) (i : int) =
    let update_all_slots accounts address =
      List.fold_left
        (fun accounts_old slot ->
          let accounts = accounts_old.^(account_storage address slot) <- slot_content address slot i in
          accounts )
        accounts updated_slots
    in
    let accounts = List.fold_left update_all_slots accounts addresses in
    let accounts = Accounts.merkleized accounts in
    let state_root = Accounts.merkle_root accounts in
    (state_root, accounts)

  let run iterations =
    Seq.ints 1
    |> Seq.take iterations
    |> Seq.fold_left
         (fun (roots, state) i ->
           let new_root, state = update_all_accounts state i in
           (new_root :: roots, state) )
         ([], initial_accounts)

  let example_address = List.hd addresses
  let update_all_slots storage i =
    let storage =
      List.fold_left
        (fun storage slot ->
          storage.^(Storage.at slot |-- Option.get_or_default B32.zeros) <-
            slot_content example_address slot i )
        storage updated_slots
    in
    let storage = Storage.merkleized storage in
    let root = Storage.merkle_root storage in
    (root, storage)

  let run_simple iterations =
    Seq.ints 1
    |> Seq.take iterations
    |> Seq.fold_left
         (fun (roots, storage) i ->
           Format.printf "ITERATION %d\n" i ;
           let new_root, storage = update_all_slots storage i in
           (new_root :: roots, storage) )
         ([], initial_storage example_address)
end

module Experiment_map_map = Experiment (Use_mpt_map) (Use_mpt_map)
module Experiment_imp_map = Experiment (Use_imp_map) (Use_mpt_map)
module Experiment_map_imp = Experiment (Use_mpt_map) (Use_imp_map)
module Experiment_imp_imp = Experiment (Use_imp_map) (Use_imp_map)

module Experiment_accounts = struct
  open Host
  open Chain.Ethereum

  let account addr = Accounts.at addr |-- Option.get_or_default Account.empty

  let slot_content (address : Address.t) (slot : B32.t) (iteration : int) =
    let account = Char.code Address.(address.$(0)) in
    let slot = U256.(to_int (of_repr slot)) in
    U256.(to_repr ~$Stdlib.((account * 100_000) + (slot * 1000) + iteration))

  let initial_storage (address : Address.t) : Storage.t =
    List.fold_left
      (fun storage slot ->
        storage.^(Storage.at slot |-- Option.get_or_default B32.zeros) <- slot_content address slot 0 )
      Storage.empty storage_slots
    |> Storage.merkleized

  let initial_accounts : Accounts.t =
    List.fold_left
      (fun state address ->
        let state = state.^(account address |-- Account.nonce) <- U256.one in
        state.^(account address |-- Account.storage) <- initial_storage address )
      Accounts.empty addresses
    |> Accounts.merkleized

  let account_storage address slot =
    account address |-- Account.storage |-- Storage.at slot |-- Option.get_or_default B32.zeros

  let update_all_accounts (accounts : Accounts.t) (i : int) =
    let update_all_slots accounts address =
      List.fold_left
        (fun accounts_old slot ->
          let accounts = accounts_old.^(account_storage address slot) <- slot_content address slot i in
          accounts )
        accounts updated_slots
    in
    let accounts = List.fold_left update_all_slots accounts addresses in
    let accounts = Accounts.merkleized accounts in
    let state_root = Accounts.merkle_root accounts in
    (state_root, accounts)

  let run iterations =
    Seq.ints 1
    |> Seq.take iterations
    |> Seq.fold_left
         (fun (roots, state) i ->
           let new_root, state = update_all_accounts state i in
           (new_root :: roots, state) )
         ([], initial_accounts)
end

module Experiment_WorldState = struct
  open Host
  open Chain.Ethereum

  let account addr = WorldState.account addr

  let slot_content (address : Address.t) (slot : B32.t) (iteration : int) =
    let account = Char.code Address.(address.$(0)) in
    let slot = U256.(to_int (of_repr slot)) in
    U256.(to_repr ~$Stdlib.((account * 100_000) + (slot * 1000) + iteration))

  let initial_storage (address : Address.t) : Storage.t =
    List.fold_left
      (fun storage slot ->
        storage.^(Storage.at slot |-- Option.get_or_default B32.zeros) <- slot_content address slot 0 )
      Storage.empty storage_slots
    |> Storage.merkleized

  let initial_accounts : WorldState.t =
      List.fold_left
        (fun state address ->
          let state = state.^(account address |-- Account.nonce) <- U256.one in
          state.^(account address |-- Account.storage) <- initial_storage address )
        WorldState.empty addresses
      |> WorldState.state_root
    |> snd

  let account_storage address slot =
    account address |-- Account.storage |-- Storage.at slot |-- Option.get_or_default B32.zeros

  let update_all_accounts (state : WorldState.t) (i : int) =
    let update_all_slots state address =
      List.fold_left
        (fun state_old slot ->
          let state = state_old.^(account_storage address slot) <- slot_content address slot i in
          state )
        state updated_slots
    in
    let state = List.fold_left update_all_slots state addresses in
    WorldState.state_root state

  let run iterations =
    Seq.ints 1
    |> Seq.take iterations
    |> Seq.fold_left
         (fun (roots, state) i ->
           let new_root, state = update_all_accounts state i in
           (new_root :: roots, state) )
         ([], initial_accounts)
end

let () =
  let ctl = Gc.get () in
  let ctl = Gc.{ctl with minor_heap_size = 8 * 1024 * 1024 (*; space_overhead = 200*)} in
  Gc.set ctl ;
  Crypto.trace := true ;
  let (state_root :: _) =
    match Sys.argv.(5) with
    | "imp_map" -> fst (Experiment_imp_map.run n_iterations)
    | "map_map" -> fst (Experiment_map_map.run n_iterations)
    | "imp_imp" -> fst (Experiment_imp_imp.run n_iterations)
    | "map_imp" -> fst (Experiment_map_imp.run n_iterations)
    | "accounts" -> fst (Experiment_accounts.run n_iterations)
    | "worldstate" -> fst (Experiment_WorldState.run n_iterations)
  in
  Format.printf "State root: %s\n" (B32.to_hex_string state_root) ;
  Format.printf "Redundant bytes hashed: %d\n" !Crypto.redundant_bytes_hashed ;
  ()
