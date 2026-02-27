(** Utilities for serializing and deserializing EEST-style test fixtures.
    Currently only blockchain tests are supported. *)

open Chain.Ethereum
open Byte_string
open Numeric
open Yojson.Safe.Util

(* Helper functions for reading and writing JSON *)
let ( .$() ) json key = member key json
let ( .$()<- ) obj k v =
  let rec loop = function
    | (k', _) :: rest when k' = k -> (k, v) :: rest
    | (k', v') :: rest -> (k', v') :: loop rest
    | [] -> [(k, v)]
  in
  `Assoc (loop (to_assoc obj))

(* Helper type for encoding and decoding OCaml association lists as JSON objects. *)
type 'v object_as_alist = (string * 'v) list
let object_as_alist_of_yojson value_of_yojson (json : Yojson.Safe.t) : ('v object_as_alist, string) result =
  Result.(
    match json with
    | `Assoc kv ->
        List.mapM kv ~f:(fun (key, v) ->
            let$ value = value_of_yojson v in
            return (key, value) )
    | _ -> fail "object_as_alist_of_yojson" )
let object_as_alist_to_yojson value_to_yojson (alist : 'v object_as_alist) : Yojson.Safe.t =
  `Assoc (List.map (fun (k, v) -> (k, value_to_yojson v)) alist)

(* Safe (non-throwing) conversions from hex strings to bytes. *)
let bytes_of_hex_string str = try Ok (Bytes.of_hex_string str) with _ -> Error "Fixtures.hex_or_string"
let hex_or_string str = if String.starts_with ~prefix:"0x" str then bytes_of_hex_string str else Ok str

module BlockchainTest = struct
  (** EEST blockchain test fixtures. See
      {{:https://steel.ethereum.foundation/docs/execution-specs/running_tests/test_formats/blockchain_test}here}
      for an overview of the file format. *)

  (* An EEST fixture's revision field can contain a single fork name or otherwise two fork names encoded in the
     format "<FORK_NAME>To<FORK_NAME>AtTime15k", to indicate that the fixture's blocks span a fork transition.
   *)
  type revision =
    | Invalid
    (* Some fixtures in the MF test set have mixed revisions like "PragueToMONAD_EIGHT" which are
       unrepresentable. *)
    | Single of Chain.Monad.Revision.t
    | Transition of {pre : Chain.Monad.Revision.t; post : Chain.Monad.Revision.t; timestamp : U256.t}
  let revision_of_yojson (json : Yojson.Safe.t) : (revision, string) result =
    match json with
    | `String "PragueToMONAD_EIGHTAtTime15k" ->
        (* Currently this is the only unrepresentable revision that appears in Foundation tests. If more
           are added later, this pattern can be extended. *)
        Ok Invalid
    | `String str -> (
      match Chain.Monad.Revision.of_string str with
      | Some rev -> Ok (Single rev)
      | None ->
          Option.(
            let$ to_index = String.find_substring ~substring:"To" str in
            let$ () = ensure (String.ends_with ~suffix:"AtTime15k" str) in
            let$ pre = Chain.Monad.Revision.of_string (String.sub str 0 to_index) in
            let$ post =
              Chain.Monad.Revision.of_string
                (String.sub str (to_index + 2)
                   (String.length str - String.length "To" - String.length "AtTime15k" - to_index) )
            in
            Some (Transition {pre; post; timestamp = U256.of_int 15_000}) )
          |> Option.to_result ~none:"Fixtures.BlockchainTest.revision" )
    | _ -> Error "Fixtures.BlockchainTest.revision"

  let revision_to_yojson : revision -> Yojson.Safe.t = function
    | Invalid -> assert false (* We should never be serializing an invalid revision. *)
    | Single rev -> `String (Chain.Monad.Revision.to_string rev)
    | Transition {pre; post; timestamp} ->
        assert (U256.(timestamp = ~$15_000)) ;
        `String
          (Format.sprintf "%sTo%sAtTime15k" (Chain.Monad.Revision.to_string pre)
             (Chain.Monad.Revision.to_string post) )

  type info =
    { filling_rpc_server : string option [@key "filling-rpc-server"] [@default None]
    ; filling_tool_version : string option [@key "filling-tool-version"] [@default None]
    ; fixture_format : string [@key "fixture-format"]
    ; hash : U256.t
    ; lllc_version : string option [@key "lllcversion"] [@default None]
    ; repo : string option [@default None]
    ; solidity : string option [@default None]
    ; source : string option [@default None]
    ; source_hash : U256.t option [@key "sourceHash"] [@default None] }
  [@@deriving yojson {strict = false}]

  type blob_schedule =
    {base_fee_update_fraction : Uint.t [@key "baseFeeUpdateFraction"]; max : Uint.t; target : Uint.t}
  [@@deriving yojson]
  type config =
    { blob_schedule : blob_schedule object_as_alist [@key "blobSchedule"]
    ; chain_id : Uint.t [@key "chainid"]
    ; network : revision }
  [@@deriving yojson]

  (* Test case blocks come in a different format when the test case expects an exception to be raised. *)
  type test_case_block = {block : Block.t; expect_exception : string option}
  let test_case_block_of_yojson json =
    match json.$("expectException") with
    | `Null ->
        (* Parse as normal block. *)
        Result.(
          let$ block = Block.of_yojson json in
          return {block; expect_exception = None} )
    | exn ->
        (* Parse as exception-raising block. *)
        Result.(
          let$ exn = [%of_yojson: string] exn in
          let$ _rlp = Bytes.of_yojson json.$("rlp") in
          let$ block = Block.of_yojson json.$("rlp_decoded") in
          return {block; expect_exception = Some exn} )
  let test_case_block_to_yojson {block; expect_exception} =
    match expect_exception with
    | None -> Block.to_yojson block
    | Some exn ->
        `Assoc
          [ ("rlp", Bytes.to_yojson (Rlp.encode (Block.to_rlp block)))
          ; ("rlp_decoded", Block.to_yojson block)
          ; ("expectException", [%to_yojson: string] exn) ]

  type test_case =
    { info : info [@key "_info"]
    ; network : revision option [@key "network"] [@default None] (* To be deprecated. *)
    ; blocks : test_case_block list
    ; config : config
    ; genesis_block_header : Block.Header.t [@key "genesisBlockHeader"]
    ; genesis_rlp : Bytes.t [@key "genesisRLP"]
    ; last_blockhash : U256.t [@key "lastblockhash"]
    ; pre : Host.Accounts.t
    ; post : Host.Accounts.t [@key "postState"]
    ; seal_engine : string option [@key "sealEngine"] [@default None] (* Deprecated. *) }
  [@@deriving yojson]

  let is_active_revision (test : test_case) =
    match test.config.network with
    | Single rev -> Option.is_some (Chain.Monad.Revision.is_active rev)
    | Transition {pre; post; _} ->
        Option.is_some (Chain.Monad.Revision.is_active pre)
        && Option.is_some (Chain.Monad.Revision.is_active post)
    | Invalid -> false

  type t = (string * test_case) list
  let of_yojson ~skip_invalid (test_cases : Yojson.Safe.t) : (t, string) result =
    Result.(
      match test_cases with
      | `Assoc kv ->
          List.filter_mapM kv ~f:(fun (name, v) ->
              match test_case_of_yojson v with
              | Ok test_case -> (
                (* According to the EEST format spec, test_case.network is deprecated and the authoritative
                   source is test_case.config.network. If present, we expect it to be identical to the network
                   in the config field. *)
                match test_case.network with
                | Some network when network <> test_case.config.network -> fail "Fixtures.BlockchainTest.t"
                | _ -> return (Some (name, test_case)) )
              | Error _ when skip_invalid -> return None
              | Error err -> fail err )
      | _ -> fail "Fixtures.BlockchainTest.t" )

  let to_yojson (test_cases : t) : Yojson.Safe.t =
    `Assoc (List.map (fun (k, v) -> (k, test_case_to_yojson v)) test_cases)
end

module TrieTest = struct
  (** Trie tests matching the ethereum-tests format, see the definition
      {{:https://ethereum-tests.readthedocs.io/en/latest/test_sample/trie_tests.html}here} *)

  type entry = Bytes.t * Bytes.t

  let entry_list_of_yojson ~hex_encoded ~hash_keys (entries : Yojson.Safe.t) : (entry list, string) result =
    Result.(
      let read = if hex_encoded then bytes_of_hex_string else hex_or_string in
      let of_kv (k, v) : (entry, string) result =
        let$ k = read k in
        let key = if hash_keys then B32.to_bytes (Crypto.keccak_256 k) else k in
        let$ value =
          match v with
          | `String str -> hex_or_string str
          | `Null -> return Bytes.empty
          | _ -> fail "Fixtures.TrieTest.entry_list"
        in
        return (key, value)
      in
      match entries with
      | `Assoc kv -> List.mapM kv ~f:of_kv
      | `List kv ->
          List.mapM kv ~f:(function
            | (`List [k; v] : Yojson.Safe.t) -> of_kv (to_string k, v)
            | _ -> fail "Fixtures.TrieTest.entry_list" )
      | _ -> fail "Fixtures.TrieTest.test_case.entries" )

  type test_case = {ordered : bool; entries : entry list; root : B32.t}
  let test_case_of_yojson ~hex_encoded ~hash_keys (json : Yojson.Safe.t) : (test_case, string) result =
    Result.(
      let$ root = B32.of_yojson json.$("root") in
      let entries = json.$("in") in
      let$ ordered =
        match entries with
        | `List _ -> Ok true
        | `Assoc _ -> Ok false
        | _ -> Error "Fixtures.TrieTest.test_case.ordered"
      in
      let$ entries = entry_list_of_yojson ~hex_encoded ~hash_keys entries in
      return {ordered; entries; root} )

  type t = (string * test_case) list
  let of_yojson ~hash_keys (entries : Yojson.Safe.t) : (t, string) result =
    Result.(
      let of_kv (name, entry) =
        let$ hex_encoded = [%of_yojson: bool option] entry.$("hexEncoded") in
        let$ test_case = test_case_of_yojson ~hex_encoded:(hex_encoded = Some true) ~hash_keys entry in
        return (name, test_case)
      in
      match entries with `Assoc kv -> List.mapM kv ~f:of_kv | _ -> fail "Fixtures.TrieTest.t" )
end
