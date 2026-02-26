open Chain.Ethereum
open Byte_string
open Numeric
open Yojson.Safe.Util

(* Helper functions for reading JSON *)
let ( .$() ) json key = member key json
let ( .$()<- ) json key value =
  to_assoc json |> List.remove_assoc key |> fun l -> (key, value) :: l |> fun l -> `Assoc l

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

module StateTest = struct end
module BlockchainTest = struct
  type info =
    { filling_rpc_server : string [@key "filling-rpc-server"]
    ; filling_tool_version : string [@key "filling-tool-version"]
    ; fixture_format : string [@key "fixture-format"]
    ; hash : U256.t
    ; lllc_version : string [@key "lllcversion"]
    ; repo : string
    ; solidity : string
    ; source : string
    ; source_hash : U256.t [@key "sourceHash"] }
  [@@deriving yojson {strict = false}]

  type blob_schedule =
    {base_fee_update_fraction : Uint.t [@key "baseFeeUpdateFraction"]; max : Uint.t; target : Uint.t}
  [@@deriving yojson]
  type config =
    { blob_schedule : blob_schedule object_as_alist [@key "blobSchedule"]
    ; chain_id : Uint.t [@key "chainid"]
    ; network : string }
  [@@deriving yojson]

  let test_case_block_to_yojson (block : Block.t) =
    (* In test case fixtures, blocks also carry their own RLP encoding and block headers also carry the
       block hash, so we reintroduce them here when deserializing the test case.
       In the future, we should consider introducing fixture-specific of Block.t and Block.Header.t. *)
    let rlp = Bytes.to_yojson (Rlp.encode (Block.to_rlp block)) in
    let hash = B32.to_yojson (Block.hash block) in
    let block = Block.to_yojson block in
    let block = block.$("rlp") <- rlp in
    let header_with_hash = block.$("blockHeader").$("hash") <- hash in
    block.$("blockHeader") <- header_with_hash

  let test_case_blocks_to_yojson (blocks : Block.t list) = `List (List.map test_case_block_to_yojson blocks)

  let test_case_genesis_header_to_yojson (header : Block.Header.t) =
    let genesis_block = {Block.empty with header} in
    (test_case_block_to_yojson genesis_block).$("blockHeader")

  type test_case =
    { network : string
    ; blocks : Block.t list [@to_yojson test_case_blocks_to_yojson]
    ; info : info [@key "_info"]
    ; config : config
    ; genesis_block_header : Block.Header.t
          [@key "genesisBlockHeader"] [@to_yojson test_case_genesis_header_to_yojson]
    ; genesis_rlp : Bytes.t [@key "genesisRLP"]
    ; last_blockhash : U256.t [@key "lastblockhash"]
    ; pre : Account.t Address.Map.t
    ; post : Account.t Address.Map.t [@key "postState"] }
  [@@deriving yojson {strict = false}]

  type t = (string * test_case) list
  let of_yojson ~skip_invalid (test_cases : Yojson.Safe.t) : (t, string) result =
    Result.(
      match test_cases with
      | `Assoc kv ->
          List.filter_mapM kv ~f:(fun (name, v) ->
              match test_case_of_yojson v with
              | Ok test_case -> return (Some (name, test_case))
              | Error _ when skip_invalid -> return None
              | Error err -> fail err )
      | _ -> fail "Fixtures.BlockchainTest.t" )

  let to_yojson (test_cases : t) : Yojson.Safe.t =
    `Assoc (List.map (fun (k, v) -> (k, test_case_to_yojson v)) test_cases)
end

module TrieTest = struct
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
