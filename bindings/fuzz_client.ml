open Monad_lib
open Byte_string
open Numeric
open Chain.Ethereum

(* TODO: move this to chain *)
module Consensus = struct
  module B33 = Byte_string.Fixed (struct
    let byte_width = `Fixed 33
  end)
  module B96 = Byte_string.Fixed (struct
    let byte_width = `Fixed 96
  end)

  module Vote = struct
    module type SIG = sig
      type t

      val to_rlp : t -> Rlp.t
      val of_rlp : Rlp.t -> t option

      val to_yojson : t -> Yojson.Safe.t
      val of_yojson : Yojson.Safe.t -> t Ppx_deriving_yojson_runtime.error_or
    end

    module V0 = struct
      type t = {id : B32.t; round : U64.t; epoch : U64.t; parent_id : B32.t; parent_round : U64.t}
      [@@deriving yojson]

      let to_rlp {id; round; epoch; parent_id; parent_round} =
        Rlp.(
          List
            [B32.to_rlp id; U64.to_rlp round; U64.to_rlp epoch; B32.to_rlp parent_id; U64.to_rlp parent_round] )
      let of_rlp = function
        | Rlp.List [id; round; epoch; parent_id; parent_round] ->
            Option.(
              let$ id = B32.of_rlp id in
              let$ round = U64.of_rlp round in
              let$ epoch = U64.of_rlp epoch in
              let$ parent_id = B32.of_rlp parent_id in
              let$ parent_round = U64.of_rlp parent_round in
              return {id; round; epoch; parent_id; parent_round} )
        | _ -> None
    end

    module V1 = struct
      type t = {id : B32.t; round : U64.t; epoch : U64.t} [@@deriving yojson]

      let to_rlp vote = Rlp.(List [B32.to_rlp vote.id; U64.to_rlp vote.round; U64.to_rlp vote.epoch])

      let of_rlp = function
        | Rlp.List [id; round; epoch] ->
            Option.(
              let$ id = B32.of_rlp id in
              let$ round = U64.of_rlp round in
              let$ epoch = U64.of_rlp epoch in
              return {id; round; epoch} )
        | _ -> None
    end
  end

  module SignerMap = struct
    type t = {num_bits : U32.t; bitmap : Bytes.t} [@@deriving yojson]

    let to_rlp signer_map = Rlp.(List [U32.to_rlp signer_map.num_bits; Rlp.of_bytes signer_map.bitmap])

    let of_rlp = function
      | Rlp.List [num_bits; bitmap] ->
          Option.(
            let$ num_bits = U32.of_rlp num_bits in
            let$ bitmap = Bytes.of_rlp bitmap in
            return {num_bits; bitmap} )
      | _ -> None
  end

  module Signatures = struct
    type t = {signer_map : SignerMap.t; aggregate_signature : B96.t} [@@deriving yojson]

    let to_rlp signatures =
      Rlp.(
        List
          [SignerMap.to_rlp signatures.signer_map; Rlp.of_bytes (B96.to_bytes signatures.aggregate_signature)] )

    let of_rlp = function
      | Rlp.List [signer_map; aggregate_signature] ->
          Option.(
            let$ signer_map = SignerMap.of_rlp signer_map in
            let$ aggregate_signature = B96.of_rlp aggregate_signature in
            return {signer_map; aggregate_signature} )
      | _ -> None
  end

  module QuorumCertificate (V : Vote.SIG) = struct
    type t = {vote : V.t; signatures : Signatures.t} [@@deriving yojson]

    let to_rlp qc = Rlp.(List [V.to_rlp qc.vote; Signatures.to_rlp qc.signatures])

    let of_rlp = function
      | Rlp.List [vote; signatures] ->
          Option.(
            let$ vote = V.of_rlp vote in
            let$ signatures = Signatures.of_rlp signatures in
            return {vote; signatures} )
      | _ -> None
  end

  module Header = struct
    (* TODO: simplify this if possible. *)
    module Base (V : Vote.SIG) = struct
      module QC = QuorumCertificate (V)
      type t =
        { block_round : U64.t
        ; epoch : U64.t
        ; qc : QC.t
        ; author : B33.t
        ; seq_number : U64.t
        ; timestamp_ns : U128.t
        ; round_signature : B96.t
        ; delayed_execution_results : Block.Header.t list
        ; execution_inputs : Block.Header.t
        ; block_body_id : B32.t }
      [@@deriving yojson]

      let of_rlp_fields : Rlp.t list -> (t * Rlp.t list) option = function
        | block_round
          :: epoch
          :: qc
          :: author
          :: seq_number
          :: timestamp_ns
          :: round_signature
          :: Rlp.List delayed_execution_results
          :: execution_inputs
          :: block_body_id
          :: remaining_fields ->
            Option.(
              let$ block_round = U64.of_rlp block_round in
              let$ epoch = U64.of_rlp epoch in
              let$ qc = QC.of_rlp qc in
              let$ author = B33.of_rlp author in
              let$ seq_number = U64.of_rlp seq_number in
              let$ timestamp_ns = U128.of_rlp timestamp_ns in
              let$ round_signature = B96.of_rlp round_signature in
              let$ delayed_execution_results =
                sequence (List.map Block.Header.of_rlp delayed_execution_results)
              in
              let$ execution_inputs = Block.Header.of_rlp_input execution_inputs in
              let$ block_body_id = B32.of_rlp block_body_id in
              return
                ( { block_round
                  ; epoch
                  ; qc
                  ; author
                  ; seq_number
                  ; timestamp_ns
                  ; round_signature
                  ; delayed_execution_results
                  ; execution_inputs
                  ; block_body_id }
                , remaining_fields ) )
        | _ -> None
    end

    module B0 = Base (Vote.V0)
    module B1 = Base (Vote.V1)

    type t =
      | V0 of {common : B0.t}
      | V1 of {common : B1.t}
      | V2 of {common : B1.t; base_fee : U64.t; base_fee_trend : U64.t; base_fee_moment : U64.t}
    [@@deriving yojson]

    let to_rlp _header = failwith "TODO"

    let of_rlp = function
      | Rlp.List fields -> (
        match B1.of_rlp_fields fields with
        | Some (common, []) -> Some (V1 {common})
        | Some (common, [base_fee; base_fee_trend; base_fee_moment]) ->
            Option.(
              let$ base_fee = U64.of_rlp base_fee in
              let$ base_fee_trend = U64.of_rlp base_fee_trend in
              let$ base_fee_moment = U64.of_rlp base_fee_moment in
              return (V2 {common; base_fee; base_fee_trend; base_fee_moment}) )
        | _ -> ( match B0.of_rlp_fields fields with Some (common, []) -> Some (V0 {common}) | _ -> None ) )
      | _ -> None

    let previous_id = function
      | V0 {common} -> common.qc.vote.id
      | V1 {common} | V2 {common; _} -> common.qc.vote.id

    let execution_inputs = function
      | V0 {common} -> common.execution_inputs
      | V1 {common} | V2 {common; _} -> common.execution_inputs

    let body_id = function
      | V0 {common} -> common.block_body_id
      | V1 {common} | V2 {common; _} -> common.block_body_id
  end

  module Body = struct
    type t = {transactions : Transaction.t list; ommers : Block.Header.t list; withdrawals : Withdrawal.t list}
    [@@deriving yojson]

    let decode_transaction = function
      | Rlp.List _ as rlp -> (
        match Transaction.of_rlp rlp with
        | None -> None
        | Some tx ->
            assert (Transaction.kind_tag tx = `Legacy) ;
            Some tx )
      | Rlp.Bytes bs -> Transaction.decode bs
    let to_rlp {transactions; ommers; withdrawals} =
      Rlp.List
        [ Rlp.List (List.map Transaction.to_rlp transactions)
        ; Rlp.List (List.map Block.Header.to_rlp ommers)
        ; Rlp.List (List.map Withdrawal.to_rlp withdrawals) ]
    let of_rlp = function
      | Rlp.List [List [List transactions; List ommers; List withdrawals]] ->
          Option.(
            let$ transactions = sequence (List.map decode_transaction transactions) in
            let$ ommers = sequence (List.map Block.Header.of_rlp ommers) in
            let$ withdrawals = sequence (List.map Withdrawal.of_rlp withdrawals) in
            return {transactions; ommers; withdrawals} )
      | _ -> None
  end
end

open Lens.Infix
open Host
open WorldState

type t =
  { mutable chain : WorldState.t
  ; mutable prev_chain : WorldState.t
  ; mutable last_run_blocks : Block.t list
  ; ledger_path : string
  ; chain_id : Uint.t }

let ( // ) path_1 path_2 = Filename.concat path_1 path_2

let read_file (filename : string) : Bytes.t = In_channel.with_open_bin filename In_channel.input_all

let header_subdir = "headers"
let body_subdir = "bodies"

let genesis_file = "genesis.json"
let finalized_head = "finalized_head"
let proposed_head = "proposed_head"

module Genesis = struct
  type initial_allocation = {wei_balance : U256.t} [@@deriving yojson]

  type t =
    { alloc : initial_allocation Address.Map.t
    ; coinbase : Address.t
    ; difficulty : Uint.t
    ; extra_data : Bytes.t [@key "extraData"]
    ; gas_limit : Uint.t [@key "gasLimit"]
    ; mix_hash : B32.t [@key "mixHash"]
    ; nonce : B8.t
    ; parent_hash : B32.t [@key "parentHash"]
    ; timestamp : U256.t }
  [@@deriving yojson {exn = true}]

  let to_world_state (genesis : t) : WorldState.t =
    let accounts =
      Address.Map.map (fun allocation -> {Account.empty with balance = allocation.wei_balance}) genesis.alloc
    in
    let state = {accounts; history = []; next_emptying_transaction_block = Address.Map.empty} in
    let history =
      let header =
        { Block.Header.empty with
          parent_hash = genesis.parent_hash
        ; ommers_hash = Crypto.keccak_256 Rlp.(encode (List []))
        ; beneficiary = genesis.coinbase
        ; state_root = WorldState.state_root state
        ; transactions_root = Mpt.empty.root_hash
        ; receipts_root = Mpt.empty.root_hash
        ; logs_bloom = Bloom.zeros
        ; difficulty = genesis.difficulty
        ; number = Uint.zero
        ; gas_limit = genesis.gas_limit
        ; gas_used = Uint.zero
        ; timestamp = genesis.timestamp
        ; extra_data = genesis.extra_data
        ; prev_randao = genesis.mix_hash
        ; nonce = genesis.nonce
        ; withdrawals_root = Mpt.empty.root_hash
        ; parent_beacon_block_root = Mpt.empty.root_hash
        ; requests_hash = None }
      in
      let block : Chain.Ethereum.Block.t = {header; transactions = []; ommers = []; withdrawals = []} in
      [block]
    in
    {state with history}
end

let make ~chain_id ~ledger_path =
  let chain =
    Yojson.Safe.from_file (ledger_path // genesis_file) |> Genesis.of_yojson_exn |> Genesis.to_world_state
  in
  {chain; prev_chain = chain; last_run_blocks = []; chain_id; ledger_path}

let read_consensus_header_opt (filename : string) =
  if Sys.file_exists filename then
    let header_rlp = Rlp.decode (read_file filename) in
    Some
      ( match Consensus.Header.of_rlp header_rlp with
      | Some header -> header
      | None -> failwith (Format.sprintf "Unable to decode consensus header in %s" filename) )
  else None

let read_consensus_body (filename : string) =
  let body_rlp = Rlp.decode (read_file filename) in
  match Consensus.Body.of_rlp body_rlp with
  | Some body -> body
  | None -> failwith (Format.sprintf "Unable to decode consensus body in %s" filename)

let headers_from (ledger_path : string) (head : string) : Consensus.Header.t Seq.t =
  let get_next_header header_id =
    if header_id = String.empty then None
    else
      Option.(
        let$ header = read_consensus_header_opt (ledger_path // header_subdir // header_id) in
        let prev_header_filename = B32.to_hex_string (Consensus.Header.previous_id header) in
        return (header, prev_header_filename) )
  in
  Seq.unfold get_next_header head

(* Finalized headers, starting with most recent. *)
let finalized_headers ledger_path = headers_from ledger_path finalized_head

(* Proposed headers, starting with most recent. *)
let proposed_headers ledger_path = headers_from ledger_path proposed_head

let set_balance (client : t) (addr : Address.t) (balance : U256.t) =
  client.chain <- (client.chain.^(account ~keep_empty:true addr |-- Account.balance) <- balance)

let get_balance (client : t) (addr : Address.t) = client.chain.^(account addr).balance

let get_state_root (client : t) = state_root client.chain

let run (client : t) (n_blocks : int) =
  client.prev_chain <- client.chain ;
  let current_block_number = (List.hd client.chain.history).header.number in
  let next_block_number = Uint.(current_block_number + ~$n_blocks) in
  Format.printf "Executing blocks %s to %s\n"
    (Uint.to_string Uint.(one + current_block_number))
    (Uint.to_string next_block_number) ;
  Format.print_flush () ;

  let t0 = Unix.gettimeofday () in

  let headers_to_execute =
    headers_from client.ledger_path proposed_head
    |> Seq.drop_while (fun (header : Consensus.Header.t) ->
        Uint.((Consensus.Header.execution_inputs header).number > next_block_number) )
    |> Seq.take_while (fun (header : Consensus.Header.t) ->
        Uint.((Consensus.Header.execution_inputs header).number > current_block_number) )
  in

  (* Read consensus block headers and bodies into a list of ethereum blocks in reverse order. *)
  let rec read_blocks (seq : Consensus.Header.t Seq.t) acc =
    match Seq.uncons seq with
    | None -> acc
    | Some (consensus_header, seq) ->
        let open Chain.Ethereum.Block in
        let Consensus.Body.{transactions; ommers; withdrawals} =
          read_consensus_body
            ( client.ledger_path
            // body_subdir
            // B32.to_hex_string (Consensus.Header.body_id consensus_header) )
        in
        let ethereum_block =
          {header = Consensus.Header.execution_inputs consensus_header; transactions; ommers; withdrawals}
        in
        read_blocks seq (ethereum_block :: acc)
  in
  let blocks = read_blocks headers_to_execute [] in
  if List.length blocks <> n_blocks then
    failwith
      (Format.sprintf "Could not read enough blocks. Found %d, expected %d\n" (List.length blocks) n_blocks) ;

  let module Execution = Execution.Make (struct
    let chain_id = client.chain_id
    let trace = false
  end) in
  List.iter
    (fun block ->
      let chain =
        Execution.process_block ~verify:false client.chain block
        |> Result.map_error (fun err ->
            Format.eprintf "%s\n" (Execution.Error.to_string err) ;
            err )
        |> Result.get_ok
      in
      client.chain <- chain )
    blocks ;
  let rec rev_take n acc = function
    | x :: xs when n > 0 -> rev_take (n - 1) (x :: acc) xs
    | _ -> acc
  in
  client.last_run_blocks <- rev_take n_blocks [] client.chain.history ;

  let t1 = Unix.gettimeofday () in
  let dt = (t1 -. t0) *. 1000. in
  Format.printf "Finished in %fms, %fms per block\n" dt (dt /. float_of_int n_blocks) ;
  Format.print_flush ()

let generate_test_fixture (client : t) (filename : string) =
  let network = Chain.Monad.Revision.(to_string Eight) in
  let genesis_block = List.hd client.prev_chain.history in
  let genesis_block_header = genesis_block.Block.header in
  let test_case : Fixtures.BlockchainTest.test_case =
    { info =
        { filling_rpc_server = "monad-execution-fuzzer"
        ; filling_tool_version = ""
        ; fixture_format = "blockchain_test"
        ; hash = U256.zero
        ; lllc_version = ""
        ; repo = ""
        ; solidity = ""
        ; source = "monad-execution-fuzzer"
        ; source_hash = U256.zero }
    ; blocks = client.last_run_blocks
    ; config = {blob_schedule = []; chain_id = client.chain_id; network}
    ; genesis_block_header
    ; genesis_rlp = Rlp.encode (Block.Header.to_rlp genesis_block_header)
    ; last_blockhash = U256.of_repr (Block.hash genesis_block)
    ; network
    ; pre = client.prev_chain.accounts
    ; next_emptying_transaction_block = client.prev_chain.next_emptying_transaction_block
    ; post = client.chain.accounts }
  in
  let open Fixtures in
  let fixture_json = BlockchainTest.test_case_to_yojson test_case in
  let fixture_json =
    let blocks =
      Yojson.Safe.Util.to_list fixture_json.$("blocks")
      |> List.map (fun (b : Yojson.Safe.t) ->
          let block = match Block.of_yojson b with Ok b -> b | Error err -> failwith err in
          let b = b.$("rlp") <- Bytes.to_yojson (Rlp.encode (Block.to_rlp block)) in
          let header_with_hash = b.$("blockHeader").$("hash") <- B32.to_yojson (Block.hash block) in
          b.$("blockHeader") <- header_with_hash )
    in
    fixture_json.$("blocks") <- `List blocks
  in
  let test_name = Filename.(remove_extension (basename filename)) in
  let output_json = `Assoc [(test_name, fixture_json)] in
  Out_channel.with_open_text filename (fun oc -> Yojson.Safe.pretty_to_channel oc output_json) ;
  Format.printf "Wrote test fixture to %s\n" filename ;
  Format.print_flush ()
