(** Definitions for Ethereum types: accounts, blocks, transactions.
    Work in progress, will be expanded as needed. *)
open Numeric

module Address = struct
  include U160

  type create2_params = {salt : U256.t; code : Bytes.t}

  (* YP (95) *)
  let of_contract_creation ~sender ~nonce ~create2 =
    of_u256_truncating
      (Crypto.keccak_256
         ( match create2 with
         | None -> Rlp.(encode (List [to_rlp sender; Uint.to_rlp nonce]))
         | Some {salt; code} ->
             Bytes.make 1 '\xff'
             ^ to_bytes_be sender
             ^ U256.to_bytes_be salt
             ^ U256.to_bytes_be (Crypto.keccak_256 code) ) )
end

module Revision = struct
  type t =
    (* The Frontier revision.
       The one Ethereum launched with. *)
    | Frontier
    (* The Homestead revision.
       https://eips.ethereum.org/EIPS/eip-606 *)
    | Homestead
    (* The Tangerine Whistle revision.
       https://eips.ethereum.org/EIPS/eip-608 *)
    | TangerineWhistle
    (*       The Spurious Dragon revision.
       https://eips.ethereum.org/EIPS/eip-607 *)
    | SpuriousDragon
    (* The Byzantium revision.
       https://eips.ethereum.org/EIPS/eip-609 *)
    | Byzantium
    (* The Constantinople revision.
       https://eips.ethereum.org/EIPS/eip-1013 *)
    | Constantinople
    (* The Petersburg revision.
       Other names: Constantinople2, ConstantinopleFix.
       https://eips.ethereum.org/EIPS/eip-1716 *)
    | Petersburg
    (* The Istanbul revision.
       https://eips.ethereum.org/EIPS/eip-1679 *)
    | Istanbul
    (* The Berlin revision.
       https://github.com/ethereum/execution-specs/blob/master/network-upgrades/mainnet-upgrades/berlin.md *)
    | Berlin
    (* The London revision.
       https://github.com/ethereum/execution-specs/blob/master/network-upgrades/mainnet-upgrades/london.md *)
    | London
    (* The Paris revision (aka The Merge).
       https://github.com/ethereum/execution-specs/blob/master/network-upgrades/mainnet-upgrades/paris.md *)
    | Paris
    (* The Shanghai revision.
       https://github.com/ethereum/execution-specs/blob/master/network-upgrades/mainnet-upgrades/shanghai.md *)
    | Shanghai
    (* The Cancun revision.
       https://github.com/ethereum/execution-specs/blob/master/network-upgrades/mainnet-upgrades/cancun.md *)
    | Cancun
    (* The Prague / Pectra revision.
       https://eips.ethereum.org/EIPS/eip-7600 *)
    | Prague
    (* The Osaka / Fusaka revision.
       https://eips.ethereum.org/EIPS/eip-7607 *)
    | Osaka
    (* The unspecified EVM revision used for EVM implementations to expose
       experimental features. *)
    | Experimental
end

module Transaction = struct
  module Access = struct
    type t = {address : Address.t (* E_a *); storage_keys : U256.t list [@tag "storageKeys"] (* E_s *)}
    [@@deriving yojson]

    let to_rlp {address; storage_keys} =
      Rlp.List [Address.to_rlp address; Rlp.List (List.map U256.to_rlp storage_keys)]
  end

  (* YP 4.2 *)
  type legacy_tx =
    { nonce : U256.t (* T_n *)
    ; gas_limit : Uint.t (* T_g *) [@key "gasLimit"]
    ; value : U256.t (* T_v *)
    ; r : U256.t (* T_r *)
    ; s : U256.t (* T_s *)
    ; to_ : Address.t (* T_t *) [@key "to"]
    ; data : Bytes.t (* Either T_d or T_i *)
    ; gas_price : Uint.t (* T_p *) [@key "gasPrice"]
    ; v : U256.t (* T_w *) }
  [@@deriving yojson {strict = false}]
  type access_list_tx =
    { nonce : U256.t (* T_n *)
    ; gas_limit : Uint.t (* T_g *) [@key "gasLimit"]
    ; value : U256.t (* T_v *)
    ; r : U256.t (* T_r *)
    ; s : U256.t (* T_s *)
    ; to_ : Address.t (* T_t *) [@key "to"]
    ; data : Bytes.t (* Either T_d or T_i *)
    ; gas_price : Uint.t (* T_p *) [@key "gasPrice"]
    ; access_list : Access.t list (* T_A *) [@key "accessList"]
    ; chain_id : Uint.t (* T_c *) [@key "chainId"]
    ; y_parity : U256.t (* T_y *) [@key "v"] }
  [@@deriving yojson {strict = false}]
  type fee_market_tx =
    { nonce : U256.t (* T_n *)
    ; gas_limit : Uint.t (* T_g *) [@key "gasLimit"]
    ; value : U256.t (* T_v *)
    ; r : U256.t (* T_r *)
    ; s : U256.t (* T_s *)
    ; to_ : Address.t (* T_t *) [@key "to"]
    ; data : Bytes.t (* Either T_d or T_i *)
    ; max_fee_per_gas : Uint.t (* T_m *) [@key "maxFeePerGas"]
    ; max_priority_fee_per_gas : Uint.t (* T_f *) [@key "maxPriorityFeePerGas"]
    ; access_list : Access.t list (* T_A *) [@key "accessList"]
    ; chain_id : Uint.t (* T_c *) [@key "chainId"]
    ; y_parity : U256.t (* T_y *) [@key "v"] }
  [@@deriving yojson {strict = false}]
  type blob_tx =
    { nonce : U256.t (* T_n *)
    ; gas_limit : Uint.t (* T_g *) [@key "gasLimit"]
    ; value : U256.t (* T_v *)
    ; r : U256.t (* T_r *)
    ; s : U256.t (* T_s *)
    ; to_ : Address.t (* T_t *) [@key "to"]
    ; data : Bytes.t (* T_d *)
    ; max_fee_per_gas : Uint.t (* T_m *) [@key "maxFeePerGas"]
    ; max_priority_fee_per_gas : Uint.t (* T_f *) [@key "maxPriorityFeePerGas"]
    ; access_list : Access.t list (* T_A *) [@key "accessList"]
    ; chain_id : Uint.t (* T_c *) [@key "chainId"]
    ; y_parity : U256.t (* T_y *) [@key "v"]
    ; max_fee_per_blob_gas : U256.t (* EIP-4844 *) [@key "maxFeePerBlobGas"]
    ; blob_versioned_hashes : U256.t list (* EIP-4844 *) [@key "blobVersionedHashes"] }
  [@@deriving yojson {strict = false}]
  type t = Legacy of legacy_tx | AccessList of access_list_tx | FeeMarket of fee_market_tx | Blob of blob_tx

  let of_yojson (json : Yojson.Safe.t) : (t, string) result =
    Result.(
      (* Ethereum text fixtures encode numeric values as hex strings, but yojson assumes primitive number types
         are encoded directly as numbers, so we read the input as a U64.t, then unpack it into an int to pattern
         match on it. *)
      match Option.map U64.to_int <$> [%of_yojson: U64.t option] (Yojson.Safe.Util.member "type" json) with
      | Ok None -> [%of_yojson: legacy_tx] json >>= fun tx -> return (Legacy tx)
      | Ok (Some 1) -> [%of_yojson: access_list_tx] json >>= fun tx -> return (AccessList tx)
      | Ok (Some 2) -> [%of_yojson: fee_market_tx] json >>= fun tx -> return (FeeMarket tx)
      | Ok (Some 3) -> [%of_yojson: blob_tx] json >>= fun tx -> return (Blob tx)
      | Ok _ | Error _ -> fail "Ethereum.Transaction.t" )

  let to_yojson (tx : t) : Yojson.Safe.t =
    match tx with
    | Legacy tx -> [%to_yojson: legacy_tx] tx
    | AccessList tx -> [%to_yojson: access_list_tx] tx
    | FeeMarket tx -> [%to_yojson: fee_market_tx] tx
    | Blob tx -> [%to_yojson: blob_tx] tx

  type kind_tag = [`Legacy | `AccessList | `FeeMarket | `Blob]
  let kind_tag tx : kind_tag =
    match tx with
    | Legacy _ -> `Legacy
    | AccessList _ -> `AccessList
    | FeeMarket _ -> `FeeMarket
    | Blob _ -> `Blob

  let to_ tx =
    match tx with Legacy {to_; _} | AccessList {to_; _} | FeeMarket {to_; _} | Blob {to_; _} -> to_

  let nonce tx =
    match tx with
    | Legacy {nonce; _} | AccessList {nonce; _} | FeeMarket {nonce; _} | Blob {nonce; _} -> nonce

  let data tx =
    match tx with Legacy {data; _} | AccessList {data; _} | FeeMarket {data; _} | Blob {data; _} -> data

  let value tx =
    match tx with
    | Legacy {value; _} | AccessList {value; _} | FeeMarket {value; _} | Blob {value; _} -> value

  let gas_limit tx =
    match tx with
    | Legacy {gas_limit; _} | AccessList {gas_limit; _} | FeeMarket {gas_limit; _} | Blob {gas_limit; _} ->
        gas_limit

  type signature = {r : U256.t; s : U256.t}
  let signature tx =
    match tx with Legacy {r; s; _} | AccessList {r; s; _} | FeeMarket {r; s; _} | Blob {r; s; _} -> {r; s}

  type fee_mechanism =
    | LegacyFee of {gas_price : Uint.t}
    | FeeMarketFee of {max_fee_per_gas : Uint.t; max_priority_fee_per_gas : Uint.t}
  let fee_mechanism (tx : t) =
    match tx with
    | Legacy {gas_price; _} | AccessList {gas_price; _} -> LegacyFee {gas_price}
    | FeeMarket {max_fee_per_gas; max_priority_fee_per_gas; _}
     |Blob {max_fee_per_gas; max_priority_fee_per_gas; _} ->
        FeeMarketFee {max_fee_per_gas; max_priority_fee_per_gas}

  let signing_hash chain_id tx =
    let bytes =
      match tx with
      | Legacy tx when U256.(tx.v = ~$27 || tx.v = ~$28) ->
          (* Pre EIP-155 transaction *)
          Rlp.encode
            (Rlp.List
               [ U256.to_rlp tx.nonce
               ; Uint.to_rlp tx.gas_price
               ; Uint.to_rlp tx.gas_limit
               ; Address.to_rlp tx.to_
               ; U256.to_rlp tx.value
               ; Rlp.Bytes tx.data ] )
      | Legacy tx ->
          (* EIP-155 transaction *)
          Rlp.encode
            (Rlp.List
               [ U256.to_rlp tx.nonce
               ; Uint.to_rlp tx.gas_price
               ; Uint.to_rlp tx.gas_limit
               ; Address.to_rlp tx.to_
               ; U256.to_rlp tx.value
               ; Rlp.Bytes tx.data
               ; Uint.to_rlp chain_id
               ; U256.(to_rlp zero)
               ; U256.(to_rlp zero) ] )
      | AccessList tx ->
          assert (Uint.(tx.chain_id = chain_id)) ;
          (* EIP-2930 *)
          "\x01"
          ^ Rlp.encode
              (Rlp.List
                 [ Uint.to_rlp chain_id
                 ; U256.to_rlp tx.nonce
                 ; Uint.to_rlp tx.gas_price
                 ; Uint.to_rlp tx.gas_limit
                 ; Address.to_rlp tx.to_
                 ; U256.to_rlp tx.value
                 ; Rlp.Bytes tx.data
                 ; Rlp.List (List.map Access.to_rlp tx.access_list) ] )
      | FeeMarket tx ->
          assert (Uint.(tx.chain_id = chain_id)) ;
          (* EIP-1559 *)
          "\x02"
          ^ Rlp.encode
              (Rlp.List
                 [ Uint.to_rlp chain_id
                 ; U256.to_rlp tx.nonce
                 ; Uint.to_rlp tx.max_priority_fee_per_gas
                 ; Uint.to_rlp tx.max_fee_per_gas
                 ; Uint.to_rlp tx.gas_limit
                 ; Address.to_rlp tx.to_
                 ; U256.to_rlp tx.value
                 ; Rlp.Bytes tx.data
                 ; Rlp.List (List.map Access.to_rlp tx.access_list) ] )
      | Blob tx ->
          assert (Uint.(tx.chain_id = chain_id)) ;
          (* EIP-4844 *)
          "\x03"
          ^ Rlp.encode
              (Rlp.List
                 [ Uint.to_rlp chain_id
                 ; U256.to_rlp tx.nonce
                 ; Uint.to_rlp tx.max_priority_fee_per_gas
                 ; Uint.to_rlp tx.max_fee_per_gas
                 ; Uint.to_rlp tx.gas_limit
                 ; Address.to_rlp tx.to_
                 ; U256.to_rlp tx.value
                 ; Rlp.Bytes tx.data
                 ; Rlp.List (List.map Access.to_rlp tx.access_list)
                 ; U256.to_rlp tx.max_fee_per_blob_gas
                 ; Rlp.List (List.map U256.to_rlp tx.blob_versioned_hashes) ] )
    in
    Crypto.keccak_256 bytes

  let sender (chain_id : Uint.t) (tx : t) =
    let {r; s} = signature tx in
    assert (U256.(r > zero && r < Crypto.secp256k1n)) ;
    assert (U256.(s > zero && s < Crypto.secp256k1n / ~$2)) ;
    let y_parity =
      match tx with
      | Legacy {v; _} ->
          if U256.(v = ~$27 || v = ~$28) then U256.(v - ~$27)
          else (* EIP-155 *) U256.(v - ~$35 - (~$2 * U256.of_unbounded_exn chain_id))
      | AccessList {y_parity; _} | FeeMarket {y_parity; _} | Blob {y_parity; _} -> y_parity
    in
    assert (U256.(y_parity <= ~$1)) ;
    let public_key = Crypto.secp256k1_recover r s y_parity (signing_hash chain_id tx) in
    Address.of_bytes_be (Bytes.sub (U256.to_bytes_be (Crypto.keccak_256 public_key)) 12 (32 - 12))

  let access_list tx =
    match tx with
    | Legacy _ -> []
    | AccessList {access_list; _} | FeeMarket {access_list; _} | Blob {access_list; _} -> access_list

  type call_or_create =
    | Call of {data : Bytes.t (* T_d *); to_ : Address.t (* T_t *)}
    | Create of {initcode : Bytes.t (* T_i *)}
  let call_or_create tx =
    let to_ = to_ tx in
    let data = data tx in
    if Address.(to_ = zero) then Create {initcode = data} else Call {data; to_}
end

module Withdrawal = struct
  (* YP 4.3 *)
  type t =
    { global_index : U64.t [@tag "index"] (* W_g *)
    ; validator_index : U64.t [@tag "validatorIndex"] (* W_v *)
    ; recipient : Address.t [@tag "address"] (* W_r *)
    ; amount : U256.t [@tag "amount"] (* W_a *) }
  [@@deriving yojson]
end

module Block = struct
  module Header = struct
    (* YP 4.4 *)
    type t =
      { parent_hash : U256.t (* H_p *) [@key "parentHash"]
      ; ommers_hash : U256.t (* H_o *) [@key "uncleHash"]
      ; beneficiary : Address.t (* H_c *) [@key "coinbase"]
      ; state_root : U256.t (* H_r *) [@key "stateRoot"]
      ; transactions_root : U256.t (* H_t *) [@key "transactionsTrie"]
      ; receipts_root : U256.t (* H_e *) [@key "receiptTrie"]
      ; logs_bloom : Bloom.t (* H_b *) [@key "bloom"]
      ; difficulty : Uint.t (* H_d *) [@key "difficulty"]
      ; number : Uint.t (* H_i *) [@key "number"]
      ; gas_limit : Uint.t (* H_l *) [@key "gasLimit"]
      ; gas_used : Uint.t (* H_g *) [@key "gasUsed"]
      ; timestamp : U256.t (* H_s *) [@key "timestamp"]
      ; extra_data : Bytes.t (* H_x *) [@key "extraData"]
      ; prev_randao : U256.t (* H_a *) [@key "mixHash"]
      ; nonce : U64.t (* H_n *) [@key "nonce"]
      ; base_fee_per_gas : Uint.t (* H_f *) [@key "baseFeePerGas"]
      ; withdrawals_root : U256.t (* H_w *) [@key "withdrawalsRoot"]
      ; blob_gas_used : U64.t (* EIP-4844 *) [@key "blobGasUsed"]
      ; excess_blob_gas : U64.t (* EIP-4844 *) [@key "excessBlobGas"]
      ; parent_beacon_block_root : U256.t (* EIP-4788 *) [@key "parentBeaconBlockRoot"]
      ; requests_hash : U256.t (* EIP-7685 *) [@key "requestsHash"] }
    [@@deriving yojson {strict = false (* Additional fields in Ethereum test fixtures: hash *)}]
  end

  (* YP 4.4 (23) *)
  type t =
    { header : Header.t (* B_H *) [@key "blockHeader"]
    ; transactions : Transaction.t list (* B_T *) [@key "transactions"]
    ; ommers : Header.t list (* B_U *) [@key "uncleHeaders"]
    ; withdrawals : Withdrawal.t list (* B_W *) [@key "withdrawals"] }
  [@@deriving yojson {strict = false (* Additional fields in Ethereum test fixtures: chainname, rlp *)}]
end

module Log = struct
  (* YP 4.4.1 (28) *)
  type t = {address : Address.t (* O_a *); topics : U256.t list (* O_t *); data : Bytes.t (* O_d *)}

  let to_bloom (log : t) : Bloom.t =
    let entries = U160.to_u256 log.address :: log.topics in
    List.fold_left
      (fun bloom entry -> Bloom.(logor bloom (of_bytes (U256.to_bytes_be entry))))
      Bloom.zeros entries
end

module Receipt = struct
  (* YP 4.4.1. *)
  type t =
    { tx_type : Transaction.kind_tag (* R_x *)
    ; succeeded : bool (* R_z *)
    ; cumulative_gas_used : Uint.t (* R_u *)
    ; bloom : Bloom.t (* R_b *)
    ; logs : Log.t list (* R_l *) }
end

module Account = struct
  type t =
    { nonce : Uint.t (* σ[a]_n *)
    ; balance : U256.t (* σ[a]_b *)
    ; storage : U256.t U256.Map.t (* σ[a]_s *)
    ; code : Bytes.t (* σ[a]_c *) }
  [@@deriving lens {submodule = true; prefix = true}, yojson]
  include TLens

  let empty = {balance = U256.zero; storage = U256.Map.empty; code = Bytes.empty; nonce = Uint.zero}
end
