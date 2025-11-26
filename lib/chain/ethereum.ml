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

  type call_or_create =
    | Call of {to_ : Address.t (* T_t *); data : Bytes.t (* T_d *)}
    | Create of {init : Bytes.t (* T_i *)}

  (* YP 4.2 *)
  type kind =
    | Legacy of
        { call_or_create : call_or_create (* Either T_i or (T_t, T_d) *)
        ; gas_price : Uint.t (* T_p *)
        ; v : U256.t (* T_w *) }
    | AccessList of
        (* Type-1 transaction as specified in EIP-2930 *)
        
        { call_or_create : call_or_create (* Either T_i or (T_t, T_d) *)
        ; gas_price : Uint.t (* T_p *)
        ; access_list : Access.t list (* T_A *)
        ; chain_id : U256.t (* T_c *)
        ; y_parity : U256.t (* T_y *) }
    | FeeMarket of
        (* Type-2 transaction as specified in EIP-1559 *)
        
        { call_or_create : call_or_create (* Either T_i or (T_t, T_d) *)
        ; max_fee_per_gas : Uint.t (* T_m *)
        ; max_priority_fee_per_gas : Uint.t (* T_f *)
        ; access_list : Access.t list (* T_A *)
        ; chain_id : U256.t (* T_c *)
        ; y_parity : U256.t (* T_y *) }
    | Blob of
        (* Blob transaction as specified in EIP-4844 *)
        
        { to_ : Address.t (* T_t *)
        ; data : Bytes.t (* T_d *)
        ; max_fee_per_gas : Uint.t (* T_m *)
        ; max_priority_fee_per_gas : Uint.t (* T_f *)
        ; access_list : Access.t list (* T_A *)
        ; max_fee_per_blob_gas : U256.t (* EIP-4844 *)
        ; blob_versioned_hashes : U256.t list (* EIP-4844 *)
        ; chain_id : U256.t (* T_c *)
        ; y_parity : U256.t (* T_y *) }
  type t =
    { nonce : U256.t (* T_n *)
    ; gas_limit : Uint.t (* T_g *)
    ; value : U256.t (* T_v *)
    ; r : U256.t (* T_r *)
    ; s : U256.t (* T_s *)
    ; kind : kind }

  type kind_tag = [`Legacy | `AccessList | `FeeMarket | `Blob]
  let kind_tag txn : kind_tag =
    match txn.kind with
    | Legacy _ -> `Legacy
    | AccessList _ -> `AccessList
    | FeeMarket _ -> `FeeMarket
    | Blob _ -> `Blob

  let call_or_create txn =
    match txn.kind with
    | Legacy {call_or_create; _} | AccessList {call_or_create; _} | FeeMarket {call_or_create; _} ->
        call_or_create
    | Blob {to_; data; _} -> Call {to_; data}
  let data_or_initcode = function Call {data; _} -> data | Create {init} -> init

  type fee_mechanism =
    | LegacyFee of {gas_price : Uint.t}
    | FeeMarketFee of {max_fee_per_gas : Uint.t; max_priority_fee_per_gas : Uint.t}
  let fee_mechanism (txn : t) =
    match txn.kind with
    | Legacy {gas_price; _} | AccessList {gas_price; _} -> LegacyFee {gas_price}
    | FeeMarket {max_fee_per_gas; max_priority_fee_per_gas; _}
     |Blob {max_fee_per_gas; max_priority_fee_per_gas; _} ->
        FeeMarketFee {max_fee_per_gas; max_priority_fee_per_gas}

  let signing_hash chain_id txn =
    let to_, data =
      match call_or_create txn with Call {to_; data} -> (to_, data) | Create {init} -> (Address.zero, init)
    in
    let bytes =
      match txn.kind with
      | Legacy {gas_price; v; _} when U256.(v = ~$27 || v = ~$28) ->
          (* Pre EIP-155 transaction *)
          Rlp.encode
            (Rlp.List
               [ U256.to_rlp txn.nonce
               ; Uint.to_rlp gas_price
               ; Uint.to_rlp txn.gas_limit
               ; Address.to_rlp to_
               ; U256.to_rlp txn.value
               ; Rlp.Bytes data ] )
      | Legacy {gas_price; _} ->
          (* EIP-155 transaction *)
          Rlp.encode
            (Rlp.List
               [ U256.to_rlp txn.nonce
               ; Uint.to_rlp gas_price
               ; Uint.to_rlp txn.gas_limit
               ; Address.to_rlp to_
               ; U256.to_rlp txn.value
               ; Rlp.Bytes data
               ; Uint.to_rlp chain_id
               ; U256.(to_rlp zero)
               ; U256.(to_rlp zero) ] )
      | AccessList {gas_price; access_list; _} ->
          (* EIP-2930 *)
          "\x01"
          ^ Rlp.encode
              (Rlp.List
                 [ Uint.to_rlp chain_id
                 ; U256.to_rlp txn.nonce
                 ; Uint.to_rlp gas_price
                 ; Uint.to_rlp txn.gas_limit
                 ; Address.to_rlp to_
                 ; U256.to_rlp txn.value
                 ; Rlp.Bytes data
                 ; Rlp.List (List.map Access.to_rlp access_list) ] )
      | FeeMarket {max_priority_fee_per_gas; max_fee_per_gas; access_list; _} ->
          (* EIP-1559 *)
          "\x02"
          ^ Rlp.encode
              (Rlp.List
                 [ Uint.to_rlp chain_id
                 ; U256.to_rlp txn.nonce
                 ; Uint.to_rlp max_priority_fee_per_gas
                 ; Uint.to_rlp max_fee_per_gas
                 ; Uint.to_rlp txn.gas_limit
                 ; Address.to_rlp to_
                 ; U256.to_rlp txn.value
                 ; Rlp.Bytes data
                 ; Rlp.List (List.map Access.to_rlp access_list) ] )
      | Blob
          { max_priority_fee_per_gas
          ; max_fee_per_gas
          ; access_list
          ; max_fee_per_blob_gas
          ; blob_versioned_hashes
          ; _ } ->
          (* EIP-4844 *)
          "\x03"
          ^ Rlp.encode
              (Rlp.List
                 [ Uint.to_rlp chain_id
                 ; U256.to_rlp txn.nonce
                 ; Uint.to_rlp max_priority_fee_per_gas
                 ; Uint.to_rlp max_fee_per_gas
                 ; Uint.to_rlp txn.gas_limit
                 ; Address.to_rlp to_
                 ; U256.to_rlp txn.value
                 ; Rlp.Bytes data
                 ; Rlp.List (List.map Access.to_rlp access_list)
                 ; U256.to_rlp max_fee_per_blob_gas
                 ; Rlp.List (List.map U256.to_rlp blob_versioned_hashes) ] )
    in
    Crypto.keccak_256 bytes

  let sender (chain_id : Uint.t) ({r; s; kind; _} as txn : t) =
    assert (U256.(r > zero && r < Crypto.secp256k1n)) ;
    assert (U256.(s > zero && s < Crypto.secp256k1n / ~$2)) ;
    let y_parity =
      match kind with
      | Legacy {v; _} -> if U256.(v = ~$27 || v = ~$28) then U256.(v - ~$27) else failwith "TODO"
      | AccessList {y_parity; _} | FeeMarket {y_parity; _} | Blob {y_parity; _} -> y_parity
    in
    let public_key = Crypto.secp256k1_recover r s y_parity (signing_hash chain_id txn) in
    Address.of_bytes_be (Bytes.sub (U256.to_bytes_be (Crypto.keccak_256 public_key)) 12 (32 - 12))

  let access_list txn =
    match txn.kind with
    | Legacy _ -> []
    | AccessList {access_list; _} | FeeMarket {access_list; _} | Blob {access_list; _} -> access_list

  let ( .$() ) obj k = Yojson.Safe.Util.member k obj

  let call_or_create_of_yojson (json : Yojson.Safe.t) =
    Result.(
      let$ to_ = Address.of_yojson json.$("to") in
      let$ data = Bytes.of_yojson json.$("data") in
      return (if to_ = Address.zero then Create {init = data} else Call {to_; data}) )

  let legacy_of_yojson (json : Yojson.Safe.t) : (kind, string) result =
    Result.(
      let$ call_or_create = call_or_create_of_yojson json in
      let$ gas_price = Uint.of_yojson json.$("gasPrice") in
      let$ v = U256.of_yojson json.$("v") in
      return (Legacy {call_or_create; gas_price; v}) )
  let access_list_of_yojson (json : Yojson.Safe.t) =
    Result.(
      let$ call_or_create = call_or_create_of_yojson json in
      let$ gas_price = Uint.of_yojson json.$("gasPrice") in
      let$ access_list = [%of_yojson: Access.t list] json.$("accessList") in
      let$ chain_id = U256.of_yojson json.$("chainId") in
      let$ y_parity = U256.of_yojson json.$("v") in
      return (AccessList {call_or_create; gas_price; access_list; chain_id; y_parity}) )
  let fee_market_of_yojson (json : Yojson.Safe.t) =
    Result.(
      let$ call_or_create = call_or_create_of_yojson json in
      let$ max_fee_per_gas = Uint.of_yojson json.$("maxFeePerGas") in
      let$ max_priority_fee_per_gas = Uint.of_yojson json.$("maxPriorityFeePerGas") in
      let$ access_list = [%of_yojson: Access.t list] json.$("accessList") in
      let$ chain_id = U256.of_yojson json.$("chainId") in
      let$ y_parity = U256.of_yojson json.$("v") in
      return
        (FeeMarket {call_or_create; max_fee_per_gas; max_priority_fee_per_gas; access_list; chain_id; y_parity}
        ) )
  let blob_of_yojson (json : Yojson.Safe.t) =
    Result.(
      let$ call_or_create = call_or_create_of_yojson json in
      let$ data, to_ =
        match call_or_create with Call {data; to_} -> return (data, to_) | Create _ -> fail "kind.to_"
      in
      let$ max_fee_per_gas = Uint.of_yojson json.$("maxFeePerGas") in
      let$ max_priority_fee_per_gas = Uint.of_yojson json.$("maxPriorityFeePerGas") in
      let$ max_fee_per_blob_gas = U256.of_yojson json.$("maxFeePerBlobGas") in
      let$ blob_versioned_hashes = return [] in
      let$ access_list = [%of_yojson: Access.t list] json.$("accessList") in
      let$ chain_id = U256.of_yojson json.$("chainId") in
      let$ y_parity = U256.of_yojson json.$("v") in
      return
        (Blob
           { data
           ; to_
           ; max_fee_per_gas
           ; max_priority_fee_per_gas
           ; max_fee_per_blob_gas
           ; access_list
           ; chain_id
           ; y_parity
           ; blob_versioned_hashes } ) )

  let of_yojson (json : Yojson.Safe.t) =
    Result.(
      let$ kind =
        match json.$("type") with
        | `Null -> legacy_of_yojson json
        | `String "0x01" -> access_list_of_yojson json
        | `String "0x02" -> fee_market_of_yojson json
        | `String "0x03" -> blob_of_yojson json
        | invalid ->
            Error (Format.sprintf "Not a valid transaction type: %s" (Yojson.Safe.pretty_to_string invalid))
      in
      let$ nonce = U256.of_yojson json.$("nonce") in
      let$ gas_limit = Uint.of_yojson json.$("gasLimit") in
      let$ value = U256.of_yojson json.$("value") in
      let$ r = U256.of_yojson json.$("r") in
      let$ s = U256.of_yojson json.$("s") in
      return {nonce; gas_limit; value; r; s; kind} )

  let to_yojson (_tx : t) : Yojson.Safe.t = failwith "TODO"
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
    [@@deriving yojson]
  end

  (* YP 4.4 (23) *)
  type t =
    { header : Header.t (* B_H *) [@key "blockHeader"]
    ; transactions : Transaction.t list (* B_T *) [@key "transactions"]
    ; ommers : Header.t list (* B_U *) [@key "uncleHeaders"]
    ; withdrawals : Withdrawal.t list (* B_W *) [@key "withdrawals"] }
  [@@deriving yojson]
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
