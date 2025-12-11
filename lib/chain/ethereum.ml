(** Definitions for Ethereum types: accounts, blocks, transactions.
    Work in progress, will be expanded as needed. *)
open Numeric

open Byte_string

module Address = struct
  include B20

  let zero = init (fun _ -> '\x00')

  let to_rlp (addr : t) = Rlp.Bytes (to_bytes addr)

  (* Frequently used in the VM to read and write addresses (Bytes.B20.t) as stack elements (U256.t). *)
  let of_u256_truncating (x : U256.t) : t = of_bytes32_truncating (U256.to_repr x)
  let to_u256 (addr : t) = U256.of_repr (to_bytes32 addr)

  type create2_params = {salt : B32.t; code : Bytes.t}

  (* YP (95) *)
  let of_contract_creation ~(sender : t) ~nonce ~create2 =
    of_bytes32_truncating
      (Crypto.keccak_256
         ( match create2 with
         | None -> Rlp.(encode (List [to_rlp sender; U256.to_rlp nonce]))
         | Some {salt; code} ->
             Bytes.(
               of_char '\xff'
               ^ B20.to_bytes sender
               ^ B32.to_bytes salt
               ^ B32.to_bytes (Crypto.keccak_256 code) ) ) )
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
    type t = {address : Address.t (* E_a *); storage_keys : B32.t list [@tag "storageKeys"] (* E_s *)}
    [@@deriving yojson]

    let to_rlp {address; storage_keys} =
      Rlp.List [Address.to_rlp address; Rlp.List (List.map Rlp.of_bytes32 storage_keys)]
  end

  module Authorization = struct
    type t = {chain_id : U256.t; nonce : U64.t; address : Address.t; y_parity : U8.t; r : U256.t; s : U256.t}
    [@@deriving yojson]

    let to_rlp {chain_id; nonce; address; y_parity; r; s} =
      Rlp.List
        [ U256.to_rlp chain_id
        ; U64.to_rlp nonce
        ; Address.to_rlp address
        ; U8.to_rlp y_parity
        ; U256.to_rlp r
        ; U256.to_rlp s ]

    (** Recover the authority address from an EIP-7702 authorization entry. *)
    let authority ({y_parity; r; s; chain_id; address; nonce} : t) : Address.t option =
      let auth_hash =
        Crypto.keccak_256 Rlp.(encode (List [U256.to_rlp chain_id; Address.to_rlp address; U64.to_rlp nonce]))
      in
      Option.(
        let$ () = ensure U256.(zero < r && r < Crypto.secp256k1n) in
        let$ () = ensure U256.(zero < s && s < Crypto.secp256k1n / ~$2) in
        Crypto.ecrecover {y_parity; r; s} auth_hash )
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
    ; y_parity : U8.t (* T_y *) [@key "v"] }
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
    ; y_parity : U8.t (* T_y *) [@key "v"] }
  [@@deriving yojson {strict = false}]

  (** EIP-7702 transaction. *)
  type set_code_tx =
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
    ; authorization_list : Authorization.t list [@key "authorizationList"]
    ; chain_id : Uint.t (* T_c *) [@key "chainId"]
    ; y_parity : U8.t (* T_y *) [@key "v"] }
  [@@deriving yojson {strict = false}]

  type t =
    | Legacy of legacy_tx
    | AccessList of access_list_tx
    | FeeMarket of fee_market_tx
    | SetCode of set_code_tx

  type kind_tag = [`Legacy | `AccessList | `FeeMarket | `SetCode]
  let kind_tag tx : kind_tag =
    match tx with
    | Legacy _ -> `Legacy
    | AccessList _ -> `AccessList
    | FeeMarket _ -> `FeeMarket
    | SetCode _ -> `SetCode

  let kind_tag_to_bytes : kind_tag -> Bytes.t = function
    | `Legacy -> Bytes.of_char '\x00'
    | `AccessList -> Bytes.of_char '\x01'
    | `FeeMarket -> Bytes.of_char '\x02'
    | `SetCode -> Bytes.of_char '\x04'

  let byte_to_kind_tag : char -> kind_tag option = function
    | '\x00' -> Some `Legacy
    | '\x01' -> Some `AccessList
    | '\x02' -> Some `FeeMarket
    | '\x04' -> Some `SetCode
    | _ -> None

  let kind_tag_to_yojson (tag : kind_tag) : Yojson.Safe.t =
    let bytestring = Format.sprintf "0x%s" (Bytes.to_hex_string (kind_tag_to_bytes tag)) in
    `String bytestring
  let kind_tag_of_yojson (json : Yojson.Safe.t) : (kind_tag, string) result =
    Result.(
      match U64.(to_int <$> of_yojson json) with
      | Ok i when i >= 0 && i < 256 -> (
        match byte_to_kind_tag (Char.unsafe_chr i) with
        | Some tag -> return tag
        | None -> fail "Ethereum.Transaction.kind_tag" )
      | _ -> fail "Ethereum.Transaction.kind_tag" )

  let of_yojson (json : Yojson.Safe.t) : (t, string) result =
    Result.(
      (* Ethereum text fixtures encode numeric values as hex strings, but yojson assumes primitive number types
         are encoded directly as numbers, so we read the input as a U64.t, then unpack it into an int to pattern
         match on it. *)
      match Option.map U64.to_int <$> [%of_yojson: U64.t option] (Yojson.Safe.Util.member "type" json) with
      | Ok None -> [%of_yojson: legacy_tx] json >>= fun tx -> return (Legacy tx)
      | Ok (Some 1) -> [%of_yojson: access_list_tx] json >>= fun tx -> return (AccessList tx)
      | Ok (Some 2) -> [%of_yojson: fee_market_tx] json >>= fun tx -> return (FeeMarket tx)
      | Ok (Some 4) -> [%of_yojson: set_code_tx] json >>= fun tx -> return (SetCode tx)
      | Ok _ | Error _ -> fail "Ethereum.Transaction.t" )

  let to_yojson (tx : t) : Yojson.Safe.t =
    let untagged_tx =
      match tx with
      | Legacy tx -> [%to_yojson: legacy_tx] tx
      | AccessList tx -> [%to_yojson: access_list_tx] tx
      | FeeMarket tx -> [%to_yojson: fee_market_tx] tx
      | SetCode tx -> [%to_yojson: set_code_tx] tx
    in
    (* For non-legacy transactions, add the transaction type back in. *)
    match kind_tag tx with
    | `Legacy -> untagged_tx
    | tag -> `Assoc (("type", kind_tag_to_yojson tag) :: Yojson.Safe.Util.to_assoc untagged_tx)

  let to_ tx =
    match tx with Legacy {to_; _} | AccessList {to_; _} | FeeMarket {to_; _} | SetCode {to_; _} -> to_

  let nonce tx =
    match tx with
    | Legacy {nonce; _} | AccessList {nonce; _} | FeeMarket {nonce; _} | SetCode {nonce; _} -> nonce

  let data tx =
    match tx with Legacy {data; _} | AccessList {data; _} | FeeMarket {data; _} | SetCode {data; _} -> data

  let value tx =
    match tx with
    | Legacy {value; _} | AccessList {value; _} | FeeMarket {value; _} | SetCode {value; _} -> value

  let gas_limit tx =
    match tx with
    | Legacy {gas_limit; _} | AccessList {gas_limit; _} | FeeMarket {gas_limit; _} | SetCode {gas_limit; _} ->
        gas_limit

  let signature chain_id tx =
    match tx with
    | AccessList {r; s; y_parity; _} | FeeMarket {r; s; y_parity; _} | SetCode {r; s; y_parity; _} ->
        Crypto.{r; s; y_parity}
    | Legacy {r; s; v; _} ->
        let y_parity =
          if U256.(v = ~$27) then U8.zero
          else if U256.(v = ~$28) then U8.one
          else
            let parity = U256.(v - ~$35 - (~$2 * U256.of_uint_exn chain_id)) in
            if U256.(parity = zero) then U8.zero else if U256.(parity = one) then U8.one else assert false
        in
        Crypto.{r; s; y_parity}

  type fee_mechanism =
    | LegacyFee of {gas_price : Uint.t}
    | FeeMarketFee of {max_fee_per_gas : Uint.t; max_priority_fee_per_gas : Uint.t}
  let fee_mechanism (tx : t) =
    match tx with
    | Legacy {gas_price; _} | AccessList {gas_price; _} -> LegacyFee {gas_price}
    | FeeMarket {max_fee_per_gas; max_priority_fee_per_gas; _}
     |SetCode {max_fee_per_gas; max_priority_fee_per_gas; _} ->
        FeeMarketFee {max_fee_per_gas; max_priority_fee_per_gas}

  (* YP (16). Note that this is different to the encoding used by the signing hash function below. *)
  let to_rlp tx =
    match tx with
    | Legacy tx ->
        Rlp.List
          [ U256.to_rlp tx.nonce
          ; Uint.to_rlp tx.gas_price
          ; Uint.to_rlp tx.gas_limit
          ; Address.to_rlp tx.to_
          ; U256.to_rlp tx.value
          ; Rlp.Bytes tx.data
          ; U256.to_rlp tx.v
          ; U256.to_rlp tx.r
          ; U256.to_rlp tx.s ]
    | AccessList tx ->
        Rlp.List
          [ Uint.to_rlp tx.chain_id
          ; U256.to_rlp tx.nonce
          ; Uint.to_rlp tx.gas_price
          ; Uint.to_rlp tx.gas_limit
          ; Address.to_rlp tx.to_
          ; U256.to_rlp tx.value
          ; Rlp.Bytes tx.data
          ; Rlp.List (List.map Access.to_rlp tx.access_list)
          ; U8.to_rlp tx.y_parity
          ; U256.to_rlp tx.r
          ; U256.to_rlp tx.s ]
    | FeeMarket tx ->
        Rlp.List
          [ Uint.to_rlp tx.chain_id
          ; U256.to_rlp tx.nonce
          ; Uint.to_rlp tx.max_priority_fee_per_gas
          ; Uint.to_rlp tx.max_fee_per_gas
          ; Uint.to_rlp tx.gas_limit
          ; Address.to_rlp tx.to_
          ; U256.to_rlp tx.value
          ; Rlp.Bytes tx.data
          ; Rlp.List (List.map Access.to_rlp tx.access_list)
          ; U8.to_rlp tx.y_parity
          ; U256.to_rlp tx.r
          ; U256.to_rlp tx.s ]
    | SetCode tx ->
        Rlp.List
          [ Uint.to_rlp tx.chain_id
          ; U256.to_rlp tx.nonce
          ; Uint.to_rlp tx.max_priority_fee_per_gas
          ; Uint.to_rlp tx.max_fee_per_gas
          ; Uint.to_rlp tx.gas_limit
          ; Address.to_rlp tx.to_
          ; U256.to_rlp tx.value
          ; Rlp.Bytes tx.data
          ; Rlp.List (List.map Access.to_rlp tx.access_list)
          ; Rlp.List (List.map Authorization.to_rlp tx.authorization_list)
          ; U8.to_rlp tx.y_parity
          ; U256.to_rlp tx.r
          ; U256.to_rlp tx.s ]

  (* YP (37) *)
  let encode tx =
    match kind_tag tx with
    | `Legacy -> Rlp.encode (to_rlp tx)
    | tag -> kind_tag_to_bytes tag ^ Rlp.encode (to_rlp tx)

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
          kind_tag_to_bytes `AccessList
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
          kind_tag_to_bytes `FeeMarket
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
      | SetCode tx ->
          assert (Uint.(tx.chain_id = chain_id)) ;
          (* EIP-1559 *)
          kind_tag_to_bytes `SetCode
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
                 ; Rlp.List (List.map Authorization.to_rlp tx.authorization_list) ] )
    in
    let hash = Crypto.keccak_256 bytes in
    hash

  let sender (chain_id : Uint.t) (tx : t) : Address.t option =
    let msg_hash = signing_hash chain_id tx in
    Option.(
      let signature = signature chain_id tx in
      let$ () = ensure U256.(zero < signature.r && signature.r < Crypto.secp256k1n) in
      let$ () = ensure U256.(zero < signature.s && signature.s < Crypto.secp256k1n / ~$2) in
      Crypto.ecrecover signature msg_hash )

  let access_list tx =
    match tx with
    | Legacy _ -> []
    | AccessList {access_list; _} | FeeMarket {access_list; _} | SetCode {access_list; _} -> access_list

  let authorization_list tx =
    match tx with
    | SetCode {authorization_list; _} -> authorization_list
    | Legacy _ | AccessList _ | FeeMarket _ -> []

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

  (* YP (21) *)
  let to_rlp {global_index; validator_index; recipient; amount} =
    Rlp.List
      [U64.to_rlp global_index; U64.to_rlp validator_index; Address.to_rlp recipient; U256.to_rlp amount]

  let encode (withdrawal : t) = Rlp.encode (to_rlp withdrawal)
end

module Block = struct
  module Header = struct
    (* YP 4.4 *)
    type t =
      { parent_hash : B32.t (* H_p *) [@key "parentHash"]
      ; ommers_hash : B32.t (* H_o *) [@key "uncleHash"]
      ; beneficiary : Address.t (* H_c *) [@key "coinbase"]
      ; state_root : B32.t (* H_r *) [@key "stateRoot"]
      ; transactions_root : B32.t (* H_t *) [@key "transactionsTrie"]
      ; receipts_root : B32.t (* H_e *) [@key "receiptTrie"]
      ; logs_bloom : Bloom.t (* H_b *) [@key "bloom"]
      ; difficulty : Uint.t (* H_d *) [@key "difficulty"]
      ; number : Uint.t (* H_i *) [@key "number"]
      ; gas_limit : Uint.t (* H_l *) [@key "gasLimit"]
      ; gas_used : Uint.t (* H_g *) [@key "gasUsed"]
      ; timestamp : U256.t (* H_s *) [@key "timestamp"]
      ; extra_data : Bytes.t (* H_x *) [@key "extraData"]
      ; prev_randao : B32.t (* H_a *) [@key "mixHash"]
      ; nonce : B8.t (* H_n *) [@key "nonce"]
      ; base_fee_per_gas : Uint.t (* H_f *) [@key "baseFeePerGas"]
      ; withdrawals_root : B32.t (* H_w *) [@key "withdrawalsRoot"]
      ; blob_gas_used : U64.t (* EIP-4844 *) [@key "blobGasUsed"]
      ; excess_blob_gas : U64.t (* EIP-4844 *) [@key "excessBlobGas"]
      ; parent_beacon_block_root : B32.t (* EIP-4788 *) [@key "parentBeaconBlockRoot"]
      ; requests_hash : B32.t (* EIP-7685 *) [@key "requestsHash"] }
    [@@deriving yojson {strict = false (* Additional fields in Ethereum test fixtures: hash *)}]

    (* YP 4.4.3 (40) *)
    let to_rlp h =
      Rlp.List
        [ Rlp.of_bytes32 h.parent_hash
        ; Rlp.of_bytes32 h.ommers_hash
        ; Address.to_rlp h.beneficiary
        ; Rlp.of_bytes32 h.state_root
        ; Rlp.of_bytes32 h.transactions_root
        ; Rlp.of_bytes32 h.receipts_root
        ; Rlp.Bytes (Bloom.to_bytes h.logs_bloom)
        ; Uint.to_rlp h.difficulty
        ; Uint.to_rlp h.number
        ; Uint.to_rlp h.gas_limit
        ; Uint.to_rlp h.gas_used
        ; U256.to_rlp h.timestamp
        ; Rlp.Bytes h.extra_data
        ; Rlp.of_bytes32 h.prev_randao
        ; Rlp.of_bytes (B8.to_bytes h.nonce)
        ; Uint.to_rlp h.base_fee_per_gas
        ; Rlp.of_bytes32 h.withdrawals_root
        ; U64.to_rlp h.blob_gas_used
        ; U64.to_rlp h.excess_blob_gas
        ; Rlp.of_bytes32 h.parent_beacon_block_root
        ; Rlp.of_bytes32 h.requests_hash ]
  end

  (* YP 4.4 (23) *)
  type t =
    { header : Header.t (* B_H *) [@key "blockHeader"]
    ; transactions : Transaction.t list (* B_T *) [@key "transactions"]
    ; ommers : Header.t list (* B_U *) [@key "uncleHeaders"]
    ; withdrawals : Withdrawal.t list (* B_W *) [@key "withdrawals"] }
  [@@deriving yojson {strict = false (* Additional fields in Ethereum test fixtures: chainname, rlp *)}]

  (* YP 4.4.3 (41) *)
  let to_rlp b =
    (* YP (42) *)
    (* Note the difference with Transaction.to_rlp and Transaction.encode *)
    let transaction_to_rlp tx =
      match Transaction.kind_tag tx with
      | `Legacy -> Transaction.to_rlp tx
      | _ -> Rlp.Bytes (Transaction.encode tx)
    in
    Rlp.List
      [ Header.to_rlp b.header
      ; Rlp.List (List.map transaction_to_rlp b.transactions)
      ; Rlp.List (List.map Header.to_rlp b.ommers)
      ; Rlp.List (List.map Withdrawal.to_rlp b.withdrawals) ]
end

module Log = struct
  (* YP 4.4.1 (28) *)
  type t = {address : Address.t (* O_a *); topics : B32.t list (* O_t *); data : Bytes.t (* O_d *)}
  [@@deriving yojson]

  (* YP (30) *)
  let to_bloom (log : t) : Bloom.t =
    let entries = Address.to_bytes32 log.address :: log.topics in
    List.fold_left
      (fun bloom entry -> Bloom.(logor bloom (hash_bytes (B32.to_bytes entry))))
      Bloom.zeros entries

  let to_rlp {address; topics; data} =
    Rlp.List
      [ Address.to_rlp address
      ; Rlp.List (List.map (fun bs -> Rlp.Bytes (B32.to_bytes bs)) topics)
      ; Rlp.Bytes data ]
end

module Receipt = struct
  (* YP 4.4.1. *)
  type t =
    { tx_type : Transaction.kind_tag (* R_x *)
    ; succeeded : bool (* R_z *)
    ; cumulative_gas_used : Uint.t (* R_u *) [@tag "cumulativeGasUsed"]
    ; bloom : Bloom.t (* R_b *) [@tag "logsBloom"]
    ; logs : Log.t list (* R_l *) }
  [@@deriving yojson]

  (* YP (25) *)
  let to_rlp {tx_type; succeeded; cumulative_gas_used; bloom; logs} =
    ignore tx_type ;
    Rlp.List
      [ U64.(to_rlp (of_bool succeeded))
      ; Uint.to_rlp cumulative_gas_used
      ; Rlp.Bytes (Bloom.to_bytes bloom)
      ; Rlp.List (List.map Log.to_rlp logs) ]

  (* YP (38) *)
  let encode (receipt : t) =
    match receipt.tx_type with
    | `Legacy -> Rlp.encode (to_rlp receipt)
    | tag -> Transaction.kind_tag_to_bytes tag ^ Rlp.encode (to_rlp receipt)
end

module Account = struct
  type t =
    { nonce : U256.t (* σ[a]_n *)
    ; balance : U256.t (* σ[a]_b *)
    ; storage : B32.t B32.Map.t (* σ[a]_s *)
    ; code : Bytes.t (* σ[a]_c *) }
  [@@deriving lens {submodule = true; prefix = true}, yojson]
  include TLens

  let empty = {balance = U256.zero; storage = B32.Map.empty; code = Bytes.empty; nonce = U256.zero}

  (* YP (14) *)
  let is_empty {balance; nonce; code; _} = balance = U256.zero && nonce = U256.zero && code = Bytes.empty

  let to_rlp {nonce; balance; storage; code} =
    let storage_root =
      let mpt =
        storage
        |> B32.Map.to_seq
        |> Seq.map (fun (k, v) ->
            let k = B32.to_bytes (Crypto.keccak_256 (B32.to_bytes k)) in
            let v = Rlp.encode U256.(to_rlp (of_repr v)) in
            (* YP (8) *)
            (k, v) )
        |> Mpt.of_seq
      in
      mpt.root_hash
    in
    let code_hash = Crypto.keccak_256 code in
    Rlp.List [U256.to_rlp nonce; U256.to_rlp balance; Rlp.of_bytes32 storage_root; Rlp.of_bytes32 code_hash]
end
