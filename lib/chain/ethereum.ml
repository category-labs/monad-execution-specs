(** Definitions for Ethereum types: accounts, blocks, transactions. *)

open Numeric
open Byte_string

module Address = struct
  (** Ethereum addresses, represented as 20-byte byte-strings. *)

  include B20

  let zero = init (fun _ -> '\x00')

  let to_rlp (addr : t) = Rlp.Bytes (to_bytes addr)

  (* Frequently used in the VM to read and write addresses (Bytes.B20.t) as stack elements (U256.t). *)
  let of_u256_truncating (x : U256.t) : t = of_bytes32_truncating (U256.to_repr x)
  let to_u256 (addr : t) = U256.of_repr (to_bytes32 addr)

  type create2_params = {salt : B32.t; initcode : Bytes.t}

  (** [of_contract_creation ~sender ~nonce ~create2] returns the address that would be created by a contract
      creation with the specific [sender] and [nonce] and optional [create2] salt, computed as per YP (95). *)
  let of_contract_creation ~(sender : t) ~(nonce : U64.t) ~(create2 : create2_params option) =
    (* YP (96) *)
    let lin =
      match create2 with
      | None -> Rlp.(encode (List [to_rlp sender; U64.(to_rlp (nonce - one))]))
      | Some {salt; initcode} ->
          Bytes.(
            of_char '\xff'
            ^ B20.to_bytes sender
            ^ B32.to_bytes salt
            ^ B32.to_bytes (Crypto.keccak_256 initcode) )
    in
    of_bytes32_truncating (Crypto.keccak_256 lin)

  (* Encoding/decoding address options, used to handle the recipient of a transaction. *)
  type t_opt = t option
  let t_opt_to_yojson (addr : t option) = match addr with Some addr -> to_yojson addr | None -> `String ""
  let t_opt_of_yojson (json : Yojson.Safe.t) =
    match json with `String "" -> Ok None | _ -> Result.map Option.some (of_yojson json)

  let t_opt_to_rlp (addr : t option) = match addr with None -> Rlp.Bytes "" | Some addr -> to_rlp addr
end

module Revision = struct
  (** Ethereum forks, not relevant to Monad but provided here for reference. *)

  type t =
    | Frontier  (** The Frontier revision. The one Ethereum launched with. *)
    | Homestead  (** {{:https://eips.ethereum.org/EIPS/eip-606}The Homestead revision.} *)
    | TangerineWhistle  (** {{:https://eips.ethereum.org/EIPS/eip-608}The Tangerine Whistle revision.} *)
    | SpuriousDragon  (** {{:https://eips.ethereum.org/EIPS/eip-607}The Spurious Dragon revision.} *)
    | Byzantium  (** {{:https://eips.ethereum.org/EIPS/eip-609}The Byzantium revision.} *)
    | Constantinople  (** {{:https://eips.ethereum.org/EIPS/eip-1013}The Constantinople revision.} *)
    | Petersburg  (** {{:https://eips.ethereum.org/EIPS/eip-1716}The Petersburg revision.} *)
    | Istanbul  (** {{:https://eips.ethereum.org/EIPS/eip-1679}The Istanbul revision.} *)
    | Berlin
        (** {{:https://github.com/ethereum/execution-specs/blob/master/network-upgrades/mainnet-upgrades/berlin.md}The Berlin revision.} *)
    | London
        (** {{:https://github.com/ethereum/execution-specs/blob/master/network-upgrades/mainnet-upgrades/london.md}The London revision.} *)
    | Paris
        (** {{:https://github.com/ethereum/execution-specs/blob/master/network-upgrades/mainnet-upgrades/paris.md}The Paris revision.} *)
    | Shanghai
        (** {{:https://github.com/ethereum/execution-specs/blob/master/network-upgrades/mainnet-upgrades/shanghai.md}The Shanghai revision.} *)
    | Cancun
        (** {{:https://github.com/ethereum/execution-specs/blob/master/network-upgrades/mainnet-upgrades/cancun.md}The Cancun revision.} *)
    | Prague  (** {{:https://eips.ethereum.org/EIPS/eip-7600}The Prague / Pectra revision.} *)
    | Osaka  (** {{:https://eips.ethereum.org/EIPS/eip-7607}The Osaka / Fusaka revision.} *)
    | Experimental
        (** The unspecified EVM revision used for EVM implementations to expose experimental features. *)
end

module Transaction = struct
  (** Ethereum transactions, and the types that make them up. *)

  module Access = struct
    (** An entry in an EIP-2930 access list. *)
    type t = {address : Address.t (* E_a *); storage_keys : B32.t list (* E_s *) [@key "storageKeys"]}
    [@@deriving yojson]

    let to_rlp {address; storage_keys} =
      Rlp.List [Address.to_rlp address; Rlp.List (List.map Rlp.of_bytes32 storage_keys)]
  end

  module Authorization = struct
    (** An EIP-7702 authorization. *)
    type t =
      { chain_id : U256.t [@key "chainId"]
      ; address : Address.t
      ; nonce : U64.t
      ; y_parity : U8.t [@key "v"]
      ; r : U256.t
      ; s : U256.t }
    [@@deriving yojson {strict = false}]

    let to_rlp {chain_id; nonce; address; y_parity; r; s} =
      Rlp.List
        [ U256.to_rlp chain_id
        ; Address.to_rlp address
        ; U64.to_rlp nonce
        ; U8.to_rlp y_parity
        ; U256.to_rlp r
        ; U256.to_rlp s ]

    (** [authority auth] recovers the authority address from an EIP-7702 authorization entry. *)
    let authority ({y_parity; r; s; chain_id; address; nonce} : t) : Address.t option =
      let msg =
        Delegation.magic ^ Rlp.(encode (List [U256.to_rlp chain_id; Address.to_rlp address; U64.to_rlp nonce]))
      in
      let auth_hash = Crypto.keccak_256 msg in
      Option.(
        let$ () = ensure U256.(zero < r && r < Crypto.secp256k1n) in
        let$ () = ensure U256.(zero < s && s <= Crypto.secp256k1n / ~$2) in
        Crypto.ecrecover {y_parity; r; s} auth_hash )
  end

  (* Transaction types below according to YP (18), YP (20) *)

  (** Legacy transactions (transaction type 0 as per YP Section 4.2) *)
  type legacy_tx =
    { nonce : U64.t (* T_n *)
    ; gas_limit : Uint.t (* T_g *) [@key "gasLimit"]
    ; value : U256.t (* T_v *)
    ; r : U256.t (* T_r *)
    ; s : U256.t (* T_s *)
    ; to_ : Address.t_opt
          (* T_t *) [@of_yojson Address.t_opt_of_yojson] [@to_yojson Address.t_opt_to_yojson] [@key "to"]
    ; data : Bytes.t (* Either T_d or T_i *)
    ; gas_price : Uint.t (* T_p *) [@key "gasPrice"]
    ; v : U256.t (* T_w *) }
  [@@deriving yojson {strict = false}]

  (** EIP-2930 access list transactions (transaction type 1 as per YP Section 4.2) *)
  type access_list_tx =
    { nonce : U64.t (* T_n *)
    ; gas_limit : Uint.t (* T_g *) [@key "gasLimit"]
    ; value : U256.t (* T_v *)
    ; r : U256.t (* T_r *)
    ; s : U256.t (* T_s *)
    ; to_ : Address.t_opt (* T_t *) [@key "to"]
    ; data : Bytes.t (* Either T_d or T_i *)
    ; gas_price : Uint.t (* T_p *) [@key "gasPrice"]
    ; access_list : Access.t list (* T_A *) [@key "accessList"]
    ; chain_id : Uint.t (* T_c *) [@key "chainId"]
    ; y_parity : U8.t (* T_y *) [@key "v"] }
  [@@deriving yojson {strict = false}]

  (** EIP-1559 fee market transactions (transaction type 2 as per YP Section 4.2) *)
  type fee_market_tx =
    { nonce : U64.t (* T_n *)
    ; gas_limit : Uint.t (* T_g *) [@key "gasLimit"]
    ; value : U256.t (* T_v *)
    ; r : U256.t (* T_r *)
    ; s : U256.t (* T_s *)
    ; to_ : Address.t_opt (* T_t *) [@key "to"]
    ; data : Bytes.t (* Either T_d or T_i *)
    ; max_fee_per_gas : Uint.t (* T_m *) [@key "maxFeePerGas"]
    ; max_priority_fee_per_gas : Uint.t (* T_f *) [@key "maxPriorityFeePerGas"]
    ; access_list : Access.t list (* T_A *) [@key "accessList"]
    ; chain_id : Uint.t (* T_c *) [@key "chainId"]
    ; y_parity : U8.t (* T_y *) [@key "v"] }
  [@@deriving yojson {strict = false}]

  (** EIP-7702 set-code transactions (transaction type 4 as per EIP-7702). *)
  type set_code_tx =
    { nonce : U64.t (* T_n *)
    ; gas_limit : Uint.t (* T_g *) [@key "gasLimit"]
    ; value : U256.t (* T_v *)
    ; r : U256.t (* T_r *)
    ; s : U256.t (* T_s *)
    ; to_ : Address.t (* T_t. As per EIP-7702, this must not be null. *) [@key "to"]
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

  let to_ tx =
    match tx with
    | Legacy {to_; _} | AccessList {to_; _} | FeeMarket {to_; _} -> to_
    | SetCode {to_; _} -> Some to_

  let nonce tx =
    match tx with
    | Legacy {nonce; _} | AccessList {nonce; _} | FeeMarket {nonce; _} | SetCode {nonce; _} -> nonce

  (* YP (17), but we do not distinguish between initcode and data fields. *)
  let data tx =
    match tx with Legacy {data; _} | AccessList {data; _} | FeeMarket {data; _} | SetCode {data; _} -> data

  let value tx =
    match tx with
    | Legacy {value; _} | AccessList {value; _} | FeeMarket {value; _} | SetCode {value; _} -> value

  let gas_limit tx =
    match tx with
    | Legacy {gas_limit; _} | AccessList {gas_limit; _} | FeeMarket {gas_limit; _} | SetCode {gas_limit; _} ->
        gas_limit

  let chain_id tx =
    match tx with
    | AccessList {chain_id; _} | FeeMarket {chain_id; _} | SetCode {chain_id; _} -> Some chain_id
    | Legacy _ -> None

  let signature chain_id tx =
    (* r, s below are as in YP (321), YP (322) *)
    match tx with
    | AccessList {r; s; y_parity; _} | FeeMarket {r; s; y_parity; _} | SetCode {r; s; y_parity; _} ->
        (* YP (324), case 3 *)
        Crypto.{r; s; y_parity}
    | Legacy {r; s; v; _} ->
        (* YP (324), cases 1, 2 *)
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

  (** [to_rlp tx] RLP-encodes the data in [tx] following YP (16). Note that this does not include the
      transaction type. *)
  let to_rlp tx =
    match tx with
    | Legacy tx ->
        Rlp.List
          [ U64.to_rlp tx.nonce
          ; Uint.to_rlp tx.gas_price
          ; Uint.to_rlp tx.gas_limit
          ; Address.t_opt_to_rlp tx.to_
          ; U256.to_rlp tx.value
          ; Rlp.Bytes tx.data
          ; U256.to_rlp tx.v
          ; U256.to_rlp tx.r
          ; U256.to_rlp tx.s ]
    | AccessList tx ->
        Rlp.List
          [ Uint.to_rlp tx.chain_id
          ; U64.to_rlp tx.nonce
          ; Uint.to_rlp tx.gas_price
          ; Uint.to_rlp tx.gas_limit
          ; Address.t_opt_to_rlp tx.to_
          ; U256.to_rlp tx.value
          ; Rlp.Bytes tx.data
          ; Rlp.List (List.map Access.to_rlp tx.access_list)
          ; U8.to_rlp tx.y_parity
          ; U256.to_rlp tx.r
          ; U256.to_rlp tx.s ]
    | FeeMarket tx ->
        Rlp.List
          [ Uint.to_rlp tx.chain_id
          ; U64.to_rlp tx.nonce
          ; Uint.to_rlp tx.max_priority_fee_per_gas
          ; Uint.to_rlp tx.max_fee_per_gas
          ; Uint.to_rlp tx.gas_limit
          ; Address.t_opt_to_rlp tx.to_
          ; U256.to_rlp tx.value
          ; Rlp.Bytes tx.data
          ; Rlp.List (List.map Access.to_rlp tx.access_list)
          ; U8.to_rlp tx.y_parity
          ; U256.to_rlp tx.r
          ; U256.to_rlp tx.s ]
    | SetCode tx ->
        Rlp.List
          [ Uint.to_rlp tx.chain_id
          ; U64.to_rlp tx.nonce
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

  (** [encode tx] RLP-encodes a transaction, preceded by its transaction kind tag for non-legacy
      transactions. YP (37) *)
  let encode tx =
    match kind_tag tx with
    | `Legacy -> Rlp.encode (to_rlp tx)
    | tag -> kind_tag_to_bytes tag ^ Rlp.encode (to_rlp tx)

  (** [signing_hash chain_id tx] computes the hash of a transaction to be signed by the sender.
      YP (317), YP (318) *)
  let signing_hash chain_id tx =
    let bytes =
      (* Note that we use a different RLP encoding of transactions here which excludes the signature fields. *)
      match tx with
      | Legacy tx when U256.(tx.v = ~$27 || tx.v = ~$28) ->
          (* Pre EIP-155 transaction *)
          Rlp.encode
            (Rlp.List
               [ U64.to_rlp tx.nonce
               ; Uint.to_rlp tx.gas_price
               ; Uint.to_rlp tx.gas_limit
               ; Address.t_opt_to_rlp tx.to_
               ; U256.to_rlp tx.value
               ; Rlp.Bytes tx.data ] )
      | Legacy tx ->
          (* EIP-155 transaction *)
          Rlp.encode
            (Rlp.List
               [ U64.to_rlp tx.nonce
               ; Uint.to_rlp tx.gas_price
               ; Uint.to_rlp tx.gas_limit
               ; Address.t_opt_to_rlp tx.to_
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
                 ; U64.to_rlp tx.nonce
                 ; Uint.to_rlp tx.gas_price
                 ; Uint.to_rlp tx.gas_limit
                 ; Address.t_opt_to_rlp tx.to_
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
                 ; U64.to_rlp tx.nonce
                 ; Uint.to_rlp tx.max_priority_fee_per_gas
                 ; Uint.to_rlp tx.max_fee_per_gas
                 ; Uint.to_rlp tx.gas_limit
                 ; Address.t_opt_to_rlp tx.to_
                 ; U256.to_rlp tx.value
                 ; Rlp.Bytes tx.data
                 ; Rlp.List (List.map Access.to_rlp tx.access_list) ] )
      | SetCode tx ->
          assert (Uint.(tx.chain_id = chain_id)) ;
          (* EIP-7702 *)
          kind_tag_to_bytes `SetCode
          ^ Rlp.encode
              (Rlp.List
                 [ Uint.to_rlp chain_id
                 ; U64.to_rlp tx.nonce
                 ; Uint.to_rlp tx.max_priority_fee_per_gas
                 ; Uint.to_rlp tx.max_fee_per_gas
                 ; Uint.to_rlp tx.gas_limit
                 ; Address.to_rlp tx.to_
                 ; U256.to_rlp tx.value
                 ; Rlp.Bytes tx.data
                 ; Rlp.List (List.map Access.to_rlp tx.access_list)
                 ; Rlp.List (List.map Authorization.to_rlp tx.authorization_list) ] )
    in
    Crypto.keccak_256 bytes

  (** [sender chain_id tx] attempts to recover the transaction sender from its signature, returning [None]
      if the signature is invalid. YP (323) *)
  let sender (chain_id : Uint.t) (tx : t) : Address.t option =
    let msg_hash = signing_hash chain_id tx in
    Option.(
      let signature = signature chain_id tx in
      (* YP (312) *)
      let$ () = ensure U256.(zero < signature.r && signature.r < Crypto.secp256k1n) in
      (* YP (313) *)
      let$ () = ensure U256.(zero < signature.s && signature.s <= Crypto.secp256k1n / ~$2) in
      (* YP (314) *)
      let$ () = ensure U8.(signature.y_parity = zero || signature.y_parity = one) in
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
    match to_ with None -> Create {initcode = data} | Some to_ -> Call {data; to_}

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
      | Ok None | Ok (Some 0) -> [%of_yojson: legacy_tx] json >>= fun tx -> return (Legacy tx)
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
end

module Withdrawal = struct
  (** A withdrawal representing an Ether transfer from a consensus validator into an execution account.
      YP (22). *)
  type t =
    { global_index : U64.t [@key "index"]  (** W_g, an unique index identifying this withdrawal. *)
    ; validator_index : U64.t [@key "validatorIndex"]
          (** W_v, the index of the consensus validator that is performing the withdrawal. *)
    ; recipient : Address.t [@key "address"]
          (** W_r, the address of the account that will receive the withdrawn funds. *)
    ; amount : U64.t [@key "amount"]  (** W_a, the amount to be withdrawn, in MON-Gwei. *) }
  [@@deriving yojson]

  (* YP (21) *)
  let to_rlp {global_index; validator_index; recipient; amount} =
    Rlp.List [U64.to_rlp global_index; U64.to_rlp validator_index; Address.to_rlp recipient; U64.to_rlp amount]

  let encode (withdrawal : t) = Rlp.encode (to_rlp withdrawal)
end

module Block = struct
  (** Ethereum blocks and block headers. *)

  module Header = struct
    (** An Ethereum block header as defined in YP (44). *)
    type t =
      { parent_hash : B32.t [@key "parentHash"]
            (** H_p, the [keccak256] hash of the RLP encoding of the parent block's header. *)
      ; ommers_hash : B32.t [@key "uncleHash"]
            (** H_o, always set to [keccak256] of the RLP encoding of the empty list. *)
      ; beneficiary : Address.t [@key "coinbase"]
            (** H_c, address of the validator that will receive the block reward and tips. *)
      ; state_root : B32.t [@key "stateRoot"]
            (** H_r, the root hash of the state trie after processing this block in full. *)
      ; transactions_root : B32.t [@key "transactionsTrie"]
            (** H_t, the root hash of the transactions trie. *)
      ; receipts_root : B32.t [@key "receiptTrie"]
            (** H_e, the root hash of the trie containing all the receipts of this block's transactions. *)
      ; logs_bloom : Bloom.t [@key "bloom"]
            (** H_b, the Bloom filter constructed from all the logs emitted by transactions in this block. *)
      ; difficulty : Uint.t [@key "difficulty"]  (** H_d, proof-of-work difficulty, set to zero. *)
      ; number : Uint.t [@key "number"]  (** H_i, the block number. *)
      ; gas_limit : Uint.t [@key "gasLimit"]
            (** H_l, the maximum total gas that can be consumed by all the transactions in this block. *)
      ; gas_used : Uint.t [@key "gasUsed"]
            (** H_g, the total gas used by all the transactions in this block. *)
      ; timestamp : U256.t [@key "timestamp"]  (** H_s, seconds since Unix epoch. *)
      ; extra_data : Bytes.t [@key "extraData"]
            (** H_x, extra data included by the miner, not used by execution. Must be at most 32 bytes. *)
      ; prev_randao : B32.t [@key "mixHash"]  (** H_a, output of the latest RANDAO beacon. *)
      ; nonce : B8.t [@key "nonce"]  (** H_n, proof-of-work nonce, set to zero. *)
      ; base_fee_per_gas : Uint.t [@key "baseFeePerGas"]
            (** H_f, the base amount of MON-wei that is burned for each unit of gas paid by a transaction. *)
      ; withdrawals_root : B32.t [@key "withdrawalsRoot"]  (** H_w, the root hash of the withdrawals trie. *)
      ; blob_gas_used : U64.t [@key "blobGasUsed"]
            (** Total blob gas consumed by transactions in this block, as per EIP-4844.
                Note that Monad does not support blob transactions. *)
      ; excess_blob_gas : U64.t [@key "excessBlobGas"]
            (** Blob gas consumed in excess of the target, prior to this block, as per EIP-4844.
                Note that Monad does not support blob transactions. *)
      ; parent_beacon_block_root : B32.t [@key "parentBeaconBlockRoot"]
            (** Root hash of the corresponding beacon chain block, see EIP-4788. *)
      ; requests_hash : B32.t [@key "requestsHash"]
            (** [sha_256] of all the EIP-7685 requests in this block. *) }
    [@@deriving yojson {strict = false (* Additional fields in Ethereum test fixtures: hash *)}, lens]

    (** [to_rlp h] RLP-encodes a block header according to YP (40) *)
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

    (* Empty block header, useful for testing. *)
    let empty =
      { parent_hash = B32.zeros
      ; ommers_hash = B32.zeros
      ; beneficiary = Address.zero
      ; state_root = B32.zeros
      ; transactions_root = B32.zeros
      ; receipts_root = B32.zeros
      ; logs_bloom = Bloom.zeros
      ; difficulty = Uint.zero
      ; number = Uint.zero
      ; gas_limit = Uint.zero
      ; gas_used = Uint.zero
      ; timestamp = U256.zero
      ; extra_data = Bytes.empty
      ; prev_randao = B32.zeros
      ; nonce = B8.zeros
      ; base_fee_per_gas = Uint.zero
      ; withdrawals_root = B32.zeros
      ; blob_gas_used = U64.zero
      ; excess_blob_gas = U64.zero
      ; parent_beacon_block_root = B32.zeros
      ; requests_hash = B32.zeros }
  end

  (* Bring block header lenses into scope for convenience. *)
  include Header

  (** An Ethereum block as defined in YP (3), YP (23) *)
  type t =
    { header : Header.t [@key "blockHeader"]  (** B_H, the header of this block. *)
    ; transactions : Transaction.t list [@key "transactions"]
          (** B_T, the list of transactions included in this block. *)
    ; ommers : Header.t list [@key "uncleHeaders"]
          (** B_U, the uncle blocks of this block. Always empty as Monad does not implement proof-of-work. *)
    ; withdrawals : Withdrawal.t list [@key "withdrawals"]
          (** The withdrawals to be processed by this block. *) }
  [@@deriving yojson {strict = false (* Additional fields in Ethereum test fixtures: chainname, rlp *)}, lens]

  let empty = {header = empty; transactions = []; ommers = []; withdrawals = []}

  (** [to_rlp b] RLP-encodes a block according to YP (41) *)
  let to_rlp b =
    (* YP (42) *)
    (* Note the difference with Transaction.to_rlp and Transaction.encode *)
    let transaction_to_rlp tx =
      match Transaction.kind_tag tx with
      | `Legacy -> Transaction.to_rlp tx
      | _ -> Rlp.Bytes (Transaction.encode tx)
    in
    (* YP (43) is List.map below *)
    Rlp.List
      [ Header.to_rlp b.header
      ; Rlp.List (List.map transaction_to_rlp b.transactions)
      ; Rlp.List (List.map Header.to_rlp b.ommers)
      ; Rlp.List (List.map Withdrawal.to_rlp b.withdrawals) ]

  let hash b = Crypto.keccak_256 (Rlp.encode (Header.to_rlp b.header))
end

module Log = struct
  (** An Ethereum log, recording a contract-specific execution event. YP (28), YP (29) *)
  type t =
    { address : Address.t  (** Oₐ, the address of the account that emitted the log. *)
    ; topics : B32.t list  (** Oₜ, a list of topics that can be used for indexing. *)
    ; data : Bytes.t  (** O_d, log-specific data of arbitrary length. *) }
  [@@deriving yojson]

  (** [to_bloom log] compresses a log into a 2048-bit Bloom filter based on its address and topics. YP (30) *)
  let to_bloom (log : t) : Bloom.t =
    let topics = Seq.map (fun topic -> B32.to_bytes topic) (List.to_seq log.topics) in
    Seq.fold_left
      (fun bloom entry -> Bloom.(logor bloom (hash_bytes entry)))
      (Bloom.hash_bytes (Address.to_bytes log.address))
      topics

  let to_rlp {address; topics; data} =
    Rlp.List
      [ Address.to_rlp address
      ; Rlp.List (List.map (fun bs -> Rlp.Bytes (B32.to_bytes bs)) topics)
      ; Rlp.Bytes data ]
end

module Receipt = struct
  (** An Ethereum transaction receipt, recording the result of a transaction execution. YP (24), YP (26),
      YP (27). *)
  type t =
    { tx_type : Transaction.kind_tag  (** Rₓ, the type of the transaction that was executed. *)
    ; succeeded : bool
          (** R_z, true in case of success, false in case of failure (including deliberate REVERT).
              Note that in the Yellow Paper this only takes values 0 or 1. *)
    ; cumulative_gas_used : Uint.t [@key "cumulativeGasUsed"]
          (** Rᵤ, the total gas used by this transaction and all previous transactions in this block. *)
    ; bloom : Bloom.t [@key "logsBloom"]  (** R_b, the Bloom filter of [logs], computed by {!Log.to_bloom}. *)
    ; logs : Log.t list  (** Rₗ, the sequence of logs produced while executing the transaction. *) }
  [@@deriving yojson]

  (** [to_rlp rec] RLP-encodes the data in [rec] following YP (25). Note that this does not include the
      transaction type. *)
  let to_rlp {tx_type; succeeded; cumulative_gas_used; bloom; logs} =
    ignore tx_type ;
    Rlp.List
      [ U64.(to_rlp (of_bool succeeded))
      ; Uint.to_rlp cumulative_gas_used
      ; Rlp.Bytes (Bloom.to_bytes bloom)
      ; Rlp.List (List.map Log.to_rlp logs) ]

  (** [encode rec] RLP-encodes a receipt, preceded by its transaction kind tag for non-legacy transactions.
      YP (38) *)
  let encode (receipt : t) =
    match receipt.tx_type with
    | `Legacy -> Rlp.encode (to_rlp receipt)
    | tag -> Transaction.kind_tag_to_bytes tag ^ Rlp.encode (to_rlp receipt)
end

module Account = struct
  (** The state associated with an Ethereum address. YP (13), but storage and code are stored directly. *)
  type t =
    { nonce : U64.t  (** σ\[a\]ₙ, the account nonce - 64 bits wide as per EIP-2681. *)
    ; balance : U256.t  (** σ\[a\]_b *)
    ; storage : B32.t B32.Map.t
          (** σ\[a\]ₛ, the account storage, represented directly as a map rather than a state root. *)
    ; code : Bytes.t  (** σ\[a\]_c, the account code, represented directly as bytecode rather than a hash. *)
    }
  [@@deriving lens {submodule = true; prefix = true}, yojson]

  include TLens

  (** Structural equality on accounts. *)
  let equal acc_1 acc_2 =
    U64.(acc_1.nonce = acc_2.nonce)
    && U256.(acc_1.balance = acc_2.balance)
    && B32.Map.(equal B32.equal acc_1.storage acc_2.storage)
    && Bytes.(acc_1.code = acc_2.code)

  let ( = ) = equal

  let empty = {balance = U256.zero; storage = B32.Map.empty; code = Bytes.empty; nonce = U64.zero}

  (** Account emptiness check as per YP (14). Note that an account with zero balance, nonce and code is
      considered empty independently of its storage, but empty accounts with non-empty storage cannot be
      created during normal execution. *)
  let is_empty {balance; nonce; code; _} = U256.(balance = zero) && U64.(nonce = zero) && Bytes.(code = empty)

  (** [is_smart_contract acc] returns [true] when the account [acc] has non-empty code that does not correspond
      to an EIP-7702 delegation. *)
  let is_smart_contract {code; _} = Bytes.(code <> empty) && not (Delegation.is_valid_delegation code)

  (** [to_rlp acc] returns the RLP encoding of the account [acc]. This involves computing the storage
      root of the account, which is potentially very expensive. *)
  let to_rlp {nonce; balance; storage; code} =
    let storage_root =
      (* Unlike in the Yellow Paper, accounts contain their entire storage. The relationship in YP (7) is
         used here in reverse to calculate the storage root from the storage KV pairs. *)
      let mpt =
        storage
        |> B32.Map.to_seq
        |> Seq.map (fun (k, v) ->
            (* YP (8), YP (9) *)
            let k = B32.to_bytes (Crypto.keccak_256 (B32.to_bytes k)) in
            let v = Rlp.encode U256.(to_rlp (of_repr v)) in
            (k, v) )
        |> Mpt.of_seq
      in
      mpt.root_hash
    in
    let code_hash = Crypto.keccak_256 code in
    Rlp.List [U64.to_rlp nonce; U256.to_rlp balance; Rlp.of_bytes32 storage_root; Rlp.of_bytes32 code_hash]
end
