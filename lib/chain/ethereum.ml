(** Definitions for Ethereum types: accounts, blocks, transactions.
    Work in progress, will be expanded as needed. *)
open Numeric

module Address = U160

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
    type t = {account_address : Address.t (* E_a *); storage_keys : U256.t list (* E_s *)}
  end

  type call_or_create =
    | Call of {to_ : Address.t (* T_t *); data : Bytes.t (* T_d *)}
    | Create of {init : Bytes.t (* T_i *)}

  (* YP 4.2 *)
  type kind =
    | Legacy of
        { call_or_create : call_or_create (* Either T_i or (T_t, T_d) *)
        ; gas_price : Uint.t (* T_p *)
        ; w : U256.t (* T_w *) }
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

  let call_or_create txn =
    match txn.kind with
    | Legacy {call_or_create; _} | AccessList {call_or_create; _} | FeeMarket {call_or_create; _} ->
        call_or_create
    | Blob {to_; data; _} -> Call {to_; data}
  let data_or_initcode = function Call {data; _} -> data | Create {init} -> init

  let access_list txn =
    match txn.kind with
    | Legacy _ -> []
    | AccessList {access_list; _} | FeeMarket {access_list; _} | Blob {access_list; _} -> access_list
end

module Withdrawal = struct
  (* YP 4.3 *)
  type t =
    { global_index : Uint64.t (* W_g *)
    ; validator_index : Uint64.t (* W_v *)
    ; recipient : Address.t (* W_r *)
    ; amount : U256.t (* W_a *) }
end

module Block = struct
  module Header = struct
    (* YP 4.4 *)
    type t =
      { parent_hash : U256.t (* H_p *)
      ; ommers_hash : U256.t (* H_o *)
      ; beneficiary : Address.t (* H_c *)
      ; state_root : U256.t (* H_r *)
      ; transactions_root : U256.t (* H_t *)
      ; receipts_root : U256.t (* H_e *)
      ; logs_bloom : U256.t (* H_b *)
      ; difficulty : Uint.t (* H_d *)
      ; number : Uint.t (* H_i *)
      ; gas_limit : Uint.t (* H_l *)
      ; gas_used : Uint.t (* H_g *)
      ; timestamp : U256.t (* H_s *)
      ; extra_data : Bytes.t (* H_x *)
      ; prev_randao : U256.t (* H_a *)
      ; nonce : Uint64.t (* H_n *)
      ; base_fee_per_gas : Uint.t (* H_f *)
      ; withdrawals_root : U256.t (* H_w *)
      ; blob_gas_used : Uint64.t (* EIP-4844 *)
      ; excess_blob_gas : Uint64.t (* EIP-4844 *)
      ; parent_beacon_block_root : U256.t (* EIP-4788 *)
      ; requests_hash : U256.t (* EIP-7685 *) }
  end

  (* YP 4.4 (23) *)
  type t =
    { header : Header.t (* B_H *)
    ; transactions : Transaction.t list (* B_T *)
    ; ommers : Header.t list (* B_U *)
    ; withdrawals : Withdrawal.t list (* B_W *) }
end

module Log = struct
  (* YP 4.4.1 (28) *)
  type t = {address : Address.t (* O_a *); topics : U256.t list (* O_t *); data : Bytes.t (* O_d *)}
end

module Receipt = struct
  type transaction_type = Legacy | AccessList | FeeMarket | Blob

  (* YP 4.4.1. *)
  type t =
    { tx_type : transaction_type (* R_x *)
    ; succeeded : bool (* R_z *)
    ; cumulative_gas_used : Uint.t (* R_u *)
    ; bloom : Bytes256.t (* R_b *)
    ; logs : Log.t list (* R_l *) }
end
