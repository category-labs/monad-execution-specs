Require Import RocqOfOCaml.RocqOfOCaml.
Require Import MonadVM.Chain.Ethereum.

Import ListNotations.

(** Constructive structural equality for the block type.  Several components
    are abstract functor results in the generated Gallina, so this definition
    composes the equality operations exported by those abstractions instead of
    inspecting their hidden representations. *)

Module E := Chain.Ethereum.
Module T := E.Transaction.

Fixpoint list_equal {A : Set} (equal : A -> A -> bool)
    (xs ys : list A) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs, y :: ys => andb (equal x y) (list_equal equal xs ys)
  | _, _ => false
  end.

Definition option_equal {A : Set} (equal : A -> A -> bool)
    (x y : option A) : bool :=
  match x, y with
  | None, None => true
  | Some x, Some y => equal x y
  | _, _ => false
  end.

Definition all (conditions : list bool) : bool :=
  List.fold_left andb true conditions.

Definition access_equal (x y : T.Access.t) : bool :=
  all
    [E.Address.equal x.(T.Access.t.address) y.(T.Access.t.address);
     list_equal String.eqb
       x.(T.Access.t.storage_keys) y.(T.Access.t.storage_keys)].

Definition authorization_equal (x y : T.Authorization.t) : bool :=
  all
    [Numeric.U256.equal x.(T.Authorization.t.chain_id)
       y.(T.Authorization.t.chain_id);
     E.Address.equal x.(T.Authorization.t.address)
       y.(T.Authorization.t.address);
     Numeric.U64.equal x.(T.Authorization.t.nonce)
       y.(T.Authorization.t.nonce);
     Numeric.U8.equal x.(T.Authorization.t.y_parity)
       y.(T.Authorization.t.y_parity);
     Numeric.U256.equal x.(T.Authorization.t.r) y.(T.Authorization.t.r);
     Numeric.U256.equal x.(T.Authorization.t.s) y.(T.Authorization.t.s)].

Definition legacy_equal (x y : T.legacy_tx) : bool :=
  all
    [Numeric.U64.equal x.(T.legacy_tx.nonce) y.(T.legacy_tx.nonce);
     Numeric.Uint.equal x.(T.legacy_tx.gas_limit) y.(T.legacy_tx.gas_limit);
     Numeric.U256.equal x.(T.legacy_tx.value) y.(T.legacy_tx.value);
     Numeric.U256.equal x.(T.legacy_tx.r) y.(T.legacy_tx.r);
     Numeric.U256.equal x.(T.legacy_tx.s) y.(T.legacy_tx.s);
     option_equal E.Address.equal x.(T.legacy_tx.to_) y.(T.legacy_tx.to_);
     Byte_string.Bytes.equal x.(T.legacy_tx.data) y.(T.legacy_tx.data);
     Numeric.Uint.equal x.(T.legacy_tx.gas_price) y.(T.legacy_tx.gas_price);
     Numeric.U256.equal x.(T.legacy_tx.v) y.(T.legacy_tx.v)].

Definition access_list_equal (x y : T.access_list_tx) : bool :=
  all
    [Numeric.U64.equal x.(T.access_list_tx.nonce) y.(T.access_list_tx.nonce);
     Numeric.Uint.equal x.(T.access_list_tx.gas_limit)
       y.(T.access_list_tx.gas_limit);
     Numeric.U256.equal x.(T.access_list_tx.value) y.(T.access_list_tx.value);
     Numeric.U256.equal x.(T.access_list_tx.r) y.(T.access_list_tx.r);
     Numeric.U256.equal x.(T.access_list_tx.s) y.(T.access_list_tx.s);
     option_equal E.Address.equal x.(T.access_list_tx.to_)
       y.(T.access_list_tx.to_);
     Byte_string.Bytes.equal x.(T.access_list_tx.data)
       y.(T.access_list_tx.data);
     Numeric.Uint.equal x.(T.access_list_tx.gas_price)
       y.(T.access_list_tx.gas_price);
     list_equal access_equal x.(T.access_list_tx.access_list)
       y.(T.access_list_tx.access_list);
     Numeric.Uint.equal x.(T.access_list_tx.chain_id)
       y.(T.access_list_tx.chain_id);
     Numeric.U8.equal x.(T.access_list_tx.y_parity)
       y.(T.access_list_tx.y_parity)].

Definition fee_market_equal (x y : T.fee_market_tx) : bool :=
  all
    [Numeric.U64.equal x.(T.fee_market_tx.nonce) y.(T.fee_market_tx.nonce);
     Numeric.Uint.equal x.(T.fee_market_tx.gas_limit)
       y.(T.fee_market_tx.gas_limit);
     Numeric.U256.equal x.(T.fee_market_tx.value) y.(T.fee_market_tx.value);
     Numeric.U256.equal x.(T.fee_market_tx.r) y.(T.fee_market_tx.r);
     Numeric.U256.equal x.(T.fee_market_tx.s) y.(T.fee_market_tx.s);
     option_equal E.Address.equal x.(T.fee_market_tx.to_)
       y.(T.fee_market_tx.to_);
     Byte_string.Bytes.equal x.(T.fee_market_tx.data)
       y.(T.fee_market_tx.data);
     Numeric.Uint.equal x.(T.fee_market_tx.max_fee_per_gas)
       y.(T.fee_market_tx.max_fee_per_gas);
     Numeric.Uint.equal x.(T.fee_market_tx.max_priority_fee_per_gas)
       y.(T.fee_market_tx.max_priority_fee_per_gas);
     list_equal access_equal x.(T.fee_market_tx.access_list)
       y.(T.fee_market_tx.access_list);
     Numeric.Uint.equal x.(T.fee_market_tx.chain_id)
       y.(T.fee_market_tx.chain_id);
     Numeric.U8.equal x.(T.fee_market_tx.y_parity)
       y.(T.fee_market_tx.y_parity)].

Definition set_code_equal (x y : T.set_code_tx) : bool :=
  all
    [Numeric.U64.equal x.(T.set_code_tx.nonce) y.(T.set_code_tx.nonce);
     Numeric.Uint.equal x.(T.set_code_tx.gas_limit)
       y.(T.set_code_tx.gas_limit);
     Numeric.U256.equal x.(T.set_code_tx.value) y.(T.set_code_tx.value);
     Numeric.U256.equal x.(T.set_code_tx.r) y.(T.set_code_tx.r);
     Numeric.U256.equal x.(T.set_code_tx.s) y.(T.set_code_tx.s);
     E.Address.equal x.(T.set_code_tx.to_) y.(T.set_code_tx.to_);
     Byte_string.Bytes.equal x.(T.set_code_tx.data) y.(T.set_code_tx.data);
     Numeric.Uint.equal x.(T.set_code_tx.max_fee_per_gas)
       y.(T.set_code_tx.max_fee_per_gas);
     Numeric.Uint.equal x.(T.set_code_tx.max_priority_fee_per_gas)
       y.(T.set_code_tx.max_priority_fee_per_gas);
     list_equal access_equal x.(T.set_code_tx.access_list)
       y.(T.set_code_tx.access_list);
     list_equal authorization_equal x.(T.set_code_tx.authorization_list)
       y.(T.set_code_tx.authorization_list);
     Numeric.Uint.equal x.(T.set_code_tx.chain_id) y.(T.set_code_tx.chain_id);
     Numeric.U8.equal x.(T.set_code_tx.y_parity) y.(T.set_code_tx.y_parity)].

Definition transaction_equal (x y : T.t) : bool :=
  match x, y with
  | T.Legacy x, T.Legacy y => legacy_equal x y
  | T.AccessList x, T.AccessList y => access_list_equal x y
  | T.FeeMarket x, T.FeeMarket y => fee_market_equal x y
  | T.SetCode x, T.SetCode y => set_code_equal x y
  | _, _ => false
  end.

Definition header_equal (x y : E.Block.Header.t) : bool :=
  all
    [String.eqb x.(E.Block.Header.t.parent_hash)
       y.(E.Block.Header.t.parent_hash);
     String.eqb x.(E.Block.Header.t.ommers_hash)
       y.(E.Block.Header.t.ommers_hash);
     E.Address.equal x.(E.Block.Header.t.beneficiary)
       y.(E.Block.Header.t.beneficiary);
     String.eqb x.(E.Block.Header.t.state_root)
       y.(E.Block.Header.t.state_root);
     String.eqb x.(E.Block.Header.t.transactions_root)
       y.(E.Block.Header.t.transactions_root);
     String.eqb x.(E.Block.Header.t.receipts_root)
       y.(E.Block.Header.t.receipts_root);
     Bloom.equal x.(E.Block.Header.t.logs_bloom)
       y.(E.Block.Header.t.logs_bloom);
     Numeric.Uint.equal x.(E.Block.Header.t.difficulty)
       y.(E.Block.Header.t.difficulty);
     Numeric.Uint.equal x.(E.Block.Header.t.number)
       y.(E.Block.Header.t.number);
     Numeric.Uint.equal x.(E.Block.Header.t.gas_limit)
       y.(E.Block.Header.t.gas_limit);
     Numeric.Uint.equal x.(E.Block.Header.t.gas_used)
       y.(E.Block.Header.t.gas_used);
     Numeric.U256.equal x.(E.Block.Header.t.timestamp)
       y.(E.Block.Header.t.timestamp);
     Byte_string.Bytes.equal x.(E.Block.Header.t.extra_data)
       y.(E.Block.Header.t.extra_data);
     String.eqb x.(E.Block.Header.t.prev_randao)
       y.(E.Block.Header.t.prev_randao);
     String.eqb x.(E.Block.Header.t.nonce) y.(E.Block.Header.t.nonce);
     Numeric.Uint.equal x.(E.Block.Header.t.base_fee_per_gas)
       y.(E.Block.Header.t.base_fee_per_gas);
     String.eqb x.(E.Block.Header.t.withdrawals_root)
       y.(E.Block.Header.t.withdrawals_root);
     Numeric.U64.equal x.(E.Block.Header.t.blob_gas_used)
       y.(E.Block.Header.t.blob_gas_used);
     Numeric.U64.equal x.(E.Block.Header.t.excess_blob_gas)
       y.(E.Block.Header.t.excess_blob_gas);
     String.eqb x.(E.Block.Header.t.parent_beacon_block_root)
       y.(E.Block.Header.t.parent_beacon_block_root);
     String.eqb x.(E.Block.Header.t.requests_hash)
       y.(E.Block.Header.t.requests_hash)].

Definition withdrawal_equal (x y : E.Withdrawal.t) : bool :=
  all
    [Numeric.U64.equal x.(E.Withdrawal.t.global_index)
       y.(E.Withdrawal.t.global_index);
     Numeric.U64.equal x.(E.Withdrawal.t.validator_index)
       y.(E.Withdrawal.t.validator_index);
     E.Address.equal x.(E.Withdrawal.t.recipient)
       y.(E.Withdrawal.t.recipient);
     Numeric.U256.equal x.(E.Withdrawal.t.amount)
       y.(E.Withdrawal.t.amount)].

Definition equal (x y : E.Block.t) : bool :=
  all
    [header_equal x.(E.Block.t.header) y.(E.Block.t.header);
     list_equal transaction_equal x.(E.Block.t.transactions)
       y.(E.Block.t.transactions);
     list_equal header_equal x.(E.Block.t.ommers) y.(E.Block.t.ommers);
     list_equal withdrawal_equal x.(E.Block.t.withdrawals)
       y.(E.Block.t.withdrawals)].
