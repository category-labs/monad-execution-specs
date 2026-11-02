(* Public test key 1 only. Never use this key for funds. This fixture also
   appears in the concrete QEDK Rocq development. *)
open Monad_lib
open Chain.Ethereum
open Numeric
open Byte_string
open State
open Lens.Infix

module E = Execution.Make (struct
  let revision = `Eleven
  let chain_id = Uint.one
  let trace = false
end)

let check label result = if not result then failwith label
let context = Libsecp256k1.External.Context.create ~sign:true ~verify:true ()
let key = Libsecp256k1.External.Key.read_sk_exn context (Bigstring.of_string (U256.to_repr_bytes U256.one))
let alice = Address.of_hex_string "7e5f4552091a69125d5dfcb7b8c2659029395bdf"
let price = Uint.of_string "200000000000000"
let high = U256.of_string "100000000000000000000"

let sign hash =
  let open Libsecp256k1.External in
  let signature = Sign.sign_recoverable_exn context ~sk:key (Bigstring.of_string (B32.to_bytes hash)) in
  let bytes = Bigstring.to_string (Sign.to_bytes context signature) in
  check "recoverable signature has 65 bytes" (String.length bytes = 65) ;
  ( U256.of_bytes_be_exn (String.sub bytes 0 32)
  , U256.of_bytes_be_exn (String.sub bytes 32 32)
  , U8.of_int (Char.code bytes.[64]) )

let auth =
  let chain_id = U256.one and address = Address.zeros and nonce = U64.of_int 2 in
  let hash =
    Crypto.keccak_256
      (Delegation.magic ^ Rlp.(encode (List [U256.to_rlp chain_id; Address.to_rlp address; U64.to_rlp nonce])))
  in
  let r, s, y_parity = sign hash in
  Transaction.Authorization.{chain_id; address; nonce; r; s; y_parity}

let tx =
  let body =
    Transaction.
      { nonce = U64.one
      ; gas_limit = Uint.of_int 100000
      ; value = U256.zero
      ; r = U256.one
      ; s = U256.one
      ; to_ = alice
      ; data = Bytes.empty
      ; max_fee_per_gas = price
      ; max_priority_fee_per_gas = Uint.zero
      ; access_list = []
      ; authorization_list = [auth]
      ; chain_id = Uint.one
      ; y_parity = U8.zero }
  in
  let r, s, y_parity = sign (Transaction.signing_hash Uint.one (SetCode body)) in
  Transaction.SetCode {body with r; s; y_parity}

let run () =
  check "transaction signature recovers Alice"
    (Option.equal Address.( = ) (Transaction.sender Uint.one tx) (Some alice)) ;
  check "self-authorization signature recovers Alice"
    (Option.equal Address.( = ) (Transaction.Authorization.authority auth) (Some alice)) ;
  let before = WorldState.empty.^(WorldState.account alice |-- Account.balance) <- high in
  let before = before.^(WorldState.account alice |-- Account.nonce) <- U64.one in
  let after = Option.get (Reserve_balance.set_reserve_balance before (Uint.of_int 100) alice high) in
  check "reserve activates at 103"
    U256.(Reserve_balance.user_reserve_balance after (Uint.of_int 103) alice = high) ;
  let header =
    { Block.Header.empty with
      number = Uint.of_int 106
    ; base_fee_per_gas = price
    ; gas_limit = Uint.of_int 1000000 }
  in
  let block = {Block.empty with header; transactions = [tx]} in
  let auth_state = {TransactionState.empty with world_state = after; current_block = block} in
  let rejected_auth = E.process_authorization auth_state auth in
  check "recovered authorization with wrong nonce still delays emptying"
    Uint.(rejected_auth.world_state.^(WorldState.next_emptying_transaction_block_for alice) = of_int 109) ;
  check "rejected authorization leaves nonce and code unchanged"
    ( U64.(rejected_auth.world_state.^(WorldState.account alice).nonce = one)
    && Bytes.(rejected_auth.world_state.^(WorldState.account alice).code = empty) ) ;
  let state = BlockState.make after block in
  let validation = Result.get_ok (E.validate_transaction state tx) in
  check "native validator accepts sender" Address.(validation.sender = alice) ;
  let post = Result.get_ok (E.process_transaction state tx) in
  check "sender and self-authorization both consume nonces"
    U64.(post.world_state.^(WorldState.account alice).nonce = of_int 3) ;
  check "transaction produces a successful receipt"
    ( List.length post.transactions_processed = 1
    && (snd (List.hd post.transactions_processed)).Receipt.succeeded )

let () =
  run () ;
  print_endline "PASS: real sender/auth recovery, native validation, execution and nonce 3."
