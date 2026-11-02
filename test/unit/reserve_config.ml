open Monad_lib
open Chain.Ethereum
open Numeric
open Byte_string
open State
open Lens.Infix

module Params = struct
  let revision = `Eleven
  let chain_id = Uint.one
  let trace = false
end
module E = Execution.Make (Params)
module Eight = Execution.Make (struct
  include Params
  let revision = `Eight
end)
module Nine = Execution.Make (struct
  include Params
  let revision = `Nine
end)
module P = struct
  let address = Reserve_balance.precompile_address
  let selector_get_k = Bytes.(~@"0xee39e7a0")
  let selector_get_reserve = Bytes.(~@"0x15226b54")
  let selector_set_reserve = Bytes.(~@"0x0cbbb4f6")
  let precompile msg = Option.get (E.Precompiles.try_precompile msg address)
end

let a = Address.of_hex_string "0x2000"
let b = Address.of_hex_string "0x3000"
let encode n = U256.(to_repr_bytes (of_int n))
let call_data selector n = selector ^ encode n
let initial block =
  let state = TransactionState.empty in
  { state with
    tx_origin = a
  ; current_block =
      {state.current_block with header = {state.current_block.header with number = Uint.of_int block}} }

let message input_data =
  Evmc.Message.
    { kind = Call
    ; static = false
    ; delegated = false
    ; depth = 0l
    ; gas = 200_000L
    ; recipient = P.address
    ; sender = a
    ; input_data
    ; value = U256.zero
    ; create2_salt = B32.zeros
    ; code_address = P.address
    ; code = Bytes.empty
    ; memory_capacity = 8_388_608l }

let check name condition = if not condition then failwith name
let successful result = match result.Evmc.Result.status_code with Success -> true | _ -> false
let reverted result = match result.Evmc.Result.status_code with Revert -> true | _ -> false

(* Compare every state field; maps and sets are compared by entries, not tree shape. *)
let world_equal (x : WorldState.t) (y : WorldState.t) =
  List.equal Block.equal x.history y.history
  && Address.Map.equal Account.equal x.accounts y.accounts
  && Address.Map.equal Uint.( = ) x.next_emptying_transaction_block y.next_emptying_transaction_block

let log_equal (x : Log.t) (y : Log.t) =
  Address.(x.address = y.address) && List.equal B32.( = ) x.topics y.topics && Bytes.(x.data = y.data)

let transaction_state_equal (x : TransactionState.t) (y : TransactionState.t) =
  world_equal x.initial_world_state y.initial_world_state
  && world_equal x.world_state y.world_state
  && Block.equal x.current_block y.current_block
  && Address.Map.equal (B32.Map.equal B32.( = )) x.transient_storage y.transient_storage
  && Address.Set.equal x.accounts_created_in_current_transaction y.accounts_created_in_current_transaction
  && Address.(x.tx_origin = y.tx_origin)
  && Gas.(x.tx_gas_price = y.tx_gas_price && x.tx_gas_limit = y.tx_gas_limit)
  && Address.Set.equal x.self_destruct y.self_destruct
  && List.equal log_equal x.logs y.logs
  && U256.(x.refund = y.refund)
  && Address.Set.equal x.accessed_addresses y.accessed_addresses
  && TransactionState.StorageKey.Set.equal x.accessed_keys y.accessed_keys

let active (state : TransactionState.t) block addr =
  Reserve_balance.user_reserve_balance state.world_state (Uint.of_int block) addr

let () =
  List.iter
    (fun (signature, selector) ->
      let actual = Bytes.sub (B32.to_bytes (Crypto.keccak_256 signature)) 0 4 in
      check ("ABI selector: " ^ signature) (String.equal actual selector) )
    [ ("getK()", P.selector_get_k)
    ; ("getReserveBalance(address)", P.selector_get_reserve)
    ; ("setReserveBalance(uint256)", P.selector_set_reserve) ] ;
  check "revision 11 is selectable"
    (Option.equal Chain.Monad.Revision.equal (Chain.Monad.Revision.of_string "MONAD_ELEVEN") (Some `Eleven)) ;
  check "revision 11 is executable"
    (match Chain.Monad.Revision.is_active `Eleven with Some `Eleven -> true | _ -> false) ;
  let s = initial 10 in
  let introspection = message Bytes.(~@"0x3a61584e") in
  check "revision 8 has no reserve precompile"
    (Option.is_none (Eight.Precompiles.try_precompile introspection P.address)) ;
  let run9 msg = Option.get (Nine.Precompiles.try_precompile msg P.address) s in
  let r, unchanged = run9 introspection in
  check "revision 9 retains introspection" (successful r && transaction_state_equal unchanged s) ;
  List.iter
    (fun data ->
      let r, unchanged = run9 (message data) in
      check "revision 9 rejects QEDK selectors without writes"
        ((not (successful r)) && transaction_state_equal unchanged s) )
    [P.selector_get_k; call_data P.selector_get_reserve 0; call_data P.selector_set_reserve 7] ;
  let configured =
    Option.get (Reserve_balance.set_reserve_balance s.world_state Uint.zero a (U256.of_int 7))
  in
  let world = configured.^(WorldState.account a |-- Account.balance) <- U256.of_int 20 in
  let post = world.^(WorldState.account a |-- Account.balance) <- U256.of_int 9 in
  let s = {s with tx_origin = b; initial_world_state = world; world_state = post} in
  List.iter
    (fun revision ->
      check "historical revisions ignore configuration storage"
        (fst (Reserve_balance.dipped_into_reserve revision s)) )
    [`Eight; `Nine] ;
  check "revision 11 uses configured threshold" (not (fst (Reserve_balance.dipped_into_reserve `Eleven s))) ;
  let header =
    { Block.Header.empty with
      gas_limit = Gas.of_int 1_000_000
    ; ommers_hash = Crypto.keccak_256 Rlp.(encode (List [])) }
  in
  let parent = {Block.empty with header} in
  let world = {WorldState.empty with history = [parent]} in
  let block = {parent with header = {header with number = Uint.one}} in
  let after8 = Result.get_ok (Eight.process_block ~verify:false world block) in
  let after9 = Result.get_ok (Nine.process_block ~verify:false world block) in
  let after11 = Result.get_ok (E.process_block ~verify:false world block) in
  check "revision 8 does not initialize 0x1001" (not (Address.Map.mem P.address after8.accounts)) ;
  check "revision 9 does not initialize 0x1001" (not (Address.Map.mem P.address after9.accounts)) ;
  check "revision 11 initializes 0x1001" U64.(after11.^(WorldState.account P.address).nonce = one) ;
  let world = world.^(WorldState.account a |-- Account.balance) <- Chain.Monad.mon_to_wei U256.(~$20) in
  let world = world.^(WorldState.next_emptying_transaction_block_for a) <- Uint.of_int 100 in
  let s =
    { (initial 10) with
      initial_world_state = world
    ; world_state = world
    ; tx_gas_limit = Gas.of_int 11
    ; tx_gas_price = Chain.Monad.(mon_to_wei U256.one) |> U256.to_uint }
  in
  List.iter
    (fun revision ->
      let check_fee name before after fee emptying expected =
        let world =
          s.initial_world_state.^(WorldState.account a |-- Account.balance) <-
            Chain.Monad.mon_to_wei (U256.of_int before)
        in
        let world =
          world.^(WorldState.next_emptying_transaction_block_for a) <-
            (if emptying then Uint.zero else Uint.of_int 100)
        in
        let post =
          world.^(WorldState.account a |-- Account.balance) <- Chain.Monad.mon_to_wei (U256.of_int after)
        in
        let state = {s with initial_world_state = world; world_state = post; tx_gas_limit = Gas.of_int fee} in
        let violated, unchanged = Reserve_balance.dipped_into_reserve revision state in
        check name (Bool.equal violated expected) ;
        check "reserve check is read-only" (transaction_state_equal unchanged state)
      in
      check_fee "every revision rejects fees above reserve" 20 20 11 false true ;
      check_fee "emptying sender may pay fees above reserve" 20 0 11 true false ;
      check_fee "fee exactly equal to reserve permits zero remainder" 20 0 10 false false ;
      check_fee "insufficient remainder below reserve minus fee rejects" 20 0 9 false true ;
      check_fee "exact required remainder passes" 20 1 9 false false ;
      check_fee "protected amount is capped by entry balance" 5 0 6 false true ;
      check_fee "fee exactly equal to entry balance passes" 5 0 5 false false ;
      let huge_fee = {s with tx_gas_limit = Uint.shift_left Uint.one 256; tx_gas_price = Uint.one} in
      check "fee above U256 range rejects without conversion overflow"
        (fst (Reserve_balance.dipped_into_reserve revision huge_fee)) ;
      let nonsender = {s with tx_origin = b} in
      check "nonsender has no fee deduction or excessive-fee rejection"
        (not (fst (Reserve_balance.dipped_into_reserve revision nonsender))) )
    [`Eight; `Nine; `Eleven]

let () =
  let s = initial 10 in
  check "default" U256.(active s 10 a = Reserve_balance.default_reserve_balance) ;
  let msg = message (call_data P.selector_set_reserve 0) in
  let r, s1 = P.precompile msg s in
  check "schedule zero" (successful r && Bytes.(r.output_data = encode 13) && Int64.equal r.gas_left 50_000L) ;
  check "zero not active early" U256.(active s1 12 a = Reserve_balance.default_reserve_balance) ;
  check "zero active at boundary" U256.(active s1 13 a = zero) ;
  let raw = Reserve_balance.stored_config s1.world_state a in
  check "activation does not clear slots" Uint.(raw.valid_from = ~$13 && raw.pending = zero) ;
  let r, s2 = P.precompile (message (call_data P.selector_set_reserve 7)) s1 in
  check "same block last wins" (successful r && U256.(active s2 13 a = ~$7)) ;
  let later = {s2 with current_block = (initial 11).current_block} in
  let r, failed = P.precompile (message (call_data P.selector_set_reserve 9)) later in
  check "prior pending rejects without writes"
    ( (not (successful r))
    && Int64.equal r.gas_left 0L
    && Bytes.(r.output_data = empty)
    && transaction_state_equal failed later ) ;
  let mature = {s2 with current_block = (initial 13).current_block} in
  let r, s3 = P.precompile (message (call_data P.selector_set_reserve 9)) mature in
  check "reschedule after maturity" (successful r && U256.(active s3 15 a = ~$7 && active s3 16 a = ~$9)) ;
  let query = message (P.selector_get_reserve ^ B32.to_bytes (Address.to_bytes32 a)) in
  let r, unchanged = P.precompile query mature in
  check "getter logical promotion only"
    ( successful r
    && Bytes.(r.output_data = encode 7 ^ encode 7 ^ encode 0)
    && transaction_state_equal unchanged mature ) ;
  let r, unchanged = P.precompile (message P.selector_get_k) s in
  check "getK"
    ( successful r
    && Bytes.(r.output_data = encode 3)
    && Int64.equal r.gas_left 199_900L
    && transaction_state_equal unchanged s ) ;
  List.iter
    (fun bad ->
      let r, unchanged = P.precompile bad s in
      check "invalid invocation"
        ( (not (successful r))
        && Int64.equal r.gas_left 0L
        && Bytes.(r.output_data = empty)
        && transaction_state_equal unchanged s ) )
    [ {msg with static = true}
    ; {msg with delegated = true}
    ; {msg with kind = DelegateCall}
    ; {msg with kind = CallCode}
    ; {msg with value = U256.one}
    ; {msg with gas = 149_999L}
    ; {msg with input_data = msg.input_data ^ "\x00"}
    ; {query with input_data = P.selector_get_reserve ^ "\x01" ^ Bytes.make 31 '\x00'} ] ;
  let overflow =
    { s with
      current_block =
        {s.current_block with header = {s.current_block.header with number = U256.to_uint U256.max_t}} }
  in
  let r, unchanged = P.precompile msg overflow in
  check "activation overflow" ((not (successful r)) && transaction_state_equal unchanged overflow) ;
  let payer_is_b = {s with tx_origin = b} in
  let r, sponsored = P.precompile msg payer_is_b in
  check "immediate caller not payer"
    ( successful r
    && U256.(active sponsored 13 a = zero && active sponsored 13 b = Reserve_balance.default_reserve_balance)
    ) ;
  (* The helper executes the real CALL opcode, then STOP or REVERT. *)
  let helper suffix =
    Bytes.of_hex_string ("0x630cbbb4f660e01b5f52600760045260205f60245f5f611001620249f0f150" ^ suffix)
  in
  let world = Reserve_balance.activate_precompile s.world_state in
  let world = world.^(WorldState.account b) <- {Account.empty with nonce = U64.one; code = helper "00"} in
  let s = {s with world_state = world; initial_world_state = world} in
  let msg = {(message "") with recipient = b; code_address = b; gas = 300_000L} in
  let r, written = E.Host.call_impl ~from_tx:None msg s in
  check "VM helper sets its own reserve"
    ( successful r
    && U256.(active written 13 b = ~$7 && active written 13 a = Reserve_balance.default_reserve_balance) ) ;
  let sponsor = Address.of_hex_string "0x4000" in
  let delegated_world = world.^(WorldState.account a |-- Account.code) <- Delegation.delegation_code b in
  let delegated_state =
    {s with tx_origin = sponsor; world_state = delegated_world; initial_world_state = delegated_world}
  in
  let delegated_tx =
    Transaction.Legacy
      { nonce = U64.zero
      ; gas_price = Gas.one
      ; gas_limit = Gas.of_int 300_000
      ; to_ = Some a
      ; value = U256.zero
      ; data = Bytes.empty
      ; v = U256.of_int 27
      ; r = U256.one
      ; s = U256.one }
  in
  let delegated_msg = E.prepare_message sponsor (Gas.of_int 300_000) delegated_tx delegated_world in
  let r, written = E.Host.call_from_eoa delegated_tx delegated_msg delegated_state in
  check "delegated nonsender sets its own reserve, not sponsor or code target"
    ( successful r
    && U256.(
         active written 13 a = ~$7
         && active written 13 b = Reserve_balance.default_reserve_balance
         && active written 13 sponsor = Reserve_balance.default_reserve_balance ) ) ;
  let world = world.^(WorldState.account b |-- Account.code) <- helper "5f5ffd" in
  let s = {s with world_state = world; initial_world_state = world} in
  let r, after_revert = E.Host.call_impl ~from_tx:None msg s in
  check "actual VM call rollback" (reverted r && world_equal after_revert.world_state world) ;
  let world = world.^(WorldState.account b |-- Account.code) <- helper "00" in
  let world = world.^(WorldState.account a |-- Account.balance) <- U256.of_int 20 in
  let world = world.^(WorldState.next_emptying_transaction_block_for a) <- Uint.of_int 100 in
  let s = {s with world_state = world; initial_world_state = world} in
  let tx =
    Transaction.Legacy
      { nonce = U64.zero
      ; gas_price = Gas.zero
      ; gas_limit = Gas.of_int 300_000
      ; to_ = Some b
      ; value = U256.of_int 15
      ; data = Bytes.empty
      ; v = U256.of_int 27
      ; r = U256.one
      ; s = U256.one }
  in
  let r, after_revert = E.Host.call_from_eoa tx {msg with value = U256.of_int 15} s in
  check "final reserve check rolls back setter and transfer"
    (reverted r && world_equal after_revert.world_state world) ;
  let world = Option.get (Reserve_balance.set_reserve_balance world Uint.zero a (U256.of_int 10)) in
  let post = world.^(WorldState.account a |-- Account.balance) <- U256.of_int 9 in
  let s =
    { s with
      initial_world_state = world
    ; world_state = post
    ; tx_gas_limit = Gas.of_int 11
    ; tx_gas_price = Gas.one }
  in
  let dipped, unchanged = Reserve_balance.dipped_into_reserve `Eleven s in
  check "fee above protected amount rejects despite saturating subtraction"
    (dipped && transaction_state_equal unchanged s) ;
  print_endline "QEDK configuration and VM rollback tests passed"
