# Handoff: porting the C++ staking fuzzer to OCaml

This file hands over a long Claude Code session to another Claude instance. It covers the goal, every design
decision and its rationale, the current state of the code, what has been tested, and what's left.

The OCaml repo is `~/code/ocaml/staking` (branch `malvarez/staking`). The C++ fuzzer is in
`~/monad/category/execution/monad/staking/fuzzer/`. **`test/fuzz/` is untracked in git.** It isn't committed,
so it has to be copied along with this file.

---

## 1. Working with this user

- **Never change code in response to a question.** This is the user's global CLAUDE.md rule, quoted: "Never make
  code changes in response to a question. A question ("Wouldn't it be better to…?", "Should we…?", "Does
  this…?") gets an answer, not an edit, even when the answer is "yes". Only edit code when explicitly asked to
  make the change."
- **The user dislikes over-engineering.** An earlier proposal (a `Check` module, Scenario/GENERATOR module types)
  was rejected as "huge overengineering". Keep things minimal.
- **The user writes `test/fuzz/lib/fuzz.ml` themselves.** Review it when asked, but don't rewrite it. The only
  edit made to it was appending `module Choice = Choice`, which dune needs (see §7).
- **Stop and ask on design choices.** For the staking instantiation, the user said: "Stop immediately and ask me
  if you are faced with a design choice or any difficulties."
- **Present real options when unsure.** The user pushes back on weak reasoning. Earlier, the claim "moving
  invariants to CONCRETE settles where `init` goes" was rightly called a non sequitur. If you don't know, say
  so.
- **Follow the project CLAUDE.md** in the repo root:
  - pure functional `lib/`, mutability only outside `lib/`;
  - `-open Monomorphic`, so polymorphic comparison is a type error;
  - `result` rather than exceptions, except for programming errors;
  - ocamlformat 0.28.1 with margin 110;
  - lens idioms.

## 2. The C++ fuzzer (source of truth)

Files in `~/monad/category/execution/monad/staking/fuzzer/`:

- **`staking_contract_fuzzer.cpp`** (driver):
  - Options are `--seed` (default 0), `--depth` (default 100), `--runs` (default max u64) and `--monad-rev`
    (default MONAD_NEXT).
  - Each run's seed is the last `machine.gen()` of the previous run.
  - Prints the success ratio (the share of transitions that returned `ok`) and the time.
  - `gen_transition`: `p = gen() % 100`. `p < 20` gives `syscall_reward`, `p < 30` gives `external_reward`, and
    anything else is uniform over `TRANSITION_COUNT`. That count is 13 including `distribute_priority_fees`
    when MIP-11 is active, otherwise 12.
- **`staking_contract_model.{hpp,cpp}`**: wraps the real `StakingContract`. Each call does a `State` push and pop,
  and `pre_call` credits the call's value to `STAKING_CA` before the call. It also holds the **shadow ledger**:
  - `error_bound`: an upper bound on reward rounding error. Each operation adds 1 or 3.
  - `unit_bias_rewards[(v, a)]`: rewards distributed but not yet claimed, times `UNIT_BIAS` (1e36).
  - `active_consensus_stake[v]` and `active_consensus_commission[v]`: reloaded from `valset_consensus` and
    `consensus_view` after each epoch change.
  - `delegator_stake[(v, a)]`: a map from epoch to stake, where the stake at epoch e is the entry for the
    largest key ≤ e. Adding a delta also adds it to every later key.
  - `withdrawal_stake[(v, a, e)]`: undelegated stake that still earns rewards in epoch e.
  - `val_id_to_historic_delegators` and `delegator_to_active_withdrawal_ids`.
  - `distribute_reward(v, r)`: `rr = r * UNIT_BIAS / active_stake`. Each historic delegator gets
    `(delegator_stake + withdrawal_stake) * rr`, and it asserts that the stakes add up to the active stake.
  - Arithmetic is wrapping uint256, so decreases are added as two's complements.
  - Rewards for compound and claim are read from the contract **before** the call:
    `unaccumulated_rewards + delegator.rewards`. For withdraw it's `withdrawal_reward`, also read before.
- **`staking_contract_machine.{hpp,cpp}`** (2,200 lines): generators, transitions, postconditions and invariants.
  - It keeps bookkeeping for the generators: `all_addresses_`, `all_delegators_`,
    `validator_auth_addresses_`, `val_id_to_signer_`, `all_val_ids_`, `delegable_val_ids_`,
    `available_withdrawal_ids_` and `all_withdrawal_requests_`.
  - `transition()` runs the chosen transition. Then, with probability 0.2, it calls
    `skip_epochs(WITHDRAWAL_DELAY)`, and finally `assert_all_invariants()`.
  - The constructor has a 0.1% chance each of first adding 199 (`ACTIVE_VALSET_SIZE - 1`) or 260 validators,
    with stake in `[ACTIVE_VALIDATOR_STAKE, MAX_STAKE]`.
  - The six invariant groups are valset, val_execution, delegator, accumulated_rewards, linked_list and
    solvency.
  - Every call is expected to succeed (`MONAD_ASSERT`).
- **`~/monad/category/vm/fuzzing/choice.hpp`**: `discrete_choice`, `with_probability`, `uniform_sample` and
  `UniformSamplingSet`.

## 3. The OCaml spec: facts you will need

- **`lib/staking.ml` entry points:**

  | Function | Input |
  | --- | --- |
  | `add_validator_function` | raw, `(message, secp_sig, bls_sig)` bytes, payable; returns a `Val_id` |
  | `delegate_function` | `val_id` |
  | `undelegate_function` | `(v, amount, U8 wid)` |
  | `compound_function` | `val_id` |
  | `withdraw_function` | `(v, wid)` |
  | `claim_rewards_function` | `val_id` |
  | `change_commission_function` | `(v, commission)` |
  | `external_reward_function` | `val_id` |
  | `get_delegator_function` | `(v, addr)` |
  | `syscall_on_epoch_change_function` | `Epoch` |
  | `syscall_snapshot_function` | `()` |
  | `syscall_reward_function` | `Address`; payable, see below |

  - The dispatchers are `Staking.precompile` and `Staking.staking_syscalls`.
  - `syscall_reward` **adds `value` to the staking balance itself** and sets `proposer_val_id`.
  - **There is no `distribute_priority_fees`**, and the spec is **not parameterised by revision**.
- **Constants:**
  - `mon` = 1e18;
  - `dust_threshold` = 1e9, which is also `min_external_reward`;
  - `active_validator_stake` = 10M MON;
  - `min_auth_address_stake` = 100k MON;
  - `unit_bias` = 1e36;
  - `active_valset_size` = 200;
  - `withdrawal_delay` = 1;
  - `max_external_reward` = 10M MON;
  - `max_commission` = MON.
- **Reading storage outside the monad:**
  - a single value: `st.^(Staking.Storage.Loc.lens loc)`;
  - an array: `fst (Staking.Storage.Array.read_to_list arr st)`;
  - a linked list: `Staking.Delegators_for_validator.traverse v Address.zero max_int st`, or
    `Staking.Validators_for_delegator.traverse a Val_id.zero max_int st`. Both return
    `(Ok (done, next, list), st)`.
- **`Variables` locations that return options:** `Variables.val_id addr` returns `Val_id.t option`, and
  `Variables.withdrawal_request (v, a, u8)` returns `Withdrawal_request.t option`.
- **`test/unit/staking.ml` helpers:**
  - `call` does ABI encoding, dispatches, and rolls back on error. It does **not** transfer value, so the
    caller must credit the staking balance.
  - Also there: `syscall`, `error_of_output_string`, and `craft_add_validator_input`, which derives secp and BLS
    keys from a 32-byte secret.
  - `initial_state` sets epoch = 1. The fuzzer starts at epoch 0, as the C++ does.
- **`Delegator.next_epoch_stake`** is `stake + delta_stake + next_delta_stake`.

## 4. Architecture decisions (agreed with the user)

1. **No outer functor around the whole library.** A narrow runner functor `Fuzz.Run (C : CONCRETE)` has been
   proposed but not yet decided.
2. **MODEL plus a concretization (CONCRETE).** Generation is fully separate from both.
3. **`step` takes `res`.** The user's view: `val next : t -> cmd -> t` "is what a transition system *is*", but
   practicality wins. A pure `next` would have to predict val_ids, track epochs and pick snapshots (all cheap)
   and do exact accumulator reward arithmetic (expensive).
4. **Invariants (`check`) belong to the concretization.**
5. **`step` returns `(t, error) result`.** MODEL and CONCRETE have **separate** error types:
   - A shared type would have to live in MODEL, since CONCRETE contains Model, which would make the model own
     concrete failures.
   - The runner tags which phase failed.
   - Errors carry only what the runner lacks.
   - The runner catches exceptions.
6. **The user removed every pretty-printer from the signatures.** The specific fuzzer, which knows the concrete
   types, prints failures.
7. **The model error doc keeps the user's wording:** "the command cannot be executed in the current state". It
   is correct: `step` is a partial transition function. An optional refinement is "with result [res]". The
   order the runner calls things in is not part of what `step` means.
8. **Staking-specific answers from the user:**
   - The **generator reads both** the model and the concrete state.
   - **`res`** carries what the C++ model reads from the contract:
     - `add_validator`: the new val_id;
     - `syscall_on_epoch_change`: the new consensus set, with stake and commission;
     - `compound`, `claim_rewards`, `withdraw`: the exact rewards, computed from the state before the call;
     - everything else: `Unit`.
   - **Postconditions that only compare the ledger with itself are dropped.**
   - **`call`, `syscall`, `error_of_output_string` and `craft_add_validator_input` are duplicated** into the
     fuzzer rather than moved. They are staking-specific, so they stay out of `test_utils`.
9. **Generator shape:**
   - `type 'e emit = state -> Model.cmd -> (state, 'e) result`, where `state = Model.t * Concrete.t`.
   - Transitions have type `Random.State.t -> emit:'e emit -> state -> (state * bool, 'e) result`, where the
     `bool` is the C++ `ok`.
   - The state comes back even when the transition fails to generate, because setup commands may already have
     run.
   - Multi-call C++ transitions (skip epochs, add a validator when none exists, snapshot before an epoch
     change) emit several commands.
10. **Each command is one contract call.**

### Still open

- **Starting states.**
  - Option (1): the genesis pair plus setup commands. It's sound by reachability, and the pair can be reused
    across runs because states are immutable.
  - Option (2): a builder from a config to a pair. It risks unsoundness and duplicates the storage layout.
  - Option (3): `abstract : concrete -> model`, for starting from chain snapshots.
  - Possible API: an abstract start-pair type that can only be built from genesis, a setup run, or
    abstraction.
  - The user was "extremely unconvinced" by (1). This is unresolved. Today both modules have an `init`.
- **How often to check.** We run `check` after every command. The C++ checks once per transition, after any
  epoch skip.
- **Where the runner lives, and its exact API.** §6 has a sketch.

## 5. Current code (builds, passes the ocamlformat check)

### `test/fuzz/lib/` (library `fuzz`)

- **`dune`:** `(library (name fuzz) (libraries monad_lib alcotest qcheck-core qcheck-alcotest))`.
- **`fuzz.ml`** (written by the user):
  - `MODEL` has `t`, `cmd`, `res`, `error`, `step : t -> cmd -> res -> (t, error) result`, and `init`.
  - `CONCRETE` has `module Model : MODEL`, `t`, `error`, `exec : Model.cmd -> t -> (Model.res * t, error) result`,
    `check : Model.t -> t -> (unit, error) result`, and `init`.
  - Then `module Choice = Choice`.
- **`choice.ml`**:
  - `discrete_choice rng ~default [(p, thunk); ...]`;
  - `with_probability rng p : bool`;
  - `sample rng list` (O(n));
  - `bytes rng n`, `u64 rng`, `u256 rng`;
  - `bound_biased_u256 rng ~lower ~upper`.

### `test/fuzz/staking/` (library `fuzz_staking`, depends on `monad_lib fuzz test_utils`)

`staking.ml` is about 1,575 lines.

- **Top level:**
  - constants named as in the C++ (`max_stake = unit_bias`, `max_delegable_stake = max_stake - dust`);
  - `epoch_add`;
  - `Delegator_key`, `Delegator_map`, `Delegator_set`, `Int_set`.
- **`Model`:**
  - `cmd` has 12 constructors: `Syscall_on_epoch_change`, `Syscall_snapshot`, `Syscall_reward`, `Add_validator`,
    `Delegate`, `Undelegate`, `Compound`, `Withdraw`, `Claim_rewards`, `Change_commission`, `External_reward`
    and `Get_delegator`.
  - `Add_validator` carries the raw `message`, the two signatures, `signer`, `sender` and `value`, as in the
    C++. The auth address is parsed from bytes 81 onwards of the message.
  - `res` is `Unit`, `Validator_added`, `Epoch_changed` (a list of val_id and `Consensus_view`) or `Rewards`.
  - `error` is one of:
    - `Invalid_epoch_change`;
    - `Snapshot_in_delay_period`;
    - `Validator_exists`;
    - `Unknown_block_author`;
    - `Inactive_validator`;
    - `Stake_mismatch`, which is the C++ assertion in `distribute_reward`.
  - `t` contains:
    - `epoch` and `in_epoch_delay_period`, which the model tracks itself;
    - the shadow ledger;
    - bookkeeping: `addresses`, `validators` (signer and auth address), `signers`, `delegable_val_ids`,
      `delegators`.
  - `withdrawal_ids` is the **single** structure that replaces the C++'s three copies of the pending withdrawal
    ids.
  - Bookkeeping facts that the C++ read back from the contract after a call are **derived from the ledger**:
    - a validator's stake is the sum of its delegators' final ledger stakes;
    - "the delegator's stored stake is zero" becomes "the ledger stake at the current epoch is zero".
  - `step` raises `invalid_arg` if `res` doesn't match the command.
- **Helpers duplicated from `test/unit/staking.ml`:** `error_of_output_string`, `Instantiation` (for
  `max_memory_usage`), `call`, `syscall` and `craft_add_validator_input`.
- **`Concrete`** (`t = TransactionState.t`; `error = Call_failed of Staking.Error.t | Violated of string`):
  - `init` is an empty state with the staking account's nonce set to 1, at epoch 0.
  - Reader helpers, plus ports of `unaccumulated_rewards`, `withdrawal_reward` and `pending_rewards`, which
    read the contract.
  - `precompile` credits `value` to the staking balance before the call, like the C++ `pre_call`.
  - `exec` checks the C++ postconditions on the contract by comparing the old and new states (states are
    immutable, so both are available). Every call must succeed.
  - `check`:
    - first checks that the model's epoch and delay period match the contract (new, not in the C++);
    - then runs the six C++ invariant groups.
  - The `at` helper adds the validator and address to a violation's message.
- **`Gen`:**
  - `new_or_old_address` (80% old);
  - `stake`, which ports `gen_stake`;
  - `any_val_id` and `potential_val_id`;
  - `add_validator ~lower ~upper`, which returns the new validator's id and auth address;
  - `validator_auth_address`, `delegable_val_id`, `delegator`, `active_consensus_val_id`;
  - `skip_epochs`, `undelegate_input` and `compound_input`;
  - the 12 transitions;
  - `start`: a 0.1% chance each of adding 199 or 260 validators, followed by an assertion on the length of
    `valset_execution`;
  - `transition`: the 20/10/70 mix, then a 0.2 chance of `skip_epochs withdrawal_delay`.
- **`module _ : Fuzz.MODEL = Model`** and **`module _ : Fuzz.CONCRETE = Concrete`** check conformance.

### Deliberate differences from the C++

- **Not ported:**
  - `distribute_priority_fees`, which the spec lacks;
  - revisions;
  - the ledger-only postconditions;
  - the machine's sanity assertions on its own bookkeeping;
  - the public-key invariants, which are off by default in the C++;
  - the proposer field in the model. `exec` still checks it after `syscall_reward`.
- **Changed:**
  - The `syscall_reward` postcondition takes the commission from the contract's view for this epoch, before the
    call, rather than from the model's value. The invariants tie the two together.
  - `get_delegator`'s `res` is `Unit`. Its postconditions are in `exec`.
  - A new address only becomes "old" (available for reuse) once a command that uses it has run.
  - RNG draw order differs from the C++, so seeds are not compatible.
  - `check` runs after every command, which is stricter than the C++.
- **Kept:** the C++ edge case where `withdraw`'s setup can reach `gen_stake(1, 0)` if a delegator has used all
  256 withdrawal ids. It's an assertion failure in both.

## 6. Testing done

All of these used throwaway executables, which were deleted afterwards.

- **Hand-written scenario:** 23 commands covering every command type. `exec`, `step` and `check` all passed
  after every command, and the rewards were non-zero.
- **Corruption:**
  - corrupting the ledger's `unit_bias_rewards` was caught by the reward-bound invariant;
  - corrupting a delegator's stake in storage was caught by the ledger stake invariant.
- **Random runs:** 300 runs of 100 transitions, seeds chained from 0. No failures. The success ratio was
  0.67–1.00, and each run took 0.3–0.9 s.
- **Forced bulk validator inserts:**
  - 199 validators: 63 s to insert, then about 0.8 s per transition.
  - 260 validators: 142 s to insert, all 260 in `valset_execution`, then about 2.3 s per transition.
  - **`check` is the bottleneck.** It decodes storage for every validator × address pair after every command.

Runner sketch: this is what the random runs used. The user asked for it as a sketch only; it isn't in the repo.

```ocaml
module Run (C : CONCRETE) = struct
  type state = C.Model.t * C.t
  type failure = Exec of C.error | Step of C.Model.error | Check of C.error | Raised of exn
  type report = {seed : int; transition : int; cmds : C.Model.cmd list; failure : failure}

  let execute ((m, c) : state) cmd : (state, failure) result =
    match C.exec cmd c with
    | Error e -> Error (Exec e)
    | Ok (res, c) -> (
      match C.Model.step m cmd res with
      | Error e -> Error (Step e)
      | Ok m -> ( match C.check m c with Ok () -> Ok (m, c) | Error e -> Error (Check e) ) )

  (* Returns the share of transitions that could be generated, and the next run's seed. *)
  let run ~start ~transition ~seed ~depth =
    let rng = Random.State.make [|seed|] in
    let cmds = ref [] in
    let emit s cmd =
      cmds := cmd :: !cmds ;
      try execute s cmd with e -> Error (Raised e)
    in
    let fail i failure = Error {seed; transition = i; cmds = List.rev !cmds; failure} in
    let rec loop i s generated =
      if i >= depth then Ok (float generated /. float depth, Random.State.bits rng)
      else
        match transition rng ~emit s with
        | Ok (s, ok) -> loop (i + 1) s (if ok then generated + 1 else generated)
        | Error failure -> fail i failure
        | exception e -> fail i (Raised e)
    in
    match start rng ~emit (C.Model.init, C.init) with
    | Ok s -> loop 0 s 0
    | Error failure -> fail (-1) failure
    | exception e -> fail (-1) (Raised e)
end
(* Usage: module R = Run (Fuzz_staking.Staking.Concrete);
   R.run ~start:Gen.start ~transition:Gen.transition ~seed ~depth *)
```

## 7. Gotchas learned in this codebase

- **Local opens shadow `t`.** In `Epoch.( ... t.epoch ...)`, `t` resolves to the value `Epoch.t` (the ABI type)
  and the code fails to compile. Don't name variables `t` inside local opens of
  `Epoch`/`Val_id`/... . Write `Epoch.( <= ) a t.epoch` instead.
- **Int literals inside `U256.( ... )`:** `+` there is U256's, so `of_int (3 + 256)` fails. Write
  `of_int 3 + of_int 256`.
- **U256 and U64 arithmetic wraps** (`of_z_truncating`), like the C++ uint256. Division by zero raises.
- **Float comparisons under Monomorphic:** use `Float.compare a b >= 0`.
- **Type-directed disambiguation** of record fields and constructors across modules works when the type is
  known; annotate, e.g. `((m, st) : state)`. Warnings 40–42 aren't errors here.
- **dune and main modules:** when a library has a module with the library's own name (`fuzz.ml`), other modules
  are only visible if that module re-exports them.
- **Formatting a subtree only:** `dune build @test/fuzz/fmt --auto-promote`. Don't reformat unrelated code.
- **`Bytes` is `String`** in `Byte_string`. Fixed-width types have `of_bytes_exn` and `init`.
- **`Crypto.Secp.gen_keypair`** raises on an invalid secret, i.e. zero or at least the curve order. With random
  secrets that's negligible.

## 8. Next steps (none started)

1. **Runner:** implement it in `Fuzz` (§6), if the user agrees to a `Fuzz.Run` functor.
2. **Driver executable:** `--seed`, `--depth` and `--runs`; seeds chained from run to run; printing done by the
   staking fuzzer; timing. Not under `dune test`, though a short fixed-seed run could be.
3. **Performance of `check`:** cache decoded storage within one `check`, or check once per transition.
4. **Spec gaps:** `distributePriorityFees` (MIP-11), and revision parameterisation. In the C++,
   `active_validator_stake` depends on the revision.
5. **Optional:** the public-key invariants, and a command printer for traces.

## 9. Side discussions (finished, for context)

- **The first request** was a report on the C++ fuzzer and the porting effort, followed by a trace or fixture
  export tool, which the user dropped ("Nevermind that").
- **Skipping jump-destination analysis in the C++ VM** when code starts with 0x00, 0xFE or 0xEF:
  - It isn't implemented. `Intercode` always calls `find_jumpdests` (`vm/interpreter/intercode.cpp`).
  - Skipping would be safe. `is_jumpdest` is only read by JUMP and JUMPI; its guard should then become
    `pc < jumpdest_map_.size()`.
  - The gain is probably small next to the copy and keccak on the same code path. The 0x00 prefix (SSTORE2
    data contracts) is the only case with much code to skip.
  - 0xEF is nearly moot: EIP-3541 rejects code deployed with that prefix, which leaves only 23-byte 7702
    delegation designators. The user dropped the topic.
- **Moving the session to another machine:** Remote Control (`/remote-control`) didn't fit the user's needs,
  hence this file.
