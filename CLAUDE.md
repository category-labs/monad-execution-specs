# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project purpose

Executable specification of the Monad Execution layer, written in OCaml. The library (`monad_lib`) implements an EVM interpreter, block/transaction execution, and Ethereum world-state management parameterized by a Monad-specific chain revision (`MONAD_ZERO` … `MONAD_NEXT`; only `MONAD_EIGHT` and `MONAD_NINE` are "active" and supported at any given time — see `lib/chain/monad.ml`).

## Build, test, run

- `dune build` — build everything.
- `dune test` — run all Alcotest suites under `test/`.
- `dune build @fmt --auto-promote` — check ocamlformat and apply changes (CI enforces this). Requires ocamlformat 0.28.1.
- `dune build @doc` — build odoc docs to `_build/default/_doc/_html/index.html`.
- `dune exec evmrun -- --bytecode HEX --calldata HEX [--gas N] [--trace] [--revision MONAD_EIGHT|MONAD_NINE]` — run raw bytecode via the interpreter.
- `dune exec execrun -- --blockchain_test FILE [--trace] [--update_fixture FILE]` — replay a blockchain-test JSON fixture.

Running a single test file (Alcotest via dune): `dune exec test/unit/numeric.exe` (each `(test (name X))` stanza produces `X.exe`). Alcotest supports `-e` to filter test names.

External test fixtures for `test/execution/blockchain_tests.ml` are downloaded by `./scripts/download_mf_tests.sh` into `test/execution/fixtures/blockchain_tests/mf_tests/`. CI runs this before `dune test`; run it locally before executing that suite.

Requires OCaml 5.4.0 with flambda. Git submodules under `third_party/` (`evmc`, `tests`) must be checked out (`git submodule update --init`).

## Architecture

### Layering (in `lib/`)

The core library is a single dune library `monad_lib` with `(include_subdirs qualified)`, so subdirectories become nested modules (e.g. `Chain.Ethereum`, `Chain.Monad`). Rough dependency layering, bottom-up:

1. **Primitives** — `numeric.ml` (Zarith-backed `U256`, `U64`, `Uint`), `byte_string.ml` (`Bytes`, `B20`, `B32`, `B256`), `comparable.ml`, `result.ml`/`option.ml` (stdlib extensions), `traits.ml`, `map.ml`, `crypto.ml` (Keccak, secp256k1), `rlp.ml`, `mpt.ml` (Merkle Patricia trie), `bloom.ml`, `gas.ml`.
2. **Monad plumbing** — `monad.ml` defines `SIG`/`SIG2` and a `Make` functor providing combinators (`>>=`, `let$`, `<$>`, `sequence`, …). Most execution logic is written against these combinators so the same code composes whether the underlying "monad" is pure state (`WorldState/BlockState/TransactionState` threading) or the trivial identity monad used by the C FFI host.
3. **Chain params** — `chain/monad.ml` (`Revision`, `PARAMS`, `Devnet`/`Testnet`/`Mainnet` chain IDs and timestamp→revision maps) and `chain/ethereum.ml` (`Address`, `Account`, `Block`, `Header`, `Transaction`, `Receipt`, `Withdrawal`).
4. **VM contract** — `evmc.ml` defines the OCaml equivalent of the [EVMC](https://evmc.ethereum.org/) interface: `HOST` module type, `Message`, `Result`, `TxContext`, `StorageStatus`. Everything above this line is host-agnostic.
5. **Host + state** — `host.ml` defines `WorldState` (accounts + block history), `BlockState` (per-block gas/receipts on top of a `WorldState`), `TransactionState` (per-tx transient/journal state on top of `BlockState`), and an `Instantiate` functor that plugs a chosen state layer into `Evmc.HOST`. Uses `lens.ppx_deriving` heavily — mutation is expressed via lenses (`world_state |-- WorldState.account addr`).
6. **VM + execution** — `vm.ml` (`Vm.Make (Params) (Host)`) implements the interpreter (memory, stack, opcode dispatch, gas metering). `execution.ml` (`Execution.Make (Params)`) implements transaction and block processing and wires the host to the VM. `precompiles.ml`, `delegation.ml` (EIP-7702), `reserve_balance.ml` (Monad-specific) live at this level.
7. **Fixtures** — `fixtures.ml` decodes the [execution-spec-tests](https://github.com/ethereum/execution-spec-tests) blockchain-test JSON format.

### Parameterization via functors

Almost everything that varies by chain revision is a functor argument:

```
module Params : sig
  val chain_id : Uint.t
  val revision : Chain.Monad.Revision.active   (* `Eight | `Nine *)
  val trace : bool
  val debug_tstore : bool   (* only for the VM; enables the fuzzer's tstore log *)
end
```

`Execution.Make (Params)` returns a module containing `Host`, `Vm`, `process_block`, `prepare_message`, etc. New chain hard-forks are added by extending `Revision.t` and gating behavior on `match Params.revision with ...`. Only two revisions are expected to be active at a time.

### C bindings (`bindings/`)

The VM can be exposed as an EVMC-compatible shared object, which is how external fuzzers/test harnesses drive it.

- `bindings/c_evmc/` — ctypes bindings to the C EVMC ABI in `third_party/evmc/include`.
- `bindings/vm/` — reverse bindings (`Cstubs_inverted`): builds `libmonadml_evm` as a shared object that exposes `evmc_create_monadml_evm` and `evmc_create_monadml_evm_debug_tstore`. `C_host` wraps a C-side host vtable into an `Evmc.HOST` implementation over the trivial state monad `type 'a st = unit -> 'a * unit`.

If you change the `Evmc.HOST` signature, both sides of the FFI (`c_evmc_template.ml` and `libmonadml_evm_template.ml`) need updating in lockstep.

### Tests

- `test/unit/` — pure unit tests for `numeric`, `rlp`, `mpt`.
- `test/interpreter/` — opcode-level VM tests (`opcodes`, `control`, `memory`, `storage`, `eip_145`, `eip_1153`). Use `test_utils/program.ml` to build bytecode programs.
- `test/execution/` — end-to-end fixture replay. `blockchain_tests.ml` walks the `mf_tests/` and `mp_tests/` folders; `procedural_tests.ml` builds fixtures programmatically. The `enabled_revisions_for_test` list at the top of `blockchain_tests.ml` is the source of truth for suppressions (missing precompiles, known-divergent tests).

## Conventions to preserve

- The core of the codebase is purely functional. Mutable fields, `ref`s and `array`s are forbidden for modules in `lib/`. CLI tools may use mutability.
- Error handling should generally be explicit via `result`. Exceptions, especially assertion failures, are allowed only to represent unrecoverable programming errors.
- Style is enforced by ocamlformat 0.28.1 with the config in `.ocamlformat` (margin 110, `break-infix=fit-or-vertical`, `profile=ocamlformat`). Do not reformat unrelated code.
- Prefer lens-based updates (`state.^$(lens) (fun x -> ...)`, `|--`) for nested state — this is the established idiom in `host.ml` and callers.
- New chain-revision behavior goes behind `match Params.revision with` inside the functor body, not as a separate module.
- YP references in comments (e.g. `(* YP (46) *)`) point to equations in the Ethereum Yellow Paper; keep them when editing the surrounding logic. Ditto for Monad references (e.g. `(* Monad §6 *)`).
- Tests are Alcotest + QCheck. Property tests use `qcheck-alcotest` — see `test/interpreter/opcodes.ml` for the pattern.
