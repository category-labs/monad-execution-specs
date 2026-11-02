# Account-configurable reserve balance (experimental QEDK)

This is the pre-MCP design. Select `MONAD_ELEVEN` explicitly to enable it;
network activation timestamps are unchanged. Eleven inherits Nine's other
implemented rules, not every feature of the C++ `MONAD_NEXT` revision.
Eight and Nine keep the fixed reserve and do not enable configuration storage
or its selectors. Their execution reserve check now explicitly rejects a
non-emptying sender's gas-fee bound above its protected amount, rather than
accepting that account through a zero threshold.

## Configuration

The default reserve is 10 MON. An account may request any U256 reserve, including
zero. A request in block `b` takes effect at `b + 3`, for both increases and
decreases. Until then the previous reserve remains active. In the request block,
the last successful setting wins. A different block cannot replace a setting
that has not yet taken effect. Activation-height overflow is rejected.

The native account `0x1001` stores each account's settled reserve, pending reserve
and activation height in three ordinary storage slots. An unused record has
activation height zero and means the default reserve. Reads select the active
value using the block height; no activation transaction or storage sweep is
required. A matured getter response has identical settled/pending values and
activation height zero, without clearing the stored record.

Storage updates use the existing call/transaction journal. Reverting an inner
call or the final transaction reserve check also rolls back its settings.
At block entry, Eleven sets the native account's nonce to at least one without
overwriting its balance, code or storage. Historical revisions do not do this.

## Precompile interface

All amounts and heights use 32-byte ABI words. Existing `dippedIntoReserve()`
introspection remains unchanged. The additional methods are enabled only in Eleven:

| Method | Selector | Gas | Result |
| --- | --- | ---: | --- |
| `getK()` | `0xee39e7a0` | 100 | `3` |
| `getReserveBalance(address)` | `0x15226b54` | 25,000 | Settled reserve, pending reserve, activation height |
| `setReserveBalance(uint256)` | `0x0cbbb4f6` | 150,000 | Activation height |

These selectors require a non-static, non-delegated `CALL`, zero value and exact
argument length. Address arguments must have twelve zero high bytes. The setter
changes the immediate caller's configuration, not the transaction sender's or
the address holding delegated code. A delegated account may execute an ordinary
`CALL` to this precompile and configure its own reserve while another account
pays for the transaction. Direct `DELEGATECALL` to the precompile is rejected.

## Execution reserve check

For each checked account, Eleven uses the configuration stored in the
transaction-entry world and active at the candidate block's height. It protects
the smaller of that reserve and the account's initial balance. This is not a
consensus budget refresh and does not change transaction admission.

In every executable revision, a non-emptying sender's maximum gas fees above
that protected amount cause the reserve check to fail. Otherwise the protected
amount is reduced by those fees. Other accounts receive no fee deduction. The existing emptying and
same-transaction selfdestruction exceptions remain unchanged. This intentionally
removes Eight/Nine's historical fee-above-reserve approximation; compatibility
with consensus-accepted historical blocks requires consensus to exclude that
case. The QEDK theorem still concerns revision Eleven, not historical consensus.

Upstream's recovered-authority emptying-counter fix is retained, including for
authorizations that fail validation. This PR changes no authorization processing.

## Tests and proof scope

`test/unit/reserve_config.ml` covers delayed activation, zero reserve, repeated
and pending settings, ABI failures, revision gating, sponsored/delegated callers,
real VM-call rollback and the final reserve check. `reserve_config_signed.ml`
checks real sender/authorization recovery and native execution of the signed
reserve-increase fixture used by the Rocq development. It also checks that Eleven
retains upstream's counter update for a recovered but nonce-invalid authorization.

Run `dune runtest test/unit test/interpreter test/execution` after initializing
the repository's pinned submodules. The `highGasUsage` Eight fixture now expects
reserve-check reverts in blocks 2-11: their gas-fee bounds are 10.2-25.5 MON,
above the fixed 10 MON reserve, and the sender is not eligible for emptying.
Its transactions, genesis state and gas usage are unchanged. Ten 10-wei value
transfers revert, so the sender retains 100 wei more and the recipient receives
100 wei less; the expected receipts, state roots and dependent block hashes are
regenerated accordingly. The rejected-authorization fixtures are unchanged.

The [Rocq source browser](https://category-labs.github.io/category-research/formalverif/userrb/)
contains proofs about a pinned translation of the configurable-reserve model.
This OCaml-only PR excludes translation artifacts, termination proof scripts
and unrelated proof-oriented VM/Host changes. Its base includes newer upstream
authorization-counter behavior that the published proof snapshot predates;
that proof is not a certification of this PR's entire executor.
