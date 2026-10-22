# Rocq translation proofs

This directory contains handwritten proofs specific to the OCaml definitions
in this repository. Files are named after stable module and definition names,
not source line numbers, and must never be overwritten during translation.

Generic lemmas and translator-generated certificate interfaces belong to
`rocq-of-ocaml`; generated Gallina belongs in the translation build directory.

## Current status

- `Termination/Natural.v` and `Termination/IntegerLoops.v` provide the common
  unsigned and signed ranking arguments used by arithmetic, pairing,
  precompile, and VM loops.
- `Termination/FiniteSeq.v` proves termination of the seven monadic consumers
  of the project's finite `Seq.t` model.
- `Termination/Ec.v`, `Termination/StringFindSubstring.v`, and
  `Termination/VmLoops.v` prove definition-specific arithmetic, substring,
  memory-dump, and bytecode-scanning facts. The scanner certificate checks
  every opcode byte, proves that PUSH immediates advance the program counter,
  and connects the generated dependent match to that checked step function.
- `Termination/Mpt.v` proves a phase-sensitive RLP-size ranking for the two
  mutually recursive `Mpt.Node.of_rlp` decoders.
- `Termination/PrecompileList.v` supplies the unsigned rank for the precompile
  parser's bounded repetition loop.
- `Termination/Rlp.v` proves the phase-and-length ranking for all three
  decoder transitions and exhibits the exceptional substring fallback that
  can repeat a truncated list input. Explicit progress checks at the recursive
  calls now make this certificate unconditional. Bounds lemmas show that
  successful native slices already satisfy those checks.
- `Termination/TrieDepth.v` proves the remaining-key-length ranking for
  prefix-trie insertion and lookup, including optional starting depths.
  Explicit progress guards attach these certificates to both definitions.
- `Termination/PatriciaTrie.v` proves that lookup descends through a finite
  tree, including an extension with an empty path segment. Generic
  array-weight bounds justify branch-child selection. Native cyclic OCaml
  values are outside this finite inductive representation.
- `Termination/VmCreateHandlerProgress.v` proves that the generated CREATE
  delegation prelude cannot increase gas. Buffer and stack result updates
  preserve gas after a child merge. Under the explicit unsigned host-return
  bound and an entry gas bound below `2^64`, every successful path of the
  generated `generic_create_impl` is gas nonincreasing. The positive generated
  charges then make both outer CREATE and CREATE2 handlers strictly decrease
  gas on every successful continuation. These conditional results do not
  establish the host-return law for arbitrary EVMC hosts.
- `Termination/VmCallHandlerProgress.v` proves that CALL output-buffer and
  memory writes preserve gas, depth-rejection refunds the forwarded amount,
  and a bounded host return followed by output handling credits no more
  than the forwarded gas. The generated `generic_call_impl` therefore
  increases gas by at most the forwarded amount on successful paths, under
  the explicit conversion and host-return premises. For a forwarded amount
  below `2^64`, the generated U256 word satisfies those conversion premises.
  A successful generated quote charge followed by the call body therefore
  strictly decreases gas under the account-access and host-return premises.
  Delegation keeps the base account-access cost, while the remaining host
  reads and write-permission guard preserve gas. A shared branch theorem now
  covers both a skipped child and an invoked child after the quote charge.
  The complete outer CALL-family control flow remains open.
- `Unreachable/CryptoBlake2.v` proves that the list-backed array update does
  not consult its fallback value when the index is in bounds.
- `Refinement/UintRlp.v` characterizes unsigned-integer RLP decoding for every
  finite byte string: empty bytes encode zero, leading zeros are rejected,
  and a nonzero leading byte permits decoding. The result is independent of
  both exceptional fallback arguments. Bounds and byte-length proofs connect
  this characterization to the executable `UintN` model. The encoder emits
  exactly the significant bytes; encoding then decoding returns every `N`,
  and re-encoding a successfully decoded value restores the original RLP.
- `Refinement/UintArithmetic.v` relates division, both remainder conventions,
  modular arithmetic, exponentiation, byte-to-word rounding, and the
  one-sixty-fourth gas deduction to the source's integer formulas. Divisors
  must be nonzero and exponents nonnegative where native operations require
  those conditions. Shift lemmas establish multiplication/division by powers
  of two for nonnegative counts and use of the existing fallback for negative
  counts, which native Zarith rejects.
- `Refinement/VmHostLift.v` proves pointwise return and bind preservation
  for the generated VM's host-state lift, together with bind congruence.
  The equations include final machine state and need no functional
  extensionality. Their generated dependencies retain the existing
  comparison, physical-equality, hashing, and formatting parameters.
- `Refinement/VmNativeRunBridge.v` proves a finite-step simulation contract:
  if native gas is the integer representation of model gas and each native
  dispatch result matches the model, model progress makes the native gas
  guard unreachable and the finite run results agree. The concrete
  native-to-model dispatch relation, including host and exception behavior,
  is still open. This contract does not certify the OCaml implementation.
- `Refinement/VmPartialObservation.v` specializes the resumption lifting and
  state-observation laws to those actual VM operations, with an explicit
  convergence premise. `Refinement/Assumptions.v` prints the dependency
  assumptions of the principal refinement theorems during the full build.

The current translation profile has zero admitted obligations and zero measure
parameters. Its two algebra loops use checked degree guards, and the VM run
loop uses a checked gas guard. Avoidance of the algebra exceptional branches
for intended fields and native/model VM correspondence remain open. The bare
host signature still permits a gas-creating state cycle; see the bounded
native witness in `../ocaml/vm_host_cycle.ml`.

Most proof files depend only on stable translator libraries.
`Termination/Mpt.v` necessarily imports generated `Rlp`, because its ranking is
defined over the translated recursive RLP datatype. `Termination/PrecompileList.v`
imports the `UintN` support module so its certificate has exactly the type
expected by the translated API. `Refinement/UintRlp.v` also imports `UintN` and
generated `Rlp`; `Refinement/UintArithmetic.v` imports `UintN`, and
`Refinement/VmHostLift.v` imports generated `Vm`. These files
are therefore checked as part of the complete
generated build rather than the source-only proof build.

The full build is the default in `rocq/scripts/check-handoff.sh`. Run
`rocq/scripts/check-generated-rocq.sh` to repeat it against an existing
generation. Run `rocq/scripts/check-partial-laws.sh` for an isolated
predicative compilation of the translator's standalone partial runtime and
an exact check that its 16 principal laws have no global assumptions.

## Upstream updates

After changing the OCaml source:

1. Regenerate the Gallina translation.
2. Run `rocq/scripts/check-proof-inventory.sh`.
3. Compile these proofs with `rocq/scripts/check-translation-proofs.sh`.
4. Update a proof only after reviewing the corresponding source definition's
   recursive edges or exceptional paths.

The checked-in manifests deliberately make additions, removals, and recursion
strategy changes visible during an upstream update.
