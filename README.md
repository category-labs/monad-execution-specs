# Monad Execution Executable Specification

## Overview

This repository contains the specification of the Monad Execution layer, as an OCaml program.

## Contract ABI

The [typed codec API](lib/contract/type.mli) describes ABI values without GADTs.
For example, `Type.tup2 (Type.Address.t, Type.U256.t)` describes two parameters
whose OCaml value is the ordinary pair `(recipient, amount)`. `Type.tuple`
embeds those fields as one ABI value; `Type.mapped` adapts a codec to a domain
type. Codec records are hidden so callers construct them through the typed
combinators rather than supply layout and encoding operations independently.

`Function.pack` closes over a function's typed codecs and handler to produce
the uniform message handler stored in a contract's dispatch table. This avoids
existential function packages without removing input/output type checking.

The [ABI tests](test/unit/solidity.ml) compare the codecs against the frozen
pre-refactor implementation, including malformed input behavior and packed
storage layouts. The old GADTs remain only in that test oracle, not in the
execution model. This source refactor does not itself establish a verified
Rocq translation or complete the staking proofs.

## Building the source

### Requirements

To build, you will need a recent (>= 3.20) version of [dune](https://dune.build/). The easiest way to get it is to install [opam](https://opam.ocaml.org/) and then run `opam install dune` from a terminal.

### Building and running

To build the project, from the root directory of this repository, run:

```shell
dune build
```

Currently, a standalone executable is provided to run EVM bytecode. To execute it, run:

```shell
dune exec evmrun -- <params>
```

Usage is as below.
```shell
Usage: evmrun [--gas N] [--trace] (--bytecode_file FILE | --bytecode HEX) (--calldata_file FILE | --bytecode HEX)
  --bytecode_file Bytecode file
  --calldata_file Calldata file
  --bytecode Bytecode
  --calldata Calldata
  --gas Gas limit (default: 100000)
  --trace Enable tracing
  -help  Display this list of options
  --help  Display this list of options
```

The unit tests can be executed with:
```shell
dune test
```

To build the documentation, you'll need to install `odoc` (with `opam install odoc`) and then run:
```shell
dune build @doc
```

The documentation is then located under `_build/default/_doc/_html/index.html`
