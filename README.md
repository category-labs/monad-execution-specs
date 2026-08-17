# Monad Execution Executable Specification

## Overview

This repository contains the specification of the Monad Execution layer implemented as OCaml code.

## Building the source

### Requirements

To build, you will need a recent (>= 3.20) version of [dune](https://dune.build/). The easiest way to get it is to install [opam](https://opam.ocaml.org/) and then run `opam install dune` from a terminal.

### Building and running

To build the project, first fetch third-party dependencies with
```shell
git submodule update --init --recursive
```
Then the project can be built with
```shell
dune build
```
The first time building the project may take a long time as `dune` fetches and builds an OCaml toolchain.
After the build has finished, unit tests can be executed with
```shell
dune test
```
Additional test fixtures can be downloaded with `scripts/download_mf_tests.sh`.

#### Executing bytecode with `evmrun`

The `evmrun` tool can run EVM bytecode on an empty blockchain.
```shell
dune exec evmrun -- <params>
```

Usage is as below.
```shell
Usage: evmrun <options> (--bytecode_file FILE | --bytecode HEX) (--calldata_file FILE | --calldata HEX)
  --revision Revision to use (default: MONAD_EIGHT)
  --chain_id Chain ID to use (default: 10143)
  --bytecode_file Bytecode file
  --calldata_file Calldata file
  --bytecode Bytecode
  --calldata Calldata
  --gc_stats Report GC statistics after execution
  --gas Gas limit (default: 100000)
  --trace Enable tracing
```

#### Executing blockchain fixtures with `execrun`

The `execrun` tool can be used to execute [EELS blockchain test fixtures](https://steel.ethereum.foundation/docs/execution-specs/running_tests/test_formats/blockchain_test/).
```shell
dune exec execrun -- <params>
```

Usage is as below.
```shell
Usage: execrun --blockchain_test FILE [--update_fixture FILE] [--trace]
  --blockchain_test Blockchain test fixture file
  --trace Trace VM execution
  --update_fixture Generate new fixtures from execution, do not verify provided roots
```

## Building the documentation

To build the documentation, you'll need to install `odoc` (with `opam install odoc`) and then run:
```shell
dune build @doc
```
The documentation can then be found under `_build/default/_doc/_html/index.html`
