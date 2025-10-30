# Monad Execution Executable Specification

## Overview

This repository contains the specification of the Monad Execution layer, as an OCaml program.

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
