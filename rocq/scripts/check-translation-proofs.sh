#!/bin/sh
set -eu

repo_root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
rocq_root="$repo_root/rocq"
switch=${ROCQ_OPAM_SWITCH:-"$repo_root/.opam-rocq-of-ocaml"}
translator_root=${ROCQ_OF_OCAML_ROOT:-"$repo_root/.rocq-tools/rocq-of-ocaml"}
translator_proofs="$translator_root/proofs"
project_proofs="$repo_root/proofs/rocq"
build=$(mktemp -d "${TMPDIR:-/tmp}/monad-vm-proof-check.XXXXXX")

cleanup() {
  rm -rf "$build"
}
trap cleanup EXIT HUP INT TERM

opam exec --switch="$switch" -- \
  make -C "$translator_proofs" -j"${JOBS:-4}"

mkdir -p "$build/project-proofs" "$build/support"
find "$project_proofs" -type f -name '*.v' |
while IFS= read -r source; do
  relative=${source#"$project_proofs"/}
  target="$build/project-proofs/$relative"
  mkdir -p "$(dirname "$target")"
  cp "$source" "$target"
done
cp "$rocq_root/support/CryptoBlake2.v" "$build/support/CryptoBlake2.v"

{
  printf '%s\n' '-Q project-proofs MonadExecutionSpecs'
  printf '%s\n' '-Q support MonadVM.Support'
  printf '%s\n' "-Q $translator_proofs RocqOfOCaml"
  printf '%s\n' 'support/CryptoBlake2.v'
  printf '%s\n' 'project-proofs/Termination/StringFindSubstring.v'
  printf '%s\n' 'project-proofs/Termination/Rlp.v'
  printf '%s\n' 'project-proofs/Termination/TrieDepth.v'
  printf '%s\n' 'project-proofs/Termination/PatriciaTrie.v'
  printf '%s\n' 'project-proofs/Termination/Natural.v'
  printf '%s\n' 'project-proofs/Termination/IntegerLoops.v'
  printf '%s\n' 'project-proofs/Termination/FiniteSeq.v'
  printf '%s\n' 'project-proofs/Termination/VmLoops.v'
  printf '%s\n' 'project-proofs/Termination/Ec.v'
  printf '%s\n' 'project-proofs/Unreachable/CryptoBlake2.v'
} >"$build/_CoqProject"

cd "$build"
opam exec --switch="$switch" -- rocq makefile -f _CoqProject -o Makefile
opam exec --switch="$switch" -- make -j"${JOBS:-4}"
