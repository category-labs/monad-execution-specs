#!/bin/sh
set -eu

repo_root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
rocq_root="$repo_root/rocq"
. "$rocq_root/toolchain.env"

switch=${ROCQ_OPAM_SWITCH:-"$repo_root/.opam-rocq-of-ocaml"}
translator_root=${ROCQ_OF_OCAML_ROOT:-"$repo_root/.rocq-tools/rocq-of-ocaml"}

for command in git opam python3 jq rg; do
  if ! command -v "$command" >/dev/null 2>&1; then
    printf 'Missing required command: %s\n' "$command" >&2
    exit 1
  fi
done

if ! opam var root >/dev/null 2>&1; then
  opam init --bare --yes
fi

git -C "$repo_root" submodule update --init

if [ ! -d "$switch" ]; then
  opam switch create --no-switch "$switch" "ocaml-variants.$OCAML_VERSION+options" \
    ocaml-option-flambda --yes
fi

if [ ! -e "$translator_root/.git" ]; then
  mkdir -p "$(dirname "$translator_root")"
  git clone "$ROCQ_OF_OCAML_REPOSITORY" "$translator_root"
elif [ -n "$(git -C "$translator_root" status --porcelain)" ]; then
  printf 'Translator checkout is dirty: %s\n' "$translator_root" >&2
  exit 1
fi

if ! git -C "$translator_root" cat-file -e "$ROCQ_OF_OCAML_COMMIT^{commit}" 2>/dev/null; then
  git -C "$translator_root" fetch "$ROCQ_OF_OCAML_REPOSITORY" \
    "$ROCQ_OF_OCAML_COMMIT"
fi
translator_revision=$(git -C "$translator_root" rev-parse HEAD)
if [ "$translator_revision" != "$ROCQ_OF_OCAML_COMMIT" ]; then
  if [ -L "$translator_root" ]; then
    printf 'Shared translator checkout has revision %s, expected %s.\n' \
      "$translator_revision" "$ROCQ_OF_OCAML_COMMIT" >&2
    printf 'Point this experiment at a matching translator worktree.\n' >&2
    exit 1
  fi
  git -C "$translator_root" checkout --detach "$ROCQ_OF_OCAML_COMMIT"
fi

opam install --switch="$switch" --yes --deps-only \
  "$rocq_root/monad-execution-specs-rocq.opam"

if [ "${ROCQ_WITH_ITREE:-0}" = 1 ]; then
  opam install --switch="$switch" --yes \
    "coq-ext-lib.$COQ_EXT_LIB_VERSION" \
    "coq-paco.$COQ_PACO_VERSION" \
    "coq-itree.$COQ_ITREE_VERSION"
fi

opam exec --switch="$switch" -- \
  dune build --root="$translator_root" src/rocqOfOCaml.exe
opam exec --switch="$switch" -- \
  dune build --pkg=disabled --root="$repo_root" @install

printf '\nToolchain ready.\n'
printf '  switch:     %s\n' "$switch"
printf '  translator: %s\n' "$translator_root"
printf '  revision:   %s\n' "$ROCQ_OF_OCAML_COMMIT"
