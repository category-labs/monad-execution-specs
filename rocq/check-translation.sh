#!/bin/sh
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
. "$root/rocq/toolchain.env"
switch=${ROCQ_OPAM_SWITCH:-"$root/.opam-rocq-of-ocaml"}
translator=${ROCQ_OF_OCAML_ROOT:-"$root/.rocq-tools/rocq-of-ocaml"}

if [ ! -f "$root/rocq/generated/next/Execution.v" ]; then
  printf 'Run rocq/scripts/generate-rocq.sh first.\n' >&2
  exit 1
fi
if [ "$(git -C "$translator" rev-parse HEAD)" != "$ROCQ_OF_OCAML_COMMIT" ]; then
  printf 'Translator checkout does not match rocq/toolchain.env.\n' >&2
  exit 1
fi

mkdir -p "$root/.rocq-tools"
build=$(mktemp -d "$root/.rocq-tools/translation-check.XXXXXX")
trap 'printf "Build and audit logs retained in %s\n" "$build"' EXIT
runtime="$build/runtime"
mkdir -p "$runtime"
git -C "$translator" archive --format=tar \
  --output="$build/runtime.tar" "$ROCQ_OF_OCAML_COMMIT" proofs
tar -xf "$build/runtime.tar" -C "$runtime"
git -C "$root" apply --unsafe-paths --directory="$runtime" \
  "$root/rocq/patches/predicative-runtime.patch"

copy_sources() {
  source_directory=$1
  target_directory=$2
  mkdir -p "$target_directory"
  find "$source_directory" -type f -name '*.v' |
  while IFS= read -r source; do
    relative=${source#"$source_directory"/}
    target="$target_directory/$relative"
    mkdir -p "$(dirname "$target")"
    cp "$source" "$target"
  done
}
copy_sources "$root/rocq/generated/next" "$build/generated"
copy_sources "$root/rocq/support" "$build/support"
copy_sources "$root/proofs/rocq" "$build/project-proofs"
copy_sources "$root/rocq/tests" "$build/tests"
cp "$root/rocq/generated.sha256" "$build/generated/generated.sha256"
if command -v sha256sum >/dev/null 2>&1; then
  (cd "$build/generated" && sha256sum -c generated.sha256)
else
  (cd "$build/generated" && shasum -a 256 -c generated.sha256)
fi
python3 "$root/rocq/scripts/check-block-equality-fields.py"

(cd "$runtime/proofs" &&
  opam exec --switch="$switch" -- rocq makefile -f _CoqProject -o Makefile &&
  opam exec --switch="$switch" -- make -j"${JOBS:-4}")

cd "$build"
{
  printf '%s\n' '-Q generated MonadVM' '-Q support MonadVM.Support'
  printf '%s\n' '-Q project-proofs MonadExecutionSpecs' '-Q tests PredicativeTests'
  printf '%s\n' "-Q $runtime/proofs RocqOfOCaml"
  find generated support project-proofs tests -type f -name '*.v' | LC_ALL=C sort
} > _CoqProject
opam exec --switch="$switch" -- rocq makefile -f _CoqProject -o Makefile
opam exec --switch="$switch" -- make -j"${JOBS:-4}"
opam exec --switch="$switch" -- ruby "$root/rocq/scripts/check-uint-parser.rb" "$build"
opam exec --switch="$switch" -- rocq c \
  -Q generated MonadVM -Q support MonadVM.Support \
  -Q project-proofs MonadExecutionSpecs -Q "$runtime/proofs" RocqOfOCaml \
  project-proofs/Refinement/Assumptions.v > assumptions.log
python3 "$root/rocq/scripts/check-assumption-report.py" assumptions.log
python3 "$root/rocq/scripts/check-bigarray-assumption-census.py" \
  "$build" "$runtime/proofs" - "$switch" --bundle
opam exec --switch="$switch" -- rocqchk -silent -o \
  -Q generated MonadVM -Q support MonadVM.Support \
  -Q project-proofs MonadExecutionSpecs -Q tests PredicativeTests \
  -Q "$runtime/proofs" RocqOfOCaml \
  MonadVM.Execution PredicativeTests.Runtime > kernel-check.log 2>&1
cat kernel-check.log
rg -Fq '* Theory: Set is predicative' kernel-check.log
rg -Fq '* Constants/Inductives relying on type-in-type: <none>' kernel-check.log
rg -Fq '* Constants/Inductives relying on unsafe (co)fixpoints: <none>' kernel-check.log
rg -Fq '* Inductives whose positivity is assumed: <none>' kernel-check.log
printf '\nGenerated translation, sidecar proofs, audits, and kernel check passed.\n'
