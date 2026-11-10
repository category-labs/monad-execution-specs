#!/usr/bin/env bash
set -euo pipefail

checks=$1
header=$2
shift 2
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
mkdir "$work/evmc"

compile() {
    "$@" -std=c11 -I "$work" -c "$checks" -o "$work/checks.o" >"$work/compile.log" 2>&1
}

cp "$header" "$work/evmc/evmc.h"
chmod u+w "$work/evmc/evmc.h"
compile "$@"
reject() {
    description=$1
    shift
    if compile "$@"; then
        echo "ABI checks accepted $description" >&2
        exit 1
    fi
    if ! grep -q 'static assertion failed' "$work/compile.log"; then
        cat "$work/compile.log" >&2
        exit 1
    fi
}

sed 's/uint32_t memory_capacity;/uint64_t memory_capacity;/' "$header" >"$work/evmc/evmc.h"
reject 'a widened message field' "$@"

sed 's/uint32_t memory_capacity;/uint32_t memory_capacity; uint64_t extra_field;/' "$header" >"$work/evmc/evmc.h"
reject 'an added message field' "$@"

sed 's/uint8_t bytes\[32\];/uint8_t bytes[33];/' "$header" >"$work/evmc/evmc.h"
reject 'a resized byte array' "$@"

sed -e 's/int64_t gas_left;/int64_t swap_field;/' \
    -e 's/int64_t gas_refund;/int64_t gas_left;/' \
    -e 's/int64_t swap_field;/int64_t gas_refund;/' "$header" >"$work/evmc/evmc.h"
reject 'reordered result fields' "$@"
