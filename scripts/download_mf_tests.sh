#!/bin/bash

set -euo pipefail

URL="https://github.com/monad-developers/execution-specs/releases/download/tests-monad@v1.2.2/fixtures_monad.tar.gz"
SHA="c96c822d2e187e9168aa20f2c158c8a2de96ea076f6e6c473a1b6d3fc5c064df"
CACHE="${XDG_CACHE_HOME:-$HOME/.cache}/monad-execution-specs"
mkdir -p "$CACHE"
TARBALL="$CACHE/fixtures_monad-$SHA.tar.gz"

if [ ! -f "$TARBALL" ]; then
    curl -L --fail -o "$TARBALL" "$URL"
fi
echo "$SHA  $TARBALL" | sha256sum -c -

TARGET="test/execution/fixtures/blockchain_tests/mf_tests"
mkdir -p "$TARGET"
tar -xzf "$TARBALL" -C "$TARGET" --strip-components=2
