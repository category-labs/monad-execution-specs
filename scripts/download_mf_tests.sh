#!/bin/bash

set -euo pipefail

URL="https://github.com/monad-developers/execution-spec-tests/releases/download/monad%40v1.0.0/fixtures_monad.tar.gz"
SHA="94b68a8cb1eb66f03a60156ac1cc73191fc084257cf8673fb259992e44c7ed0d"
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
