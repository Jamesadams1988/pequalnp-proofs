#!/bin/sh
# Run from the pinned upstream Lean project (the directory with lakefile.toml).
set -eu
src=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
lake env sh -eu -c '
    src=$1
    build=$2
    export LEAN_PATH="$build${LEAN_PATH:+:$LEAN_PATH}"
    lean --root="$src" -o "$build/QueryTree.olean" "$src/QueryTree.lean"
    lean --root="$src" -o "$build/OrdinaryTree.olean" "$src/OrdinaryTree.lean"
' sh "$src" "$build"
