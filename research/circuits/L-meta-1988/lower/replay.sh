#!/usr/bin/env bash
set -euo pipefail
if [ "$#" -ne 1 ]; then echo "Usage: $0 /path/to/built/pequalnp-proofs/lean" >&2; exit 2; fi
here=$(cd "$(dirname "$0")" && pwd)
project=$(cd "$1" && pwd)
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
cd "$project"
for mod in Elimination Lower Degrees; do
  lake env bash -eu -c 'export LEAN_PATH="$1${4:+:$4}:$LEAN_PATH"; lean -j1 --root="$2" -o "$1/$3.olean" "$2/$3.lean"' -- "$build" "$here" "$mod" "${LEAN_PATH:-}"
done
