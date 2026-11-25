#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 2 ]]; then
  echo "usage: bash replay-fresh-output.sh /path/to/pequalnp-proofs/lean /path/to/FreshOutput.lean" >&2
  exit 2
fi
project=$(realpath "$1")
fresh=$(realpath "$2")
here=$(cd "$(dirname "$0")" && pwd)
lib=$(mktemp -d)
trap 'rm -rf "$lib"' EXIT
cd "$project"
lake build PEqualNP.Outside.L_meta_4795 PEqualNP.Outside.L_meta_8642
lake env bash -euo pipefail -c '
  lib=$1
  fresh=$2
  here=$3
  export LEAN_PATH="$lib:${LEAN_PATH:-}"
  lean -j1 --root="$(dirname "$fresh")" -o "$lib/FreshOutput.olean" "$fresh"
  lean -j1 --root="$here" -o "$lib/FreshOutputAt.olean" "$here/FreshOutputAt.lean"
  lean -j1 --root="$here" "$here/Row16752Example.lean"
' bash "$lib" "$fresh" "$here"
