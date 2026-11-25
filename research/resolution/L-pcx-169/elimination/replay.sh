#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
project=$(cd "${1:?pass the upstream lean project directory}" && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
python3 -B "$here/hole_blocks.py"
python3 -B "$here/eliminate.py" --rounds 2 --seed 420 --output "$tmp/dp.json"
cd "$project"
lake build PEqualNP.Defs
lake env bash -c '
  export LEAN_PATH="$1:$LEAN_PATH"
  lean -j1 --root="$2" -o "$1/HallLocal.olean" "$2/HallLocal.lean"
  lean -j1 --root="$2" "$2/HallBlocks.lean"
  lean -j1 --root="$2" "$2/ColumnRoot.lean"
' _ "$tmp" "$here"
