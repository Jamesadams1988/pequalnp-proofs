#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
project=$(cd "${1:?pass the upstream lean project directory}" && pwd)
python3 -B "$here/check_filters.py"
cd "$project"
lake build PEqualNP.Defs
lake env lean -j1 --root="$here" "$here/FilterObstruction.lean"
