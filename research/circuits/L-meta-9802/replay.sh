#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
project=$(realpath "${1:?pass the lean directory of the pinned upstream checkout}")
cd "$project"
lake build PEqualNP.Defs PEqualNP.MetaComplexity.Helpers.CoverCircuitList PEqualNP.MetaComplexity.Helpers.Support PEqualNP.Outside.L_meta_4795
lake env python3 -B "$here/replay.py" "${@:2}"
