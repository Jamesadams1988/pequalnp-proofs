#!/usr/bin/env bash
set -euo pipefail
source_dir=$(cd "$(dirname "$0")" && pwd)
project_dir=$(realpath "${1:?Pass the lean directory of the pinned upstream checkout}")
cd "$project_dir"
lake build PEqualNP.MetaComplexity.Helpers.CoverCircuitList
lake env lean "$source_dir/Literal124.lean"
