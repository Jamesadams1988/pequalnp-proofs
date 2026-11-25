#!/usr/bin/env bash
set -euo pipefail
project=$(realpath "${1:?pass the upstream lean directory}")
here=$(cd "$(dirname "$0")" && pwd)
circuits=$(dirname "$here")
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT

python3 "$here/thresholds/generate.py" > "$build/ThresholdBatch.lean"
python3 "$here/family/generate_exact.py" > "$build/FamilyExact.lean"
cmp "$build/ThresholdBatch.lean" "$here/thresholds/ThresholdBatch.lean"
cmp "$build/FamilyExact.lean" "$here/family/FamilyExact.lean"
cd "$project"
lake build PEqualNP.Outside.L_meta_4795 PEqualNP.Outside.L_meta_8657 PEqualNP.Outside.L_meta_8642 PEqualNP.Outside.L_meta_12184
lake env bash -euo pipefail -c '
  build=$1
  here=$2
  circuits=$3
  export LEAN_PATH="$build:${LEAN_PATH:-}"
  compile() {
    local file=$1
    lean -j1 --root="$(dirname "$file")" -o "$build/$(basename "$file" .lean).olean" "$file"
  }
  compile "$circuits/L-meta-13646/CofactorBound.lean"
  compile "$circuits/L-meta-15094/FreshOutput.lean"
  compile "$here/Threshold.lean"
  compile "$here/PositiveTwin.lean"
  compile "$here/ThresholdWeights.lean"
  compile "$here/FreshOutputAt.lean"
  compile "$here/Row16752Example.lean"
  compile "$build/ThresholdBatch.lean"
  compile "$build/FamilyExact.lean"
' bash "$build" "$here" "$circuits"
