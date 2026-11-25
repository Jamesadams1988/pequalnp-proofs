#!/usr/bin/env bash
set -euo pipefail
project=$(realpath "${1:?pass the upstream lean directory}")
here=$(cd "$(dirname "$0")" && pwd)
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
export PYTHONDONTWRITEBYTECODE=1

python3 "$here/tools/encode_cp.py" > "$build/Control.lean"
cmp "$build/Control.lean" "$here/Control.lean"
python3 "$here/tools/make_catalog.py" > "$build/ColumnCatalog.lean"
cmp "$build/ColumnCatalog.lean" "$here/ColumnCatalog.lean"
python3 "$here/tools/make_residual.py" > "$build/Residual.lean"
cmp "$build/Residual.lean" "$here/Residual.lean"
python3 "$here/tools/php_family.py"
python3 "$here/tools/row_support.py"
python3 "$here/interval/verify_interval.py"
python3 "$here/interval/interval_proof.py"

cd "$project"
lake build PEqualNP.Defs PEqualNP.Outside.L_meta_9672
lake env bash -euo pipefail -c '
  build=$1
  here=$2
  export LEAN_PATH="$build:${LEAN_PATH:-}"
  for module in Control RankOne GlobalRank CPRank FirstClosurePoint RealClosurePoint RankTwo TripleSupport TriangleGeometry ColumnCatalog Column EssentialEdges TargetTrace CapacityBudget DivCount SourceCoverage TraceTree Capacity14 Interval65 Residual; do
    echo "Checking $module"
    lean -j1 --root="$here" -o "$build/$module.olean" "$here/$module.lean"
  done
' bash "$build" "$here"
