#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
project=$(cd "${1:?Pass the pinned upstream lean directory}" && pwd)
temp=$(mktemp -d)
trap 'rm -rf "$temp"' EXIT
export PYTHONDONTWRITEBYTECODE=1
python3 "$here/check-project.py" "$project"
python3 "$here/check-input.py"
python3 "$here/search/verify.py" "$here/statement.json" | diff -u "$here/search/results.txt" -
python3 "$here/adaptive/check.py" "$here/adaptive/cert-51.txt" --claim 51 --assignment "$here/statement.json"
c++ -O3 -std=c++20 "$here/formula/star_bound.cpp" -o "$temp/upper"
"$temp/upper" | diff -u "$here/formula/independent-counts.txt" -
c++ -O3 -std=c++20 "$here/formula/star_forest.cpp" -o "$temp/forest"
"$temp/forest" "$here/formula/edges.txt" | diff -u "$here/formula/result.txt" -
c++ -O3 -std=c++20 "$here/adaptive/find.cpp" -o "$temp/search"
"$temp/search" "$here/formula/edges.txt" 51 1000000 "$temp/cert.txt"
cmp "$temp/cert.txt" "$here/adaptive/cert-51.txt"
cd "$project"
lake build +PEqualNP.MetaComplexity.Helpers.PermInputs +PEqualNP.MetaComplexity.Helpers.CoverCircuitList +PEqualNP.MetaComplexity.Helpers.ForestBound
lake env bash -eu -c '
  here=$1
  temp=$2
  export LEAN_PATH="$temp:$LEAN_PATH"
  lean "$here/upper/Literal124.lean"
  lean -R "$here/lower" -o "$temp/Lower.olean" "$here/lower/Lower.lean"
  lean "$here/formula/StarForestArithmetic.lean"
  lean "$here/lower/Terminal51.lean"
  lean -R "$here/adaptive" -o "$temp/Adaptive.olean" "$here/adaptive/Adaptive.lean"
  lean -R "$here/adaptive" -o "$temp/Graph.olean" "$here/adaptive/Graph.lean"
  lean "$here/adaptive/Cert46.lean"
  lean -R "$here/adaptive" -o "$temp/Fast.olean" "$here/adaptive/Fast.lean"
  python3 "$here/adaptive/make.py" 46 "$here/adaptive/cert-46.txt" "$here/statement.json" "$temp/Expanded46.lean" --fast
  lean "$temp/Expanded46.lean"
  if [[ ${EXPAND_51:-0} == 1 ]]; then
    python3 "$here/adaptive/make.py" 51 "$here/adaptive/cert-51.txt" "$here/statement.json" "$temp/Expanded51.lean" --fast
    lean "$temp/Expanded51.lean"
  fi
' -- "$here" "$temp"
