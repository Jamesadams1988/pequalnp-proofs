#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
lean_dir=$(cd "${1:?Pass the configured project lean directory}" && pwd)
root=$(git -C "$lean_dir" rev-parse --show-toplevel)
temp=$(mktemp -d)
trap 'rm -rf "$temp"' EXIT
export PYTHONDONTWRITEBYTECODE=1

python3 "$here/control/enumerate.py" | diff -u "$here/control/census.txt" -
python3 "$here/packed/packed.py" | diff -u "$here/packed/results.txt" -
(cd "$here/localized" && python3 localized.py) | diff -u "$here/localized/results.txt" -
python3 "$here/clauses/clauses.py" | diff -u "$here/clauses/results.txt" -
python3 "$here/algebra/replay.py"

# Use the original upstream file that provides the read-one star construction.
pin=1972ec9f567e2b3c90b0adc5472172f7e5ddfab0
module=PEqualNP/Outside/L_meta_2393
bridge=PEqualNP/MetaComplexity/Helpers/ReadTwoBridge
mkdir -p "$temp/PEqualNP/Outside" "$temp/PEqualNP/MetaComplexity/Helpers"
git -C "$root" show "$pin:lean/$bridge.lean" > "$temp/$bridge.lean"
echo "551c6d74b63710a6f0a7aff7db5683eed31c2bfc537c1344dec99b57f92c03b8  $temp/$bridge.lean" | sha256sum -c
git -C "$root" show "$pin:lean/$module.lean" > "$temp/$module.lean"
echo "bc7ab55f02ddb5f2ff17d552a48d6f3cb0711605c53b63877c79725a68172b35  $temp/$module.lean" | sha256sum -c

# Lean resolves a top-level package from one search root. Overlay the existing
# project modules beside the one pinned Outside module in the temporary tree.
for dir in PEqualNP PEqualNP/MetaComplexity PEqualNP/MetaComplexity/Helpers; do
  for entry in "$lean_dir"/.lake/build/lib/lean/"$dir"/*; do
    [[ -e "$entry" ]] || continue
    name=$(basename "$entry")
    if [[ "$name" != ReadTwoBridge.* && ! -e "$temp/$dir/$name" ]]; then
      ln -s "$entry" "$temp/$dir/$name"
    fi
  done
done

cd "$lean_dir"
lake env bash -eu -c '
  here=$1
  temp=$2
  module=$3
  bridge=$4
  export LEAN_PATH="$temp:$LEAN_PATH"
  lean -R "$temp" -o "$temp/$module.olean" "$temp/$module.lean"
  lean -R "$temp" -o "$temp/$bridge.olean" "$temp/$bridge.lean"
  lean -R "$here/threshold" -o "$temp/ReadMonotone.olean" "$here/threshold/ReadMonotone.lean"
  lean "$here/threshold/Threshold.lean"
  lean "$here/IncidenceRead.lean"
  lean -R "$here/factors" -o "$temp/FactorCount.olean" "$here/factors/FactorCount.lean"
  lean "$here/factors/PrivateFrontier.lean"
  lean "$here/factors/ExactClauses.lean"
  lean "$here/control/ScalarControl.lean"
  lean "$here/localized/LocalizedFano.lean"
  lean "$here/algebra/PairAlgebra.lean"
' -- "$here" "$temp" "$module" "$bridge"
