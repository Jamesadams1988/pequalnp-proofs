#!/usr/bin/env bash
set -eu
root=$(cd "$(dirname "$0")" && pwd)
lean_root=$(cd "${1:?Pass the configured pequalnp-proofs lean directory}" && pwd)
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
python3 "$root/traces.py"
c++ -std=c++17 -O3 "$root/read-once/readonce.cpp" -o "$scratch/readonce"
"$scratch/readonce" > "$scratch/readonce.txt"
diff -u "$root/read-once/results.txt" "$scratch/readonce.txt"
c++ -std=c++17 -O2 "$root/dag/clique_dag.cpp" -o "$scratch/dag"
"$scratch/dag" > "$scratch/dag.txt"
diff -u "$root/dag/bounds.txt" "$scratch/dag.txt"
cd "$lean_root"
for src in "$root"/{Control196,DepthThree211}.lean "$root"/rank/*.lean "$root"/trees/*.lean; do
  lake env lean "$src"
done
