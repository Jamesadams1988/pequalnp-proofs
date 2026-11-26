#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")" && pwd)
cd "$root"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
python3 -B upper/check_stars.py assignment.json | diff -u upper/results.txt -
python3 -B symmetry/first_gate_symmetry.py assignment.json | diff -u symmetry/first_gate_orbits.json -
python3 -B solver/verify_encoding.py > "$tmp/sat.json"
python3 -B - "$tmp/sat.json" <<'PY'
import json,sys
from pathlib import Path
live=json.loads(Path(sys.argv[1]).read_text()); ref=json.loads(Path("solver/verification.json").read_text())
assert live==ref
print("Verified small SAT instances and all witness clauses.")
PY
c++ -O3 -std=c++20 cofactors/bound.cpp -o "$tmp/bound"
python3 -B cofactors/extract.py | "$tmp/bound" | diff -u cofactors/expected.txt -
python3 -B cofactors/small_audit.py --solver "$tmp/bound"
