#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")" && pwd)
project=$(cd "${1:?supply the upstream lean directory}" && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
cd "$root"
python3 -B - "$project" <<'PY'
import hashlib
import json
from pathlib import Path
import sys

project = Path(sys.argv[1])
sources = json.loads(Path('sources.json').read_text())
for entry in sources['checked_dependencies'].values():
    data = (project.parent / entry['file']).read_bytes()
    if hashlib.sha256(data).hexdigest() != entry['file_sha256']:
        raise ValueError(f"input changed: {entry['id']}")
posted = json.loads(Path('statement.json').read_text())['statement']
end = '(63 : ℕ) ≤ x1.size'
assert posted.endswith(end)
wrapper = posted[:-len(end)] + '(30 : ℕ) ≤ x1.size'
assert wrapper in Path('lower/Lower.lean').read_text()
print('Three source digests and literal 30-gate lower-bound specialization match.')
PY
python3 -B upper/verify.py
python3 -B read-once/check_cover.py
python3 -B read-once/four_vertices.py
python3 -B elimination-limit/cap.py
python3 -B transversals/check.py | diff - transversals/expected.txt
python3 -B supergraphs/coalescence.py | diff - supergraphs/results.txt
c++ -std=c++20 -O3 read-once/check.cpp -o "$tmp/read-once"
"$tmp/read-once" | diff - read-once/expected.txt
c++ -std=c++20 -O3 fractional/verify.cpp -o "$tmp/fractional"
"$tmp/fractional" | diff - fractional/expected.txt
c++ -std=c++20 -O3 false-pairs/verify.cpp -o "$tmp/false-pairs"
"$tmp/false-pairs"
cd "$project"
lake build +PEqualNP.MetaComplexity.Helpers.PermInputs +PEqualNP.Outside.L_meta_6528 +PEqualNP.Outside.L_meta_4580 +PEqualNP.Outside.L_meta_1500
bash "$root/lower/replay.sh" "$project"
for proof in upper/Upper64.lean support/TwoFactors.lean support/SplitCover.lean support/ConeCount.lean transversals/FactorTransversal.lean; do
  lake env lean "$root/$proof"
done
