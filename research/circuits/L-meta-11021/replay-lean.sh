#!/usr/bin/env bash
# Compile the pinned proof bodies, the joined theorems and the mathematical verifier.
set -euo pipefail
root=$(cd "$(dirname "$0")" && pwd)
project=$(cd "${1:?supply the pinned project lean directory}" && pwd)
cd "$project"
python3 -B - "$root" <<'PY'
import hashlib
import json
from pathlib import Path
import sys
root = Path(sys.argv[1])
inputs = json.loads((root / 'sources/dependencies.json').read_text())
for row in inputs['dependencies']:
    source = Path.cwd().parent / row['file']
    if hashlib.sha256(source.read_bytes()).hexdigest() != row['sha256']:
        raise SystemExit(f"changed dependency: {row['row']}")
assignment = json.loads((root / 'sources/assignment.json').read_text())
if assignment['statement'] != (root / 'sources/negative.txt').read_text().rstrip('\n'):
    raise SystemExit('wrong statement for verifier')
print('Matched all eleven upstream source hashes and the assigned statement.')
PY
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
# A prepared project's compiled dependencies can be reused with --prebuilt.
# The normal invocation compiles all eleven directly from the verified files.
deps=(534 17107 17103 17269 17271 17273 17275 17277 17279 17281 17283)
case "${2:-}" in
  '') rebuild=yes; lake build +PEqualNP.Defs +PEqualNP.MetaComplexity.Helpers.Shannon ;;
  --prebuilt) rebuild=no ;;
  *) echo "unknown option: $2" >&2; exit 2 ;;
esac
mkdir -p "$build/PEqualNP/Outside"
export LEAN_PATH="$build:$(lake env printenv LEAN_PATH)${LEAN_PATH:+:$LEAN_PATH}"
if [[ $rebuild == yes ]]; then
    python3 -B "$root/link-lean-path.py" "$build" no
    for n in "${deps[@]}"; do
        file="PEqualNP/Outside/L_meta_$n"
        lean -j1 --root="$project" -o "$build/$file.olean" "$project/$file.lean"
    done
else
    python3 -B "$root/link-lean-path.py" "$build" yes
fi
for file in upper/Upper lower/CaseAudit lower/UpperJoin lower/ExactLower lower/ExactMinimum \
            depth/TreeBase depth/Emit depth/Unfold depth/DepthBound depth/DepthJoin depth/ExactDepth; do
    lean -j1 --root="$root/${file%/*}" -o "$build/${file##*/}.olean" "$root/$file.lean"
done
file=PEqualNP/Outside/L_meta_11021
lean -j1 --root="$root/lower/src" -o "$build/$file.olean" "$root/lower/src/$file.lean"
checker=(lean --run CheckLemma.lean)
if [[ -x "$project/.lake/build/bin/checklemma" ]]; then
    checker=("$project/.lake/build/bin/checklemma")
fi
"${checker[@]}" PEqualNP.Outside.L_meta_11021 "$root/sources/negative.txt" refute
