#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
project=$(cd "${1:?supply the proofs project lean directory}" && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
python3 -B "$root/upper/make-check.py" "$tmp"
cd "$project"
lookup() { printf '%s' "$(lake env printenv LEAN_PATH)${LEAN_PATH:+:$LEAN_PATH}"; }
paths=$(lookup)
if ! LEAN_PATH="$paths" python3 -B "$root/link-lean-path.py" "$tmp/build" upper; then
    lake build +PEqualNP.Defs
    paths=$(lookup)
    LEAN_PATH="$paths" python3 -B "$root/link-lean-path.py" "$tmp/build" upper
fi
export LEAN_PATH="$tmp/build:$paths"
module=PEqualNP.Outside.ForkUpper11021
file=PEqualNP/Outside/ForkUpper11021
lean -j1 --root="$tmp/source" -o "$tmp/build/$file.olean" "$tmp/source/$file.lean"
checker=(lean --run CheckLemma.lean)
if [[ -x "$project/.lake/build/bin/checklemma" ]]; then
    checker=("$project/.lake/build/bin/checklemma")
fi
"${checker[@]}" "$module" "$tmp/upper.txt" check > "$tmp/upper.log"
grep -F 'ACCEPTED (check): PEqualNP.Outside.ForkUpper11021' "$tmp/upper.log" | cut -d';' -f1-2
if "${checker[@]}" "$module" "$tmp/control15.txt" check > "$tmp/control.log" 2>&1; then
    echo "15-gate negative control unexpectedly passed" >&2
    exit 1
fi
grep -F 'REJECTED (statement):' "$tmp/control.log" > /dev/null
echo 'The mathematical checker rejected the 15-gate negative control for a statement mismatch.'
