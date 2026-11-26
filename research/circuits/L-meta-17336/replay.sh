#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
project=$(cd "${1:?Pass the configured upstream Lean directory}" && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
export PYTHONDONTWRITEBYTECODE=1
python3 "$here/check-project.py" "$project"
python3 "$here/centers/verify.py" | diff -u "$here/centers/results.txt" -
python3 "$here/upper/verify.py" "$here/centers/statement.json" | diff -u "$here/upper/truth-tables.txt" -
cd "$project"
lake build +PEqualNP.Defs.MetaComplexityMinimal +PEqualNP.MetaComplexity.Helpers.PermInputs
lake env lean "$here/upper/Witnesses.lean"
lake env lean -R "$here/lower" -o "$tmp/Transfer.olean" "$here/lower/Transfer.lean"
lake env bash -eu -c '
  export LEAN_PATH="$1:$LEAN_PATH"
  lean -R "$2/lower" -o "$1/Transfer3.olean" "$2/lower/Transfer3.lean"
  lean "$2/lower/Masks.lean"
' -- "$tmp" "$here"
if [[ ${BUILD_DONOR:-0} == 1 ]]; then
  lake build +PEqualNP.Outside.L_meta_8455 +PEqualNP.Outside.L_meta_8459
  lake env bash -eu -c 'export LEAN_PATH="$1:$LEAN_PATH"; lean "$2/lower/From8455.lean" && lean "$2/lower/From8459.lean"' -- "$tmp" "$here"
fi
