#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
project=$(cd "${1:?supply the pinned upstream lean directory}" && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
cd "$project"
python3 -B "$here/check-sources.py" "$project"
lake build +PEqualNP.Outside.L_meta_534 +PEqualNP.Outside.L_meta_17110
lake env bash -eu -c '
  export LEAN_PATH="$1:$LEAN_PATH"
  lean -R "$2" -o "$1/Upper.olean" "$2/Upper.lean"
  lean -R "$2" -o "$1/CaseAudit.olean" "$2/CaseAudit.lean"
' -- "$tmp" "$here"
if [[ ${2:-} == --full ]]; then
  for n in 17303 17305 17307 17313 17315 17317 17319 17321 17323; do
    lake build "+PEqualNP.Outside.L_meta_$n"
  done
  lake env bash -eu -c 'export LEAN_PATH="$1:$LEAN_PATH"; lean -R "$2" "$2/Exact.lean"' -- "$tmp" "$here"
fi
