#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
project=$(cd "${1:?pass the upstream lean project directory}" && pwd)
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
(cd "$here" && sha256sum -c SHA256SUMS)
python3 -B "$here/emit.py" "$here/trace149.json" "$build/Witness149.lean" --budget 149
cmp "$here/Witness149.lean" "$build/Witness149.lean"
cat > "$build/Audit.lean" <<'LEAN'
import Witness149
#print axioms Row133.refutation149
LEAN
cd "$project"
lake env bash -euo pipefail -c '
  export LEAN_PATH="$1:${LEAN_PATH:-}"
  lean -j1 --root="$1" -o "$1/Witness149.olean" "$1/Witness149.lean"
  lean -j1 --root="$1" "$1/Audit.lean" | tee "$1/audit.log"
  grep -F -x "'\''Row133.refutation149'\'' depends on axioms: [propext, Classical.choice, Quot.sound]" "$1/audit.log" >/dev/null
' bash "$build"
