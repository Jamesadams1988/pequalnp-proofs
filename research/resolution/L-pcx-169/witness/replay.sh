#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
project=$(cd "${1:?pass the prepared upstream lean project}" && pwd)
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
(cd "$here" && sha256sum -c SHA256SUMS)
python3 -B "$here/emit.py" "$here/trace157.json" "$build/Hall157.lean" --budget 157
cmp "$here/Hall157.lean" "$build/Hall157.lean"
printf 'import Hall157\n#print axioms Row169.refutation157\n' > "$build/Audit.lean"
cd "$project"
lake env bash -euo pipefail -c '
  export LEAN_PATH="$1:${LEAN_PATH:-}"
  lean -j1 --root="$1" -o "$1/Hall157.olean" "$1/Hall157.lean"
  lean -j1 --root="$1" "$1/Audit.lean" | tee "$1/audit.log"
  grep -Fx "'\''Row169.refutation157'\'' depends on axioms: [propext, Classical.choice, Quot.sound]" "$1/audit.log" >/dev/null
' bash "$build"
