#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
project=$(cd "${1:?pass the prepared upstream lean project}" && pwd)
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
(cd "$here" && sha256sum -c SHA256SUMS)
python3 -B "$here/../../witness/emit.py" "$here/trace377.json" "$build/Tree377.lean" --budget 377 --tree
cmp "$here/Tree377.lean" "$build/Tree377.lean"
printf 'import Tree377\n#print axioms Row169.refutation377\n#print axioms Row169.tree377\n' > "$build/Audit.lean"
cd "$project"
lake env bash -euo pipefail -c '
  export LEAN_PATH="$1:${LEAN_PATH:-}"
  lean -j1 --root="$1" -o "$1/Tree377.olean" "$1/Tree377.lean"
  lean -j1 --root="$2/../formal" -o "$1/QueryTree.olean" "$2/../formal/QueryTree.lean"
  lean -j1 --root="$2/../formal" -o "$1/OrdinaryTree.olean" "$2/../formal/OrdinaryTree.lean"
  lean -j1 --root="$2" "$2/PureTree189.lean" | tee "$1/bridge.log"
  grep -Fx "'\''Row169.pureTree189'\'' depends on axioms: [propext, Classical.choice, Quot.sound]" "$1/bridge.log" >/dev/null
  lean -j1 --root="$1" "$1/Audit.lean" | tee "$1/audit.log"
  for name in Row169.refutation377 Row169.tree377; do
    grep -Fx "'\''$name'\'' depends on axioms: [propext, Classical.choice, Quot.sound]" "$1/audit.log" >/dev/null
  done
' bash "$build" "$here"
