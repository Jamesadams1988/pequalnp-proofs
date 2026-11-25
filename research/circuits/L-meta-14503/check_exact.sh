#!/usr/bin/env bash
# Supply the upstream lean/ directory with its pinned Mathlib and PEqualNP.Defs built.
# Put its Lean 4.36.0 toolchain on PATH.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
project=$(cd "${1:?supply the prepared upstream lean/ directory}" && pwd)
lean_prefix=$(cd "$project" && lean --print-prefix)
lean_bin="$lean_prefix/bin/lean"
[[ "$("$lean_bin" --short-version)" == 4.36.0 ]]
build=$(mktemp -d)
trap 'rm -rf -- "$build"' EXIT
mkdir -p "$build/PEqualNP/Outside"
cd "$build"
libs=("$build" "$project/.lake/build/lib/lean" "$project"/.lake/packages/*/.lake/build/lib/lean)
export LEAN_PATH
LEAN_PATH=$(IFS=:; echo "${libs[*]}")
for entry in "$project"/.lake/build/lib/lean/PEqualNP/*; do
  if [[ "${entry##*/}" != Outside ]]; then
    ln -s -- "$entry" PEqualNP/
  fi
done
# Source hashes from upstream 6bf43eb12e4309eb4a3a9856fb88db9504e05296.
cp -- "$project"/PEqualNP/Outside/L_meta_{4795,9526}.lean PEqualNP/Outside/
sha256sum -c <<'HASHES'
5e85e410b1778e17b12481072680e6bdc76b5a8de2aa1d9ac6d69d1ee1c43c33  PEqualNP/Outside/L_meta_4795.lean
f0b349c8769119a77e899f1dcf0027f3f08e784994841d27ee59006ae631e838  PEqualNP/Outside/L_meta_9526.lean
HASHES
for module in L_meta_4795 L_meta_9526; do
  src="PEqualNP/Outside/$module"
  "$lean_bin" -j1 -R "$build" -o "$src.olean" "$src.lean"
done
"$lean_bin" -j1 -R "$here" -o ExactMinimum.olean "$here/ExactMinimum.lean"
