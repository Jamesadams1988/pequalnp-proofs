#!/usr/bin/env bash
# Supply the upstream lean/ directory with Mathlib and PEqualNP.Defs built.
# Set PATH to its Lean 4.36.0 toolchain. Witness.lean defaults to the adjacent file.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
project=$(cd "${1:?supply the prepared upstream lean/ directory}" && pwd)
witness=${2:-"$here/Witness.lean"}
lean_prefix=$(cd "$project" && lean --print-prefix)
lean_bin="$lean_prefix/bin/lean"
build=$(mktemp -d)
trap 'rm -rf -- "$build"' EXIT
mkdir -p "$build/PEqualNP/Outside"
cp -- "$witness" "$build/Witness.lean"
cd "$build"

# Witness.lean is James Adams's public 11-gate construction at commit ccd14374bc4a.
printf '%s  %s\n' 4fe23079e234554ce223dd8a45d3c42ca894d8da6c5377b8686d20870fb2d33c Witness.lean | sha256sum -c -
[[ "$("$lean_bin" --short-version)" == 4.36.0 ]]
libs=("$build" "$project/.lake/build/lib/lean" "$project"/.lake/packages/*/.lake/build/lib/lean)
export LEAN_PATH
LEAN_PATH=$(IFS=:; echo "${libs[*]}")

# Lean picks a search-path entry for an entire top-level package. Expose the
# prepared project modules in the same temporary package as the two fresh helpers.
for entry in "$project"/.lake/build/lib/lean/PEqualNP/*; do
  if [[ "${entry##*/}" != Outside ]]; then
    ln -s -- "$entry" PEqualNP/
  fi
done

# Rebuild both cited helpers from the pinned source even if the checkout has cached modules.
# File hashes are from upstream 6bf43eb12e4309eb4a3a9856fb88db9504e05296.
cp -- "$project"/PEqualNP/Outside/L_meta_{4795,9526}.lean PEqualNP/Outside/
sha256sum -c <<'HASHES'
5e85e410b1778e17b12481072680e6bdc76b5a8de2aa1d9ac6d69d1ee1c43c33  PEqualNP/Outside/L_meta_4795.lean
f0b349c8769119a77e899f1dcf0027f3f08e784994841d27ee59006ae631e838  PEqualNP/Outside/L_meta_9526.lean
HASHES
for module in L_meta_4795 L_meta_9526; do
  src="PEqualNP/Outside/$module"
  "$lean_bin" -j1 -R "$build" -o "$src.olean" "$src.lean"
done
"$lean_bin" -j1 -R "$build" -o Witness.olean Witness.lean
"$lean_bin" -j1 -R "$here" -o ExactMinimum.olean "$here/ExactMinimum.lean"
