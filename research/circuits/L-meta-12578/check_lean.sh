#!/usr/bin/env bash
# Run from any directory. The argument is the upstream project's lean/ directory.
set -euo pipefail
research_dir=$(cd "$(dirname "$0")" && pwd)
project_dir=$(cd "${1:?supply the path to the upstream lean directory}" && pwd)
build_dir=$(mktemp -d)
trap 'rm -rf -- "$build_dir"' EXIT
cd "$project_dir"
lake build +PEqualNP.MetaComplexity.Helpers.PermInputs +PEqualNP.Outside.L_meta_8683
lake env bash -euo pipefail -c '
  research_dir=$1
  build_dir=$2
  export LEAN_PATH="$build_dir:${LEAN_PATH}"
  for module in Structure Witness ExactAudit SplitTransfer SplitAudit; do
    lean -j1 -R "$research_dir" -o "$build_dir/$module.olean" "$research_dir/$module.lean"
    echo "Checked $module"
  done
' bash "$research_dir" "$build_dir"
