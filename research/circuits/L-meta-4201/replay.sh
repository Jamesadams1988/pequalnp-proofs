#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
project=$(realpath "${1:?pass the upstream lean project directory}")
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
python3 -B "$here/candidate/test_verify_candidate.py"
cd "$project"
lake build PEqualNP.Defs PEqualNP.MetaComplexity.Helpers.CoverCircuitList
lake env bash -euo pipefail -c '
  export LEAN_PATH="$1:${LEAN_PATH:-}"
  here=$2
  for module in ExtremalVerifier PlaneVerifier Separation ChargeCount Charging PGSequence PGForty PGHexSequence ZeroSensitivity Extremal PG4Sensitivity StarBound RectanglePlane RectangleTruth FilteredOutput SpanningGraph Upper125 Restriction CoreTransfer General HexSignature HexNormalize DagToCode CodeToHex EmbeddedFive PGFortyOne HexFour PGFortyOneNative; do
    echo "Checking $module"
    lean -j1 --root="$here" -o "$1/$module.olean" "$here/$module.lean"
  done
' bash "$build" "$here"
