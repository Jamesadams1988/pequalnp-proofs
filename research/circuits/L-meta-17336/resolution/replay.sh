#!/usr/bin/env bash
set -euo pipefail
if [[ $# -lt 2 || $# -gt 3 ]]; then
  echo "Usage: $0 PROJECT_LEAN WITNESSES_LEAN [--closed]" >&2
  exit 2
fi
if [[ $# -eq 3 && $3 != --closed ]]; then
  echo "The optional third argument is --closed" >&2
  exit 2
fi
here=$(cd "$(dirname "$0")" && pwd)
project=$(cd "$1" && pwd)
witness=$(realpath "$2")
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
cd "$project"
if [[ ${3:-} == --closed ]]; then
  python3 - "$here" "$project" <<'CHECK_SOURCE'
from pathlib import Path
import hashlib
import json
import sys

here, project = map(Path, sys.argv[1:])
receipt = json.loads((here / "verdict.json").read_text())
source = (project / "PEqualNP/Outside/L_meta_17335.lean").read_bytes()
if hashlib.sha256(source).hexdigest() != receipt["sha256"]:
    raise SystemExit("The upstream source differs from the checked verdict.")
marker = "theorem PEqualNP.Outside.L_meta_17335 : "
before, separator, definition = source.decode().rpartition(marker)
signature, assignment, _ = definition.partition(" :=")
if not separator or not assignment or signature not in (here / "ExactOrFirst.lean").read_text():
    raise SystemExit("The upstream theorem type differs from the corollary hypothesis.")
print("Upstream checked-source digest and theorem type verified.")
CHECK_SOURCE
fi
lake env lean -j1 --root="$(dirname "$witness")" -o "$build/Witnesses.olean" "$witness"
export LEAN_PATH="$build${LEAN_PATH:+:$LEAN_PATH}"
lake env lean -j1 --root="$here" -o "$build/ExactOrFirst.olean" "$here/ExactOrFirst.lean"
if [[ $# -eq 3 ]]; then
  lake env lean -j1 --root="$here" "$here/From17335.lean"
fi
