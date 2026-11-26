#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
if [[ $# -gt 1 ]]; then
  echo 'Usage: bash replay.sh [path/to/reviewed/L_meta_17335.lean]' >&2
  exit 2
fi
reviewed_source=''
if [[ $# -eq 1 ]]; then
  reviewed_source=$(realpath "$1")
elif [[ -f "$here/Prior17335.lean" ]]; then
  reviewed_source="$here/Prior17335.lean"
fi
stage=$(mktemp -d)
trap 'rm -rf "$stage"' EXIT
cp "$here"/{replay_extract.py,inspect_tables.py,allowlist.tsv} "$stage/"
cd "$stage"
if [[ -n "$reviewed_source" ]]; then
  cp "$reviewed_source" Prior17335.lean
else
  curl -fsSL 'https://raw.githubusercontent.com/open-goat/pequalnp-proofs/d8cf13b117c0488da25b467d9bebe19b896323b5/lean/PEqualNP/Outside/L_meta_17335.lean' -o Prior17335.lean
fi
echo '4defc64e8c1808d31eb16e4d092560256cadea0b1f32be2d604d9413002b10a2  Prior17335.lean' | sha256sum -c -
python3 inspect_tables.py
python3 replay_extract.py
lean_bin=${LEAN_BIN_DIR:-$(dirname "$(command -v lean)")}
"$lean_bin/lean" -j1 -c Numerical.c Numerical.lean
"$lean_bin/leanc" -O2 -o numerical Numerical.c
./numerical
