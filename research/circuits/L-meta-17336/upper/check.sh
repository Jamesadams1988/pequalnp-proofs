#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
if [ "$#" -ne 1 ]; then
  echo "Usage: $0 /path/to/built/pequalnp-proofs/lean" >&2
  exit 2
fi
project=$(cd "$1" && pwd)
cd "$project"
exec lake env lean "$here/Witnesses.lean"
