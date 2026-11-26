#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
project=$(cd "${1:?supply the pinned upstream Lean project directory}" && pwd)
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
python3 -B "$here/prepare-check.py" "$build"
cd "$project"
paths="$(lake env printenv LEAN_PATH)${LEAN_PATH:+:$LEAN_PATH}"
# Lean takes one package prefix. Expose Defs and the new proof in the same package.
mkdir -p "$build/lib/PEqualNP/Outside"
LEAN_PATH="$paths" python3 -B - "$build/lib/PEqualNP" <<'PY'
import os, sys
from pathlib import Path
target = Path(sys.argv[1])
candidates = [Path(p) / "PEqualNP" for p in os.environ["LEAN_PATH"].split(os.pathsep) if p]
package = next((p for p in candidates if (p/"Defs.olean").is_file() and (p/"Defs").is_dir()), None)
if package is None:
    raise SystemExit("Run lake build +PEqualNP.Defs in the project and retry.")
for src in [package/"Defs", *package.glob("Defs.*")]:
    (target/src.name).symlink_to(src.resolve(), target_is_directory=src.is_dir())
PY
export LEAN_PATH="$build/lib:$paths"
module=PEqualNP.Outside.ForkUpper9742
file=PEqualNP/Outside/ForkUpper9742
lean -j1 --root="$build/source" -o "$build/lib/$file.olean" "$build/source/$file.lean"
checker=(lean --run CheckLemma.lean)
if [[ -x "$project/.lake/build/bin/checklemma" ]]; then checker=("$project/.lake/build/bin/checklemma"); fi
"${checker[@]}" "$module" "$build/upper63.txt" check > "$build/upper.log"
grep '^ACCEPTED (check):' "$build/upper.log"
if "${checker[@]}" "$module" "$build/control62.txt" check > "$build/control.log"; then
    echo 'The 63-gate witness unexpectedly passed for a 62-gate budget.' >&2
    exit 1
fi
grep '^REJECTED (statement):' "$build/control.log" | cut -c1-120
