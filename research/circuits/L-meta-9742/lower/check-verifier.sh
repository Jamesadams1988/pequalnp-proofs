#!/usr/bin/env bash
set -euo pipefail
proofs=$(cd "$(dirname "$0")" && pwd)
project=$(cd "${1:?supply the pinned upstream Lean project directory}" && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
cd "$project"
if [[ ${2:-} != --prebuilt ]]; then lake build +PEqualNP.Outside.L_meta_614; fi
project_paths="$(lake env printenv LEAN_PATH)${LEAN_PATH:+:$LEAN_PATH}"
LEAN_PATH="$project_paths" python3 -B - "$work" "$proofs" <<'PY'
import json, os, sys
from pathlib import Path
work, proofs = map(Path,sys.argv[1:])
dest=work/"PEqualNP"
(dest/"Outside").mkdir(parents=True)
paths=[Path(p)/"PEqualNP" for p in os.environ["LEAN_PATH"].split(os.pathsep) if p]
defs=next(p for p in paths if (p/"Defs").is_dir() and (p/"Defs.olean").is_file())
for src in [defs/"Defs",*defs.glob("Defs.*")]:
    (dest/src.name).symlink_to(src.resolve(),target_is_directory=src.is_dir())
donor=next(p/"Outside/L_meta_614.olean" for p in paths if (p/"Outside/L_meta_614.olean").is_file())
(dest/"Outside"/donor.name).symlink_to(donor.resolve())
s=json.loads((proofs.parent/"assignment.json").read_text())["statement"]
assert s.count("C.size ≤ 62")==1
assert (proofs/"checker/lower.statement").read_text().rstrip("\n")==s.replace("C.size ≤ 62","C.size ≤ 37")
PY
export LEAN_PATH="$work:$project_paths"
file=PEqualNP/Outside/ForkLower9742
lean -j1 --root="$proofs/checker" -o "$work/$file.olean" "$proofs/checker/$file.lean"
checker=(lean --run CheckLemma.lean)
if [[ -x "$project/.lake/build/bin/checklemma" ]]; then checker=("$project/.lake/build/bin/checklemma"); fi
"${checker[@]}" PEqualNP.Outside.ForkLower9742 "$proofs/checker/lower.statement" check
