#!/usr/bin/env bash
# Rebuild the pinned zero-pivot proof under its ordinary outside-proof module names.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
project=$(cd "${1:?supply the pinned project lean directory}" && pwd)
destination=${2:?supply a new or empty build directory}
mkdir -p "$destination"
out=$(cd "$destination" && pwd)
if [[ -n $(ls -A "$out") ]]; then
    echo "use a new or empty build directory: $out" >&2
    exit 2
fi

cd "$project"
python3 -B "$here/generate.py" PEqualNP/Outside/L_meta_17103.lean "$out"
lake build +PEqualNP.Defs
lean_compiler=$(lake env which lean)
export LEAN_PATH="$out:$(lake env printenv LEAN_PATH)${LEAN_PATH:+:$LEAN_PATH}"
python3 -B "$here/../../link-lean-path.py" "$out" upper
for source in "$out"/PEqualNP/Outside/Split17103/P*.lean; do
    part=${source##*/P}
    number=${part%.lean}
    options=(-M 6000)
    if (( 10#$number >= 59 )); then
        options=(-DElab.async=false -M 8000)
    fi
    "$lean_compiler" -j1 "${options[@]}" --root="$out" -o "${source%.lean}.olean" "$source"
done
wrapper="$out/PEqualNP/Outside/L_meta_17103"
"$lean_compiler" -j1 -DElab.async=false -M 8000 --root="$out" -o "$wrapper.olean" "$wrapper.lean"
