#!/usr/bin/env bash
# Run in a pinned upstream lean/ checkout with PEqualNP.Defs and its pinned dependencies built.
set -eu
research_dir=$(cd "$(dirname "$0")" && pwd)
replay_dir=$(mktemp -d)
trap 'rm -rf "$replay_dir"' EXIT
replay() {
  lake env sh -c '
    export LEAN_PATH="$1:$LEAN_PATH"
    exec lean --root="$2" -o "$1/$3.olean" "$2/$3.lean"
  ' sh "$replay_dir" "$research_dir" "$1"
}
if [[ "${1:-}" == read-once ]]; then
  replay SignedFrontier
  for module in SemanticCuts SignedChildren Rectangle SmallSide Concrete ZeroReject Borderline AutoRectangle AutoExamples PinSavings Polarity PolarityCase; do
    replay "$module"
  done
  exit 0
fi
replay ThresholdCircuit
replay SignedFrontier
replay Symmetry
replay FrontierGoal
replay Prune
replay MaskPrune
replay Head13
replay CompactLayer
replay UniformChunks
replay UniformPilot
replay PrunedSearch
replay Branch13
replay SmallGroup
replay Child27Case
