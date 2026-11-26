"""Check a two-gate-elimination manifest for the literal L-meta-9769 graph.

Usage: python3 check.py cert-50.txt --claim 50 [--assignment assignment-public.json]
A conventional cert-N.txt filename supplies the claim if --claim is omitted.
Input lines are four decimal integers: ordinary left mask, ordinary right mask,
local goal, and pivot wire in 0..41. Every path is checked independently.
"""
import argparse
from collections import Counter
from dataclasses import dataclass
import json
from pathlib import Path
import re

# Point rows and original line wire IDs, transcribed from the Lean disjunction.
ROWS = (
    (26,28,38,41), (21,22,27,29,39), (22,23,28,30,40), (23,24,29,31,41),
    (21,24,25,30,32), (22,25,26,31,33), (23,26,27,32,34), (24,27,28,33,35),
    (25,28,29,34,36), (26,29,30,35,37), (27,30,31,36,38), (28,31,32,37,39),
    (29,32,33,38,40), (30,33,34,39,41), (21,31,34,35,40), (22,32,35,36,41),
    (21,23,33,36,37), (22,24,34,37,38), (23,25,35,38,39), (24,26,36,39,40),
    (25,27,37,40,41),
)
EDGES = tuple((p, l) for p, row in enumerate(ROWS) for l in row)
TERMS = tuple((1 << p) | (1 << l) for p, l in EDGES)
SHORE = (1 << 21) - 1
ALL = (1 << 42) - 1


def require(condition, message):
    if not condition:
        raise ValueError(message)


def bits(word):
    while word:
        bit = word & -word
        yield bit
        word ^= bit


def evaluate(ones):
    return any(ones & e == e for e in TERMS)


@dataclass
class Residual:
    units: int
    ordinary: int
    witnesses: dict


def substitute(ones, zeros):
    """Substitute all path pins into the original DNF, then apply u OR (u AND v) = u."""
    units = 0
    pairs = []
    for term in TERMS:
        if term & zeros:
            continue
        free = term & ~ones
        require(free != 0, "true constant cofactor")
        if free & (free - 1):
            pairs.append(free)
        else:
            units |= free
    witnesses = {u: u for u in bits(units)}
    ordinary = 0
    for pair in pairs:
        if pair & units:
            continue
        ordinary |= pair
        for v in bits(pair):
            witnesses[v] = pair
    require(bool(witnesses), "false constant cofactor")
    # A direct monotone Boolean test on this cofactor's extreme assignments.
    require(not evaluate(ones) and evaluate(ALL ^ zeros), "cofactor is constant")
    return Residual(units, ordinary, witnesses)


def check_dependency(ones, zeros, bit, term):
    """Concrete pair of full assignments agreeing off the given bit."""
    low = ones | (term & ~bit)
    high = low | bit
    require(not ((ones | zeros) & bit) and not (high & zeros), "invalid dependency witness pins")
    require(not evaluate(low) and evaluate(high), "invalid dependency witness against the literal graph")


def load_manifest(path, claim):
    manifest = {}
    for line_number, raw in enumerate(path.read_text().splitlines(), 1):
        words = raw.split()
        require(len(words) == 4 and all(re.fullmatch(r"[0-9]+", w) for w in words),
                f"line {line_number}: expected four decimal integers")
        left, right, goal, pivot = map(int, words)
        require(0 < left <= SHORE and 0 < right <= SHORE and 0 < goal <= claim and 0 <= pivot < 42,
                f"line {line_number}: field out of range")
        key = left, right, goal
        require(key not in manifest, f"line {line_number}: repeated triple {key}")
        manifest[key] = pivot
    return manifest


def verify(manifest, claim):
    reached = set()
    depths = Counter()
    splits = 0
    smallest_leaf_bound = None

    def walk(ones, zeros, depth):
        nonlocal splits, smallest_leaf_bound
        state = substitute(ones, zeros)
        essential = len(state.witnesses)
        leaf_bound = essential - 1 + 2 * depth
        if leaf_bound >= claim:
            for bit, term in state.witnesses.items():
                check_dependency(ones, zeros, bit, term)
            depths[depth] += 1
            smallest_leaf_bound = leaf_bound if smallest_leaf_bound is None else min(smallest_leaf_bound, leaf_bound)
            return
        key = state.ordinary & SHORE, state.ordinary >> 21, claim - 2 * depth - state.units.bit_count()
        require(key in manifest, f"insufficient leaf {leaf_bound} < {claim}, missing split {key}")
        pivot = 1 << manifest[key]
        require(pivot in state.witnesses, f"pivot is inessential at {key}")
        check_dependency(ones, zeros, pivot, state.witnesses[pivot])
        reached.add(key)
        splits += 1
        # Both cofactors must pass; no earlier visit to a key discharges this path.
        walk(ones, zeros | pivot, depth + 1)
        walk(ones | pivot, zeros, depth + 1)

    walk(0, 0, 0)
    unused = manifest.keys() - reached
    require(not unused, f"{len(unused)} extraneous manifest triples; first {min(unused) if unused else None}")
    return len(reached), splits, sum(depths.values()), sorted(depths.items()), smallest_leaf_bound


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--claim", type=int)
    parser.add_argument("--assignment", type=Path)
    args = parser.parse_args()
    claim = args.claim
    if claim is None:
        match = re.fullmatch(r"cert-([0-9]+)\.txt", args.manifest.name)
        require(match is not None, "give --claim for a nonstandard filename")
        claim = int(match[1])
    require(claim > 0, "claim must be positive")
    require(len(EDGES) == len(set(EDGES)) == 104, "invalid embedded edge list")
    if args.assignment:
        desk = json.loads(args.assignment.read_text())
        require(desk["id"] == "L-meta-9769", "wrong assignment ID")
        extracted = [tuple(map(int, pair)) for pair in re.findall(r"\(x (\d+) && x (\d+)\)", desk["statement"])]
        require(len(extracted) == len(EDGES) and set(extracted) == set(EDGES), "different assignment graph")
    states, paths, leaves, depths, leaf_min = verify(load_manifest(args.manifest, claim), claim)
    print(f"verified lower bound {claim}; manifest states {states}; internal path visits {paths}; leaves {leaves}")
    print(f"leaf depths {depths}; smallest certified path bound {leaf_min}")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, KeyError) as exc:
        raise SystemExit(f"certificate rejected: {exc}")
