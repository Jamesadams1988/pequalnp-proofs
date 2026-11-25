#!/usr/bin/env python3
"""Check a binary AND/OR gate list against all inputs for L-meta-9791.

Usage: python3 check_circuit.py [candidate.json]
An input mask has bit i set exactly when vertex i is active.
Exit codes: 0 for exact agreement, 1 for a counterexample, 2 for invalid input.
"""

import argparse
import json
from pathlib import Path

# The ordered edge list in the L-meta-9791 statement. Vertices 0..12 are points,
# and vertices 13..23 are lines. Inputs retain the desk's vertex numbering.
EDGES = (
    (0, 15), (0, 21), (0, 23), (1, 16), (1, 22), (2, 13), (2, 17), (2, 23),
    (3, 13), (3, 14), (3, 18), (4, 14), (4, 15), (4, 19), (5, 13), (5, 15),
    (5, 16), (5, 20), (6, 14), (6, 16), (6, 17), (6, 21), (7, 15), (7, 17),
    (7, 18), (7, 22), (8, 16), (8, 18), (8, 19), (8, 23), (9, 17), (9, 19),
    (9, 20), (10, 18), (10, 20), (10, 21), (11, 13), (11, 19), (11, 21),
    (11, 22), (12, 14), (12, 20), (12, 22), (12, 23),
)
POINTS, LINES = 13, 11
INPUTS = POINTS + LINES


def load_circuit(path):
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict) or not isinstance(data.get("gates"), list):
        raise ValueError("expected an object containing a gates list and an output wire")
    gates = data["gates"]
    for wire, gate in enumerate(gates, INPUTS):
        if not isinstance(gate, list) or len(gate) != 3:
            raise ValueError(f"wire {wire} needs a gate of the form [operation, left, right]")
        operation, left, right = gate
        if operation not in ("and", "or"):
            raise ValueError(f"wire {wire} has unknown operation {operation!r}")
        if any(type(i) is not int or not 0 <= i < wire for i in (left, right)):
            raise ValueError(f"wire {wire} needs two integer source wires from 0 through {wire - 1}")
    output = data.get("output")
    if type(output) is not int or not 0 <= output < INPUTS + len(gates):
        raise ValueError("output must be the index of an input or an existing gate")
    return gates, output


def first_mismatch(gates, output):
    point_assignments = 1 << POINTS
    all_points = (1 << point_assignments) - 1
    # In each integer, bit p is the value of this wire on point assignment p.
    points = [
        sum(1 << p for p in range(point_assignments) if p & (1 << point))
        for point in range(POINTS)
    ]
    neighbors = [0] * LINES
    for point, line in EDGES:
        neighbors[line - POINTS] |= points[point]

    for selection in range(1 << LINES):
        wires = points.copy()
        expected = 0
        for line, hits in enumerate(neighbors):
            active = selection & (1 << line)
            wires.append(all_points if active else 0)
            if active:
                expected |= hits
        for operation, left, right in gates:
            a, b = wires[left], wires[right]
            wires.append(a & b if operation == "and" else a | b)
        actual = wires[output]
        difference = actual ^ expected
        if difference:
            first_bit = difference & -difference
            p = first_bit.bit_length() - 1
            mask = (selection << POINTS) | p
            return mask, bool(expected & first_bit), bool(actual & first_bit)
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("candidate", nargs="?", type=Path, default=Path(__file__).with_name("Control54.json"))
    args = parser.parse_args()
    try:
        gates, output = load_circuit(args.candidate)
    except (OSError, ValueError) as error:
        parser.error(str(error))
    print(f"Gates: {len(gates)}")
    mismatch = first_mismatch(gates, output)
    if mismatch is None:
        print(f"Exact agreement on all {1 << INPUTS:,} assignments.")
        return 0
    mask, expected, actual = mismatch
    active = [v for v in range(INPUTS) if mask & (1 << v)]
    print(f"First mismatch at input {mask} (0x{mask:06x}), active vertices {active}.")
    print(f"Expected {int(expected)}, circuit returned {int(actual)}.")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
