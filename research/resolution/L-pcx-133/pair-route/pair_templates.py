"""Reproduce two local, syntax-checked Res(+) derivations for two-bit pigeons."""
import argparse
from itertools import combinations
import json
from pathlib import Path


class Derivation:
    def __init__(self):
        self.lines = []
        self.steps = []

    def add(self, clause, step):
        self.lines.append(frozenset(clause))
        self.steps.append(step)
        return self.lines[-1]

    def collision(self, i, j, hole):
        return self.add(
            [(1 << (2 * p + k), 1 - ((hole >> k) & 1)) for p in (i, j) for k in (0, 1)],
            {"rule": "ax", "p": i, "q": j, "hole": hole},
        )

    def weaken(self, parent, result):
        assert parent in self.lines
        result = frozenset(result)
        for point in range(1024):
            def holds(clause):
                return any((point & mask).bit_count() % 2 == bit for mask, bit in clause)
            assert not holds(parent) or holds(result)
        return self.add(result, {"rule": "weak", "parent": self.lines.index(parent), "clause": sorted(result)})

    def resolve(self, left, right, mask):
        assert left in self.lines and right in self.lines
        assert (mask, 0) in left and (mask, 1) in right
        return self.add(
            (left - {(mask, 0)}) | (right - {(mask, 1)}),
            {"rule": "res", "neg": self.lines.index(left), "pos": self.lines.index(right), "pivot": mask},
        )


def difference(i, j, bit):
    return (1 << (2 * i + bit)) ^ (1 << (2 * j + bit))


def pair(proof, i, j):
    delta = {(difference(i, j, bit), 1) for bit in (0, 1)}
    coordinates = [1 << (2 * i + bit) for bit in (0, 1)]
    points = []
    for hole in range(4):
        original = proof.collision(i, j, hole)
        signs = {(mask, 1 - ((hole >> k) & 1)) for k, mask in enumerate(coordinates)}
        points.append(proof.weaken(original, delta | signs))
    even = proof.resolve(points[1], points[0], coordinates[0])
    odd = proof.resolve(points[3], points[2], coordinates[0])
    result = proof.resolve(odd, even, coordinates[1])
    assert result == delta
    return result


def not_all_equal(proof, ab, bc, ac):
    # Derive "first bits are not all equal" from the three pair inequalities.
    a = difference(0, 1, 0)
    b = difference(0, 1, 1)
    c = difference(1, 2, 0)
    d = difference(1, 2, 1)
    rb = proof.weaken(ac, {(a, 1), (c, 1), (b, 0), (d, 0)})
    only_b = proof.resolve(rb, bc, d)
    result = proof.resolve(only_b, ab, b)
    assert result == {(a, 1), (c, 1)}
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--trace", type=Path)
    options = parser.parse_args()
    proof = Derivation()
    pairs = {ij: pair(proof, *ij) for ij in combinations(range(5), 2)}
    assert len(proof.lines) == len(set(proof.lines)) == 110
    print("All ten pair inequalities: 40 axioms, 40 weakenings, 30 resolutions.")
    not_all_equal(proof, pairs[0, 1], pairs[1, 2], pairs[0, 2])
    assert [step["rule"] for step in proof.steps[110:]] == ["weak", "res", "res"]
    print("Any three pairwise distinct pigeons must vary in either chosen bit: three additional lines for one bit.")
    if options.trace:
        options.trace.write_text(json.dumps(proof.steps, separators=(",", ":")) + "\n")
