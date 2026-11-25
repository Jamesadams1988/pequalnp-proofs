"""Replay ordinary resolution on BPHP(5,2) and profile the final proof DAG."""

import argparse
from collections import Counter
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def verify(path):
    steps = json.loads(path.read_text())
    clauses = []
    parents = []
    tree_leaves = []
    depths = []
    usages = Counter()
    axioms = set()
    require(steps, "empty trace")

    for index, step in enumerate(steps):
        if step["rule"] == "ax":
            p, q, hole = step["p"], step["q"], step["hole"]
            require(0 <= p < 5 and 0 <= q < 5 and p != q and 0 <= hole < 4,
                    f"invalid collision axiom at line {index}")
            axioms.add((min(p, q), max(p, q), hole))
            clause = frozenset((2 * pigeon + bit, 1 - ((hole >> bit) & 1))
                               for pigeon in (p, q) for bit in (0, 1))
            parents.append(())
            tree_leaves.append(1)
            depths.append(0)
        else:
            require(step["rule"] == "res", f"unsupported rule at line {index}")
            a, b, mask = step["neg"], step["pos"], step["pivot"]
            require(0 <= a < index and 0 <= b < index, f"invalid parents at line {index}")
            require(0 < mask < 1 << 10 and mask.bit_count() == 1,
                    f"expected single-variable pivot at line {index}")
            variable = mask.bit_length() - 1
            negative, positive = (variable, 0), (variable, 1)
            require(negative in clauses[a] and positive in clauses[b],
                    f"missing pivot literal at line {index}")
            clause = (clauses[a] - {negative}) | (clauses[b] - {positive})
            parents.append((a, b))
            usages.update((a, b))
            tree_leaves.append(tree_leaves[a] + tree_leaves[b])
            depths.append(1 + max(depths[a], depths[b]))
        clauses.append(clause)

    require(not clauses[-1], "last line does not derive the empty clause")
    require(len(axioms) == 40, "missing collision axiom")
    live = {len(steps) - 1}
    for index in reversed(range(len(steps))):
        if index in live:
            live.update(parents[index])
    distinct = len(set(clauses))
    require(len(live) == len(steps), "proof contains unused lines")
    require(distinct == len(steps), "proof contains duplicate clauses")
    widths = Counter(map(len, clauses))
    return {
        "lines": len(steps),
        "axioms": len(axioms),
        "resolutions": len(steps) - len(axioms),
        "distinct_clauses": distinct,
        "live_ancestors_including_final": len(live),
        "unfolded_leaf_occurrences": tree_leaves[-1],
        "maximum_resolution_depth": depths[-1],
        "maximum_width": max(widths),
        "clauses_by_width": dict(sorted(widths.items())),
        "lines_used_multiple_times": sum(count > 1 for count in usages.values()),
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("trace", type=Path)
    args = parser.parse_args()
    print(json.dumps(verify(args.trace), indent=2))
