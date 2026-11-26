"""Reconstruct the full graph group and its first-gate orbits for L-meta-9742."""

import argparse
import json
import re
from itertools import combinations, permutations
from pathlib import Path


POINTS = tuple(range(13))
LINES = tuple(range(13, 26))
VERTICES = POINTS + LINES


def require(condition, message):
    if not condition:
        raise ValueError(message)


def pair(a, b):
    return (a, b) if a < b else (b, a)


def parse_edges(assignment):
    require(assignment["id"] == "L-meta-9742", "unexpected assignment id")
    edge_list = re.search(r"\(\[(.*?)\]\s*:\s*List", assignment["statement"], re.S)
    require(edge_list is not None, "missing Lean edge list")
    raw = json.loads("[" + edge_list[1].replace("(", "[").replace(")", "]") + "]")
    edges = {tuple(edge) for edge in raw}
    require(len(raw) == len(edges) == 51, "expected 51 distinct edges")
    require(all(a in POINTS and b in LINES for a, b in edges), "wrong bipartition")
    return edges


def adjacency(edges):
    neighbors = {v: set() for v in VERTICES}
    for a, b in edges:
        neighbors[a].add(b)
        neighbors[b].add(a)
    return neighbors


def plane_constructions(neighbors):
    common = {}
    for side in (POINTS, LINES):
        for a, b in combinations(side, 2):
            intersection = neighbors[a] & neighbors[b]
            require(len(intersection) == 1, "join or meet is not unique")
            common[a, b] = next(iter(intersection))
    return common


def closure_program(seed, common):
    """Record enough uniquely determined joins and meets to recover every label."""
    known = set(seed)
    steps = []
    while len(known) < len(VERTICES):
        previous = len(known)
        for (a, b), v in common.items():
            if a in known and b in known and v not in known:
                steps.append((a, b, v))
                known.add(v)
        require(len(known) > previous, "chosen frame does not generate the plane")
    return steps


def preserves_edges(mapping, edges):
    return {pair(mapping[a], mapping[b]) for a, b in edges} == edges


def enumerate_group(edges):
    neighbors = adjacency(edges)
    require({v for v in VERTICES if len(neighbors[v]) == 3} == {0, 13},
            "expected two degree-three vertices")
    reached = {0}
    while True:
        expanded = reached.union(*(neighbors[v] for v in reached))
        if expanded == reached:
            break
        reached = expanded
    require(reached == set(VERTICES), "graph must be connected")
    require((0, 13) not in edges, "deleted flag already present")
    full = adjacency(edges | {(0, 13)})
    require(all(len(n) == 4 for n in full.values()), "unexpected completed degrees")
    common = plane_constructions(full)

    # The first two seed points lie on line 13. Pick two more with no collinear triple.
    a = 0
    b = min(full[13] - {a})
    c = min(set(POINTS) - full[13])
    side_lines = (13, common[pair(a, c)], common[pair(b, c)])
    d = min(set(POINTS) - set.union(*(full[line] for line in side_lines)))
    seed = (a, b, c, d)
    steps = closure_program(seed, common)
    preserving = set()
    for images in permutations(POINTS[1:], 3):
        if images[0] not in full[13]:
            continue
        mapped = dict(zip(seed, (0,) + images))
        for u, v, w in steps:
            source = pair(mapped[u], mapped[v])
            if source not in common:
                break
            mapped[w] = common[source]
        else:
            candidate = tuple(mapped[v] for v in VERTICES)
            if len(set(candidate)) == 26 and preserves_edges(candidate, edges):
                preserving.add(candidate)

    dual = tuple(13 + (-v) % 13 if v in POINTS else (13 - v) % 13 for v in VERTICES)
    require(preserves_edges(dual, edges), "duality failed")
    reversing = {tuple(dual[v] for v in g) for g in preserving}
    group = preserving | reversing
    require(len(preserving) == 108 and len(group) == 216, "unexpected group size")
    require(VERTICES in group, "missing identity")
    for g in group:
        require(set(g) == set(VERTICES) and preserves_edges(g, edges), "bad group element")
        require(all(tuple(g[v] for v in h) in group for h in group), "closure failed")
    return group, seed, steps


def orbit_report(assignment):
    edges = parse_edges(assignment)
    group, seed, steps = enumerate_group(edges)
    unseen = set(combinations(VERTICES, 2))
    orbits = []
    while unseen:
        a, b = min(unseen)
        orbit = {pair(g[a], g[b]) for g in group}
        require((a, b) in orbit and orbit <= unseen, "orbits overlap")
        require(all((p in edges) == ((a, b) in edges) for p in orbit),
                "orbit mixes edges and nonedges")
        require(sum(pair(g[a], g[b]) == (a, b) for g in group) * len(orbit) == len(group),
                "orbit-stabilizer check failed")
        unseen -= orbit
        orbits.append({"representative": (a, b), "size": len(orbit),
                       "edge": (a, b) in edges, "members": sorted(orbit)})
    require(sum(o["size"] for o in orbits) == 325, "pair coverage failed")
    require(sum(o["size"] for o in orbits if o["edge"]) == 51, "edge coverage failed")
    return {
        "id": assignment["id"],
        "deleted_flag": (0, 13),
        "frame": seed,
        "frame_joins_and_meets": steps,
        "part_preserving_group_order": 108,
        "full_group_order": len(group),
        "distinct_unordered_input_pairs": 325,
        "pair_orbit_count": len(orbits),
        "labeled_first_gate_cases": 2 * len(orbits),
        "gate_labels": ["AND", "OR"],
        "pair_orbits": orbits,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("assignment", nargs="?", type=Path,
                        default=Path(__file__).resolve().parents[1] / "assignment.json")
    args = parser.parse_args()
    with args.assignment.open(encoding="utf-8") as file:
        report = orbit_report(json.load(file))
    print(json.dumps(report, separators=(",", ":")))
