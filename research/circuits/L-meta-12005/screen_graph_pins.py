"""Screen three literal encodings of simple edge functions in a public desk snapshot."""
import argparse
import json
import re
from collections import Counter, defaultdict
from pathlib import Path

CLAUSE = r"\(x (\d+) && x (\d+)\)"
PAIR = r"\((\d+), (\d+)\)"
FLAT = r"\(\[([\d, ]+)\] : List (?:ℕ|Nat)\)"
FLAT_FUNCTION = re.compile(
    r"decide \(∃ i < " + FLAT + r"\.length / 2, "
    + r"\(List.ofFn x\)\.getD \(\(\[\1\] : List (?:ℕ|Nat)\)\.getD \(2 \* i\) 0\) false = true ∧ "
    + r"\(List.ofFn x\)\.getD \(\(\[\1\] : List (?:ℕ|Nat)\)\.getD \(2 \* i \+ 1\) 0\) false = true\)"
)
DISJUNCTION = re.compile(
    r"\(fun x : Fin \d+ → Bool => (" + CLAUSE + r"(?: \|\| " + CLAUSE + r")*)\)"
)
PAIR_FUNCTION = re.compile(
    r"∃ u v : Fin (?P<dim>\d+), \(u.val, v.val\) ∈ \(\[(?P<edges>" + PAIR + r"(?:, " + PAIR
    + r")*)\] : List \(ℕ × ℕ\)\) ∧ x u = true ∧ x v = true"
)


def parse(statement):
    dims = set(re.findall(r"x : Fin (\d+) → Bool", statement))
    if len(dims) != 1:
        return
    n = int(dims.pop())
    parsed = []
    flat_matches = list(FLAT_FUNCTION.finditer(statement))
    if len(re.findall(FLAT, statement)) != 3 * len(flat_matches):
        return
    for match in flat_matches:
        values = [int(a) for a in match[1].split(",")]
        if len(values) % 2:
            return
        parsed.append(("flat", zip(values[::2], values[1::2])))

    disjunctions = list(DISJUNCTION.finditer(statement))
    disj_pairs = [re.findall(CLAUSE, m[1]) for m in disjunctions]
    if sum(map(len, disj_pairs)) != len(re.findall(CLAUSE, statement)):
        return
    parsed.extend(("disjunction", pairs) for pairs in disj_pairs)

    pair_lists = list(PAIR_FUNCTION.finditer(statement))
    if any(int(m["dim"]) != n for m in pair_lists):
        return
    list_pairs = [re.findall(PAIR, m["edges"]) for m in pair_lists]
    if sum(map(len, list_pairs)) != len(re.findall(PAIR, statement)):
        return
    parsed.extend(("pairs", pairs) for pairs in list_pairs)

    graphs = set()
    for kind, pairs in parsed:
        edges = tuple(sorted({tuple(sorted(map(int, pair))) for pair in pairs}))
        if any(not (0 <= a < b < n) for a, b in edges):
            return
        graphs.add((kind, (n, edges)))
    if len(graphs) == 1:
        return graphs.pop()


def witnesses(n, edges):
    adj = [set() for _ in range(n)]
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    hits = []
    for p, neighbors in enumerate(adj):
        if len(neighbors) == 1:
            q, = neighbors
            if len(adj[q]) >= 2 and any(q not in edge and p not in edge for edge in edges):
                hits.append((p, q, False))
        if neighbors:
            hits.extend((p, q, True) for q in range(n) if neighbors < adj[q])
    return hits


def summarize(groups):
    graph_shapes, row_shapes = Counter(), Counter()
    pairings = Counter()
    for graph, rows in groups.items():
        pins = {v for _, _, v in witnesses(*graph)}
        shape = {(False,): "false_only", (True,): "true_only", (False, True): "both", (): "neither"}[tuple(sorted(pins))]
        graph_shapes[shape] += 1
        row_shapes[shape] += len(rows)
        if pins:
            negated = sum(r['statement'].lstrip().startswith('¬') for r in rows)
            pairings[f"{len(rows) - negated} positive, {negated} negated"] += 1
    return {"rows": sum(map(len, groups.values())), "graphs": len(groups),
            "graph_shapes": dict(graph_shapes), "row_shapes": dict(row_shapes),
            "hit_graph_polarity_counts": dict(pairings)}


def run(path, show_hits):
    data = json.loads(path.read_text())
    by_graph = defaultdict(list)
    kinds = Counter()
    for row in data["gaps"]:
        result = parse(row["statement"])
        if result:
            kind, graph = result
            kinds[kind] += 1
            by_graph[graph].append(row)
    by_clean_row = {g: [r for r in rows if not r.get('pr_open') and not r.get('reserved')]
                    for g, rows in by_graph.items()}
    clean = {g: rs for g, rs in by_clean_row.items() if rs}
    wholly_clean = {g: rs for g, rs in by_graph.items() if len(rs) == len(by_clean_row[g])}
    print(json.dumps({"updated_at": data["updated_at"], "encodings": kinds,
                      "unscreened_rows": len(data["gaps"]) - sum(kinds.values()), "all": summarize(by_graph),
                      "any_pr_free_unreserved_row": summarize(clean),
                      "every_row_pr_free_unreserved": summarize(wholly_clean)}, indent=2))
    if show_hits:
        for graph, rows in clean.items():
            hits = witnesses(*graph)
            if hits:
                print(graph[0], ",".join(r["id"] for r in rows), hits)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("snapshot", type=Path)
    parser.add_argument("--show-hits", action="store_true")
    args = parser.parse_args()
    run(args.snapshot, args.show_hits)
