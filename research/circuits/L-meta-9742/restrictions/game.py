"""Check the monotone circuit lower bound by enumerating all possible first gates."""
import argparse
from collections import Counter
from functools import cache
from itertools import combinations
import json
from pathlib import Path
import re

def vertices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit

def graph_data(assignment):
    edges = json.loads(Path(__file__).with_name("edges.json").read_text())
    if assignment:
        text = json.loads(assignment.read_text())["statement"]
        original = [[int(i), int(j)] for i, j in re.findall(r'\((\d+), (\d+)\)', text)]
        assert original == edges
    adj = [0] * 26
    assert len(edges) == 51 and len(set(map(tuple, edges))) == 51
    for i, j in edges:
        assert 0 <= i < 13 <= j < 26
        adj[i] |= 1 << j
        adj[j] |= 1 << i
    assert all((adj[i] & adj[j]).bit_count() <= 1 for i,j in combinations(range(26),2))
    return adj

def run(adj, rounds):
    universe = (1 << 26) - 1
    def active(mask):
        return sum(1 << i for i in vertices(mask) if adj[i] & mask)

    @cache
    def terminal(mask):
        if not mask:
            return 0
        assert active(mask) == mask
        heavy = sum(1 << i for i in vertices(mask) if (adj[i] & mask).bit_count() >= 2)
        for i,j in combinations(vertices(heavy), 2):
            if adj[i] >> j & 1:
                alternatives_i = adj[i] & mask & ~(1 << j)
                alternatives_j = adj[j] & mask & ~(1 << i)
                assert any(alternatives_j & ~adj[k] for k in vertices(alternatives_i))
            else:
                assert adj[i] & mask != adj[j] & mask
        match = {}
        def augment(i, seen):
            for j in vertices(adj[i] & heavy):
                if j in seen:
                    continue
                seen.add(j)
                if j not in match or augment(match[j], seen):
                    match[j] = i
                    return True
            return False
        for i in vertices(heavy & ((1 << 13) - 1)):
            augment(i,set())
        assert len(match) == len(set(match.values()))
        assert all(heavy >> i & heavy >> j & 1 and adj[i] >> j & 1 for j,i in match.items())
        return mask.bit_count() + len(match) - 1

    @cache
    def search(mask, depth):
        bound = terminal(mask)
        if depth == 0 or mask.bit_count() <= 2:
            return bound
        indices = list(vertices(mask))
        low, high = {}, {}
        for i in indices:
            remaining = mask ^ (1 << i)
            neighbors = adj[i] & mask
            low[i] = search(active(remaining), depth - 1)
            rest = active(remaining & ~neighbors)
            high[i] = neighbors.bit_count() + (search(rest, depth - 1) if rest else -1)
        bound = max(bound, max(low.values()) + 1, max(high.values()) + 1)
        scores = Counter()
        for i,j in combinations(indices, 2):
            edge = bool(adj[i] >> j & 1)
            for op in ("AND", "OR"):
                if op == "AND" and not edge:
                    continue
                if op == "OR" and (adj[i] & mask == 1 << j or adj[j] & mask == 1 << i):
                    continue
                best = 0
                for x,y in ((i,j),(j,i)):
                    if op == "AND":
                        reused = bool(adj[x] & mask & ~(1 << y))
                        absorbing, neutral = low[x], high[x]
                    else:
                        reused = bool(edge or adj[x] & mask & ~adj[y])
                        absorbing, neutral = high[x], low[x]
                    best = max(best, absorbing + 2 + reused, neutral + 1 + reused)
                    if reused and low[x] > 0:
                        opposite = max(absorbing + 3, neutral + 3)
                        same = max(absorbing + 4, neutral + 2)
                        best = max(best, min(opposite, same))
                scores[op, best] += 1
        if mask == universe:
            print("First-gate cases", sorted(scores.items()))
        assert scores
        return max(bound, min(score for op,score in scores))

    for d in range(rounds+1):
        score = search(universe, d)
        print(f"Round {d}: lower bound {score}; {terminal.cache_info().currsize} terminal masks", flush=True)
        if d == 3:
            assert score >= 39
        if d == 5:
            assert score >= 40

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--assignment", type=Path)
    parser.add_argument("--rounds", type=int, default=5)
    args = parser.parse_args()
    if args.rounds < 0:
        parser.error("rounds must be nonnegative")
    run(graph_data(args.assignment), args.rounds)
