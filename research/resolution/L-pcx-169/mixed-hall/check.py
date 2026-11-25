"""Check the line ownership and matching counts for the ordinary 5 into 4 Hall template."""
from collections import Counter, defaultdict
from itertools import combinations, permutations
from math import comb

P = frozenset(range(5))
H = frozenset(range(4))
DUMMY = 4


def subsets(s, k=None):
    for size in (range(len(s) + 1) if k is None else [k]):
        yield from map(frozenset, combinations(sorted(s), size))


def pos(rows, holes):
    return frozenset(4 * p + h + 1 for p in rows for h in holes)


def resolve(negative, positive, pivot):
    assert -pivot in negative and pivot in positive
    return frozenset(negative - {-pivot}) | (positive - {pivot})


def candidates(s, t):
    """Check all order-independent subset transitions and yield their actual clauses."""
    u = H - t

    # In a conditional clause, old rows from which column h still needs elimination.
    def condition(r, h, rest):
        clause = pos(s-{r}, u) | pos(rest, {h})
        return clause if rest == s-{r} else clause | {-(4*r+h+1)}

    for r in s:
        for h in t:
            for rest in subsets(s - {r}):
                before = condition(r, h, rest)
                for i in rest:
                    pivot = 4*i+h+1
                    collision = {-(4*r+h+1), -pivot}
                    result = resolve(collision, before, pivot)
                    assert result == condition(r, h, rest-{i})
                    yield result

        # Row orientation starts at the full positive pigeon axiom for r.
        for done in subsets(t):
            before = pos(s,u) | pos({r},t-done) if done else pos({r},H)
            for h in t-done:
                result = resolve(condition(r,h,set()), before, 4*r+h+1)
                assert result == pos(s,u) | pos({r},t-done-{h})
                yield result

    for h in t:
        for anchor in s:
            # Column orientation starts at the child missing the anchor pigeon.
            domain = s - {anchor}
            for rest in subsets(domain):
                before = (pos(domain,u|{h}) if rest == domain
                          else pos(s,u) | pos(rest,{h}))
                for r in rest:
                    result = resolve(condition(r,h,set()), before, 4*r+h+1)
                    assert result == pos(s,u) | pos(rest-{r},{h})
                    yield result


def verify():
    all_phi = list(permutations(range(5)))
    owners = {}
    counts = Counter()
    ax = {pos({p}, H) for p in P}
    ax |= {frozenset({-(4*p+h+1),-(4*q+h+1)}) for p,q in combinations(P,2) for h in H}
    for k in range(1,5):
        for s in subsets(P, k+1):
            for t in subsets(H, k):
                node = (s,t)
                matching = [phi for phi in all_phi if {phi[p] for p in s} == t | {DUMMY}]
                assert len(matching) * comb(5,k+1) == len(all_phi)
                for r in s:
                    assert sum(phi[r] in t for phi in matching) * (k+1) == k * len(matching)
                for h in t:
                    assert all(phi.index(h) in s for phi in matching)
                for c in set(candidates(s,t)):
                    assert c not in ax, (node,c)
                    assert c not in owners, (owners.get(c),node,c)
                    owners[c] = node
                    counts[k] += 1
    level_nodes = [comb(4,k) for k in range(1,5)]
    charged = sum(count*k*(k+1) for k,count in enumerate(level_nodes, start=1))
    assert len(ax) == 45 and charged == 112
    print('120 bijections and each candidate pivot checked')
    print('distinct available internal clauses by level:', dict(sorted(counts.items())))
    print('minimum rectangle counts at levels 1 through 4:', *level_nodes)
    print(f'{len(ax)} axioms + {charged} distinct resolution lines = {len(ax)+charged}')

if __name__ == '__main__':
    verify()
