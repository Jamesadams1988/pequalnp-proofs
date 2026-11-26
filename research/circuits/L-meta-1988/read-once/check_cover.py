"""Verify the supplied 96-factor cover directly from its component formulas."""
from pathlib import Path

SIDE = (1 << 13) - 1
UNIVERSE = (1 << 26) - 1
EDGES = [(1 << p) | (1 << (13 + line)) for p in range(13) for line in range(13)
         if (p + line) % 13 in {0, 1, 3, 9}]
NEIGHBORS = [sum(edge ^ (1 << v) for edge in EDGES if edge >> v & 1) for v in range(26)]


def canonical_terms(singletons):
    """Each (point mask, line mask) term contributes a single product."""
    remaining = UNIVERSE ^ singletons
    terms = []
    while remaining:
        frontier = remaining & -remaining
        part = 0
        while frontier:
            bit = frontier & -frontier
            frontier ^= bit
            part |= bit
            frontier |= NEIGHBORS[bit.bit_length() - 1] & remaining & ~part
        remaining &= ~part
        if part & SIDE and part >> 13:
            terms.append((part & SIDE, part & ~SIDE))
    return terms


def accepts(singletons, terms, assignment):
    return bool(singletons & assignment or any(
        (points & assignment) and (lines & assignment) for points, lines in terms))


def main():
    masks = [int(row) for row in Path(__file__).with_name("cover96.txt").read_text().splitlines()]
    if len(set(masks)) != len(masks) or len(masks) != 96:
        raise ValueError("expected 96 distinct factors")
    factors = [(mask, canonical_terms(mask)) for mask in masks]
    for mask, terms in factors:
        if not all(accepts(mask, terms, edge) for edge in EDGES):
            raise ValueError(f"factor {mask} misses an edge")
    cuts = []
    for points in range(SIDE + 1):
        lines = sum(1 << v for v in range(13, 26) if not NEIGHBORS[v] & points)
        if all(points >> p & 1 or NEIGHBORS[p] & lines for p in range(13)):
            cuts.append(points | lines)
    if len(cuts) != 704:
        raise ValueError("unexpected maximal independent set count")
    for cut in cuts:
        if all(accepts(mask, terms, cut) for mask, terms in factors):
            raise ValueError(f"cover accepts maximal independent assignment {cut}")
    print("Verified 96 canonical factors on all 52 edges and all 704 maximal negatives.")


if __name__ == "__main__":
    main()
