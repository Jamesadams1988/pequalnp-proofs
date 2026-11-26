"""Maximum number of flexible pivots under uniform neighbor witnesses."""
N = 13
FULL = (1 << N) - 1
NEIGHBORS = [
    sum(1 << line for line in range(N) if (point + line) % N in {0, 1, 3, 9})
    for point in range(N)
]


def subsets(mask):
    current = mask
    while True:
        yield current
        if not current:
            return
        current = (current - 1) & mask


def main():
    neighbor_union = [0] * (FULL + 1)
    admits_order = [False] * (FULL + 1)
    admits_order[0] = True
    for mask in range(1, FULL + 1):
        bit = mask & -mask
        neighbor_union[mask] = neighbor_union[mask ^ bit] | NEIGHBORS[bit.bit_length() - 1]
        for vertex, neighbors in enumerate(NEIGHBORS):
            bit = 1 << vertex
            if mask & bit and admits_order[mask ^ bit] and neighbors & ~neighbor_union[mask ^ bit]:
                admits_order[mask] = True
                break

    best = 0
    terminal_edges = 0
    for line in range(N):
        for point in range(N):
            if not NEIGHBORS[point] & (1 << line):
                continue
            terminal_edges += 1
            for left in subsets(FULL ^ NEIGHBORS[line]):
                if admits_order[left]:
                    allowed = FULL & ~NEIGHBORS[point] & ~neighbor_union[left]
                    for right in subsets(allowed):
                        if admits_order[right]:
                            best = max(best, left.bit_count() + right.bit_count())
    assert (terminal_edges, best) == (52, 6)
    print(f"Examined {terminal_edges} terminal edges. Maximum flexible pivots: {best}.")


if __name__ == "__main__":
    main()
