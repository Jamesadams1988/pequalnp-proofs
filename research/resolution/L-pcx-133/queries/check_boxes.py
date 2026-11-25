"""Exact integer check for collision-labeled Cartesian partitions of five pigeons."""
from collections import Counter
from itertools import combinations, product


def weight(row):
    occupancies = sorted(Counter(row).values(), reverse=True)
    if occupancies == [2, 1, 1, 1]:
        return 4
    if occupancies == [2, 2, 1]:
        return -1
    return 0


def main():
    holes = range(4)
    distribution = Counter(weight(row) for row in product(holes, repeat=5))
    mass = sum(weight * count for weight, count in distribution.items())
    if distribution != {4: 240, -1: 360, 0: 424} or mass != 600:
        raise ValueError(distribution)

    # Two pigeons coincide at hole 0. Additional coordinates equal to 0 give
    # zero weight, leaving arbitrary subsets of the other three hole labels.
    others = (1, 2, 3)
    subsets = [s for k in range(4) for s in combinations(others, k)]
    caps = []
    for factors in product(subsets, repeat=3):
        caps.append(sum(weight((0, 0, *tail)) for tail in product(*factors)))
    if len(caps) != 512 or max(caps) != 6:
        raise ValueError("Unexpected normalized box maximum")
    print("Total weight 600 over 1024 assignments. Maximum box weight 6 over 512 boxes.")
    print("Every disjoint collision-labeled product partition has at least 100 boxes.")


if __name__ == "__main__":
    main()
