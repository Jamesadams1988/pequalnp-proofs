"""Count leaves required by a parity decision tree on the unique-collision inputs.

A correct tree must output the colliding pair. Its internal queries may be any
parity of the ten bits. Restriction to critical inputs can collapse a query
with only one nonempty branch. We minimize a two-level lower bound over the
remaining (informative) queries at the root and separately in both children.
"""
from collections import Counter
from itertools import combinations, permutations


def collision_groups():
    groups = []
    for i, j in combinations(range(5), 2):
        points = []
        for assignment in permutations(range(4)):
            distinct = iter(assignment[1:])
            values = [assignment[0] if k in (i, j) else next(distinct) for k in range(5)]
            points.append(sum(value << (2 * k) for k, value in enumerate(values)))
        groups.append(points)
    return groups


def main():
    groups = collision_groups()
    points = [x for group in groups for x in group]
    assert len(set(points)) == len(points) == 240
    assert all(len(group) == 24 for group in groups)
    labels = [((1 << 24) - 1) << (24 * i) for i in range(len(groups))]
    full = (1 << len(points)) - 1
    masks = [
        sum(1 << i for i, x in enumerate(points) if (x & form).bit_count() % 2)
        for form in range(1, 1 << 10)
    ]

    def labels_present(sample):
        return sum(bool(label & sample) for label in labels)

    def child_bound(sample):
        # Each surviving label requires a different leaf. A non-monochrome
        # node must eventually split. Both sides may then require that label.
        if labels_present(sample) == 1:
            return 1
        return min(
            labels_present(left) + labels_present(sample ^ left)
            for mask in masks
            if (left := mask & sample) and left != sample
        )

    outcomes = Counter()
    for mask in masks:
        assert mask and mask != full
        outcomes[child_bound(full ^ mask) + child_bound(mask)] += 1
    print("Two-level leaf lower bounds, grouped by all 1023 root forms:", dict(sorted(outcomes.items())))
    assert sum(outcomes.values()) == 1023
    assert min(outcomes) == 19
    print("Every such tree needs at least 19 leaves and 18 binary resolutions.")
    print("Pair-normalization cost 110 plus tree tail cost at least 18 gives at least 128 lines.")


if __name__ == "__main__":
    main()
