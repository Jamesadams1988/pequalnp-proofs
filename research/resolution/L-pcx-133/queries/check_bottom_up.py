"""Bottom-up replay for arbitrary single-pigeon questions using sets of labels."""
from itertools import combinations, combinations_with_replacement


def main():
    domains = [tuple(s) for size in range(1, 5) for s in combinations(range(4), size)]
    states = sorted(combinations_with_replacement(sorted(domains), 5),
                    key=lambda state: sum(map(len, state)))
    costs = {}
    for state in states:
        singletons = [domain for domain in state if len(domain) == 1]
        if len(set(singletons)) < len(singletons):
            costs[state] = 1
            continue
        candidates = []
        for index, domain in enumerate(state):
            if index and state[index - 1] == domain:
                continue
            for size in range(1, len(domain)):
                for left in combinations(domain, size):
                    if domain[0] not in left:
                        continue
                    right = tuple(hole for hole in domain if hole not in left)
                    rest = state[:index] + state[index + 1:]
                    candidates.append(costs[tuple(sorted((*rest, left)))] +
                                      costs[tuple(sorted((*rest, right)))])
        costs[state] = min(candidates)

    root = ((0, 1, 2, 3),) * 5
    if costs[root] != 120:
        raise ValueError(costs[root])
    print(f"All {len(states)} product-domain states checked bottom-up; optimum 120 leaves.")


if __name__ == "__main__":
    main()
