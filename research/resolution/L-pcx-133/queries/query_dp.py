"""Exact minimum leaf count for local queries in the bit pigeonhole search problem."""
from functools import cache

# A four-bit mask is the set of hole labels still available to one pigeon.
# Complementary queries define the same split. Each representative contains 0.
MODELS = {
    "raw_bits": (0b0011, 0b0101),
    "local_parity": (0b0011, 0b0101, 0b1001),
    "all_local_questions": (1, 3, 5, 7, 9, 11, 13),
}

def terminal(state):
    singles = [mask for mask in state if mask.bit_count() == 1]
    return len(singles) != len(set(singles))

def branches(state, questions):
    for index, mask in enumerate(state):
        if index and state[index - 1] == mask:
            continue
        other = state[:index] + state[index + 1:]
        for question in questions:
            yes, no = mask & question, mask & (15 ^ question)
            if yes and no:
                yield tuple(sorted((*other, yes))), tuple(sorted((*other, no)))

def solve(questions):
    costs = {}
    choices = {}
    @cache
    def visit(state):
        if terminal(state):
            result = 1
        else:
            options = [(visit(a) + visit(b), a, b) for a, b in branches(state, questions)]
            if not options:
                raise ValueError("A live state had no informative query")
            result, left, right = min(options)
            choices[state] = left, right
        costs[state] = result
        return result
    root = (15,) * 5
    total = visit(root)
    # Check the Bellman equations on every reachable state.
    for state, value in costs.items():
        if terminal(state):
            assert value == 1
        else:
            assert value == min(costs[a] + costs[b] for a, b in branches(state, questions))
    return total, costs, choices

if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Use Python without -O to enable the checks.")
    for name, questions in MODELS.items():
        total, states, _ = solve(questions)
        print(f"{name}: {total} leaves, {2*total-1} tree nodes, {len(states)} domain states")
