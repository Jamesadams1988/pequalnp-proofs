"""Replay each two-phase proof and verify which derived occurrences are reused."""
from collections import Counter
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "formal"))
from verify_tree import inspect


def audit(k, expected):
    steps = json.loads((HERE / f"hall{k}.json").read_text())
    profile = inspect(steps)
    if (profile["lines"], profile["pigeon_axioms"], profile["hole_axioms"]) != (expected, 5, 40):
        raise ValueError(profile)
    # Independently recover the intermediate as signed literals, and inspect
    # the number of uses even when a derived literal set occurs in another line.
    target = {4 * p + h + 1 for p in range(k + 1) for h in range(k, 4)}
    clauses = []
    uses = Counter()
    for step in steps:
        if step["rule"] == "pigeon":
            clause = {4 * step["p"] + h + 1 for h in range(4)}
        elif step["rule"] == "hole":
            clause = {-(4 * step[p] + step["h"] + 1) for p in ("p", "q")}
        else:
            neg, pos = step["neg"], step["pos"]
            uses.update((neg, pos))
            pivot = step["pivot"] + 1
            clause = (clauses[neg] - {-pivot}) | (clauses[pos] - {pivot})
        clauses.append(clause)
    candidates = [i for i, clause in enumerate(clauses) if clause == target]
    if len(candidates) != 1:
        raise ValueError("expected one exact Hall occurrence")
    hall = candidates[0]
    for i, step in enumerate(steps[:-1]):
        if uses[i] == 0 or (step["rule"] == "res" and i != hall and uses[i] != 1):
            raise ValueError(f"unexpected reuse or unused line {i}")
    print(f"k={k}: {expected} lines, Hall clause at line {hall+1}, read {uses[hall]} times")


if __name__ == "__main__":
    for k, expected in enumerate((223, 223, 233), 1):
        audit(k, expected)
