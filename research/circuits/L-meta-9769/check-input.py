"""Compare the graph inputs, finite witnesses, and Lean endpoints with the desk text."""
import json
import re
from pathlib import Path

here = Path(__file__).resolve().parent
statement = json.loads((here / "statement.json").read_text())["statement"]
pattern = r"\(x (\d+) && x (\d+)\)"
literal = [tuple(map(int, pair)) for pair in re.findall(pattern, statement)]
graph = [tuple(map(int, line.split())) for line in (here / "formula/edges.txt").read_text().splitlines()]
assert literal == [(p, l + 21) for p, l in graph]
assert len(graph) == len(set(graph)) == 104
full = {(p, (p + offset) % 21) for p in range(21) for offset in (0, 5, 7, 17, 20)}
assert full - set(graph) == {(0, 0)} and not set(graph) - full
positive = statement.removeprefix("¬ (").removesuffix(")")
assert positive.endswith(" 123")
upper = (here / "upper/Literal124.lean").read_text()
# Whitespace may differ across a theorem's declaration.
normalize = lambda value: " ".join(value.split())
assert normalize(positive[:-4] + " 124") in normalize(upper)
lower = (here / "lower/Lower.lean").read_text()
literal_function = positive.removeprefix("PEqualNP.MetaComplexity.HasCircuitSize 42 ").removesuffix(" 123")
assert normalize(literal_function) in normalize(lower)
assert normalize(literal_function) in normalize((here / "lower/Terminal51.lean").read_text())

result = (here / "formula/result.txt").read_text().splitlines()
for line in result[:-1]:
    p, l, rows, cols = map(int, line.split())
    assert rows.bit_count() == p and cols.bit_count() == l
    selected = [(a, b) for a, b in graph if rows >> a & 1 and cols >> b & 1]
    rdeg = [sum(a == i for a, _ in selected) for i in range(21)]
    cdeg = [sum(b == j for _, b in selected) for j in range(21)]
    assert all(rdeg[a] == 1 or cdeg[b] == 1 for a, b in selected)
assert max(sum(map(int, line.split()[:2])) for line in result[:-1]) == 25
print("Literal 104 edges, both Lean endpoints and all 22 star-forest witnesses agree.")
