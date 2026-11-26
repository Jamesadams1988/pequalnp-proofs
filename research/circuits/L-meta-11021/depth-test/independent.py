"""Independent depth-four control, using bit sets indexed by functions for partner queries."""
from itertools import combinations_with_replacement
from pathlib import Path
import json
import re

# Recover the graph from the assigned statement rather than transcribing the graph.
statement = json.loads((Path(__file__).resolve().parents[1] / 'sources' / 'assignment.json').read_text())['statement']
edge_inputs = sorted((1 << int(a)) | (1 << int(b)) for a, b in re.findall(r'\(x (\d+) && x (\d+)\)', statement))
inputs = range(512)
positive = {x for x in inputs if any(x & e == e for e in edge_inputs)}
negative = set(inputs) - positive
maximal_false = sorted(x for x in negative if all((x | (1 << v)) not in negative
                      for v in range(9) if not x & (1 << v)))
all_inputs = (1 << 512) - 1
tables = {0, all_inputs}
for v in range(9):
    col = sum(1 << x for x in inputs if x & (1 << v))
    tables.update([col, all_inputs ^ col])
for d in (1, 2):
    for a, b in combinations_with_replacement(sorted(tables), 2):
        tables.add(a | b)
        tables.add(a & b)
tables = sorted(tables)
count = len(tables)
function_bits = (1 << count) - 1
# Each column enumerates functions true on one input. A whole partner shortlist
# is filtered with one machine-implemented Python big-integer operation.
columns = []
for x in inputs:
    by_function = bytearray((count + 7) // 8)
    bit = 1 << x
    for j, t in enumerate(tables):
        if bit & t:
            by_function[j // 8] |= 1 << (j % 8)
    columns.append(int.from_bytes(by_function, 'little'))

def coverage(target, forbidden):
    # Consider depth-three terms which must be false on every forbidden row.
    n = len(target)
    full = (1 << n) - 1
    forbidden_int = sum(1 << r for r in forbidden)
    reject = {1 << r: function_bits ^ columns[r] for r in forbidden}
    covers = [function_bits]  # all functions accepting every row of a subset
    for x in target:
        covers += [c & columns[x] for c in covers]
    target_bits = [1 << x for x in target]
    safe_at_two = set()
    partners_by_target = [0] * (1 << n)
    feasible = bytearray(1 << n)
    # Cache intersections for eight consecutive raw input indices. Signed
    # depth-two functions have many repeated local truth patterns.
    chunk_cache = [{} for _ in range(64)]
    for t in tables:
        mask = sum(1 << j for j, bit in enumerate(target_bits) if bit & t)
        forbidden_true = t & forbidden_int
        if not forbidden_true:
            safe_at_two.add(mask)
        if not mask:
            continue
        partners = function_bits
        while forbidden_true and partners:
            byte = ((forbidden_true & -forbidden_true).bit_length() - 1) // 8
            block = (forbidden_true >> (8 * byte)) & 255
            cache = chunk_cache[byte]
            if block not in cache:
                z = block << (8 * byte)
                allowed = function_bits
                while z:
                    bit = z & -z
                    allowed &= reject[bit]
                    z ^= bit
                cache[block] = allowed
            partners &= cache[block]
            forbidden_true ^= block << (8 * byte)
        partners_by_target[mask] |= partners
    # Combine every first child that accepts a required target subset, then
    # check that at least one admissible partner accepts that same subset.
    for j in range(n):
        step = 1 << j
        for base in range(0, 1 << n, 2 * step):
            for mask in range(base, base + step):
                partners_by_target[mask] |= partners_by_target[mask + step]
    for mask in range(1 << n):
        feasible[mask] = bool(covers[mask] & partners_by_target[mask])
    # For a depth-three OR, each child must already reject all forbidden rows.
    for a, b in combinations_with_replacement(safe_at_two, 2):
        sub = a | b
        top = sub
        while True:
            feasible[sub] = 1
            if sub == 0:
                break
            sub = (sub - 1) & top
    maximal = [m for m in range(1 << n) if feasible[m] and not any(
        feasible[m | (1 << j)] for j in range(n) if not m & (1 << j))]
    best = max((a | b).bit_count() for a,b in combinations_with_replacement(maximal, 2))
    return len(maximal), best

print(f'{len(positive)} true, {len(negative)} false, {len(edge_inputs)} minimal true, {len(maximal_false)} maximal false, {count} depth-two tables', flush=True)
print('OR root (all negatives forbidden):', coverage(edge_inputs, negative), flush=True)
# Complementing the full tree turns an AND-root solution for f into an OR-root
# solution for NOT f, with the same depth, since signed leaves are available.
print('AND root (all positives required):', coverage(maximal_false, positive), flush=True)
