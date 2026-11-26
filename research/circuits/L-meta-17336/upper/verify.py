"""Check the literal Lean gate lists on every assignment, independently of Lean."""
import json
import re
import sys
from pathlib import Path

root = Path(__file__).resolve().parent
source = (root / 'Witnesses.lean').read_text()
target, = re.findall(r'def target .*? :=\n  (.+)', source)
if len(sys.argv) == 2:
    assignment = json.loads(Path(sys.argv[1]).read_text())
    exact, = re.findall(r'\(fun x : Fin 9 → Bool => (.*?)\) → 16 ≤ C.size', assignment['statement'])
    assert assignment['id'] == 'L-meta-17336' and target == exact
edges = [(int(a), int(b)) for a, b in re.findall(r'\(x (\d+) && x (\d+)\)', target)]
assert len(edges) == 12 and len(set(edges)) == 12
expected = {'not5': 17}
for j in [6, 7, 8]:
    expected.update({f'and5_{j}': 17, f'or5_{j}': 16, f'or5_{j}Padded': 17})
circuits = re.findall(r'def (\w+) : Circuit :=\s*⟨\[(.*?)\], (\d+)⟩', source, re.S)
assert {name for name, *_ in circuits} == set(expected) and len(circuits) == len(expected)
for name, body, output in circuits:
    gates = [(op, list(map(int, args.split(', ')))) for op, args in re.findall(r'⟨\.(and|or|not), \[([\d, ]+)\]⟩', body)]
    assert len(gates) == expected[name] and body.count('⟨.') == len(gates)
    assert gates[0] == (('not', [5]) if name=='not5' else ('and' if name.startswith('and') else 'or', [5, int(name.split('_')[1][0])]))
    assert 0 <= int(output) < 9 + len(gates)
    for i, (op, args) in enumerate(gates):
        assert len(args) == (1 if op == 'not' else 2) and all(0 <= a < 9+i for a in args)
    mutation = 0
    for mask in range(512):
        wires = [bool(mask & 1<<i) for i in range(9)]
        first = (not wires[5]) if name=='not5' else (all if name.startswith('and') else any)(wires[i] for i in gates[0][1])
        truth = any(wires[a] and wires[b] for a,b in edges)
        short = any(wires[a] and wires[b] for a,b in edges[1:])
        for op,args in gates:
            wires.append(not wires[args[0]] if op=='not' else (all if op=='and' else any)(wires[a] for a in args))
        assert wires[9] == first and wires[int(output)] == truth, (name,mask)
        mutation += wires[int(output)] != short
    assert mutation > 0
    print(f'{name}: {len(gates)} gates, wire 9 and output agree on 512/512 inputs; deleting edge {edges[0]} breaks {mutation}.')
