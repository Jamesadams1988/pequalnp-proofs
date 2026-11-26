"""Prepare the standalone 16-gate upper witness for the project's mathematical checker."""
import json
from pathlib import Path
import sys

here = Path(__file__).resolve().parent
dest = Path(sys.argv[1])
statement = json.loads((here.parent / 'sources/assignment.json').read_text())['statement']
prefix, suffix = '¬ (∀ t : ℕ, ', ' t → 16 ≤ t)'
if not statement.startswith(prefix) or not statement.endswith(suffix):
    raise ValueError('assigned statement is not the expected 16-gate lower-bound negation')
predicate = statement[len(prefix):-len(suffix)]
name = 'PEqualNP.Outside.ForkUpper11021'
proof = (here / 'Upper.lean').read_text()
for old in ('namespace CircuitTable11021', 'end CircuitTable11021'):
    if proof.count(old) != 1:
        raise ValueError('unexpected witness namespace')
    proof = proof.replace(old, old.replace('CircuitTable11021', name))
proof = proof.replace('#print axioms upper\n#print axioms depth_five\n', '')
ty = predicate + ' 16'
proof += f'\ntheorem {name} : {ty} := {name}.upper\n'
source = dest / 'source/PEqualNP/Outside/ForkUpper11021.lean'
source.parent.mkdir(parents=True, exist_ok=True)
source.write_text(proof)
(dest / 'upper.txt').write_text(ty + '\n')
(dest / 'control15.txt').write_text(predicate + ' 15\n')
