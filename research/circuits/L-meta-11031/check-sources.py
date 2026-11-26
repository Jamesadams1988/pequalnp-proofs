"""Verify the published upstream proof hashes and the input types of the assembly."""
import hashlib
import json
from pathlib import Path
import re
import sys

package = Path(__file__).resolve().parent
project = Path(sys.argv[1]).resolve()
manifest = json.loads((package / 'sources/dependencies.json').read_text())
assigned = json.loads((package / 'sources/assignment.json').read_text())['statement']
cases = [17303, 17305, 17307, 17313, 17315, 17317, 17319, 17321, 17323]


def theorem_type(source, number):
    marker = f'theorem PEqualNP.Outside.L_meta_{number} :'
    declarations = re.split('^' + re.escape(marker), source, flags=re.MULTILINE)
    if len(declarations) != 2:
        raise ValueError(f'expected one public theorem in L-meta-{number}')
    signature = declarations[1]
    depth = 0
    for pos, ch in enumerate(signature):
        if depth == 0 and signature.startswith(':=', pos):
            return signature[:pos].strip()
        depth += int(ch in '([{') - int(ch in ')]}')
    raise ValueError(f'missing declaration body for L-meta-{number}')


types = {}
receipts = json.loads((package / 'sources/intake.json').read_text())
for record in manifest['dependencies']:
    number = int(record['row'].split('-')[-1])
    raw = (project.parent / record['file']).read_bytes()
    receipt, = [r for r in receipts if r['row'] == record['row']]
    if hashlib.sha256(raw).hexdigest() != record['sha256']:
        raise ValueError(f"source hash mismatch for {record['row']}")
    if (receipt['merged_pr'], receipt['author'], receipt['merged_at']) != (record['pr_url'], record['author'], record['merged_at']):
        raise ValueError(f"intake and merge records differ for {record['row']}")
    if not record['public_desk_hash_match'] or not record['pr_blob_matches_current_pin'] or not record['merged_at']:
        raise ValueError(f"incomplete checked-source record for {record['row']}")
    types[number] = theorem_type(raw.decode(), number)

assert set(types) == {534, 17110, *cases}
assert assigned.startswith('¬ (') and assigned.endswith(')')
assert types[17110].endswith(' → ' + assigned[3:-1])
audit = (package / 'CaseAudit.lean').read_text()
consumer = (package / 'Exact.lean').read_text()
for pivot, number in enumerate(cases):
    assert f'(h{number} : {types[number]})' in audit
    assert re.findall(r'false = !\(y (\d+)\)', types[number]) == [str(pivot)]
    assert f'import PEqualNP.Outside.L_meta_{number}\n' in consumer
uses = '\n    '.join(f'PEqualNP.Outside.L_meta_{n}' for n in cases)
assert 'assemble\n    ' + uses + '\n' in consumer
assert f'¬ ({assigned})' in consumer and f'¬ ({assigned})' in audit
print('Matched eleven upstream checked-source digests, nine ordered first-gate cases and the exact target.')
