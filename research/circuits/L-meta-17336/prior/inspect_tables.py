"""Read the prior candidate's fixed truth tables, independently of its Lean evaluator."""
from ast import literal_eval
from collections import Counter
from pathlib import Path
from hashlib import sha256
import re

root = Path(__file__).resolve().parent
source = (root / 'Prior17335.lean').read_bytes()
assert sha256(source).hexdigest() == '4defc64e8c1808d31eb16e4d092560256cadea0b1f32be2d604d9413002b10a2'
source = source.decode()


def literal(name):
    match = re.search(r'^def ' + name + r' : [^\n]*? := ([^\n]+)$', source, re.M)
    return literal_eval(match.group(1))


edges = [(0,4),(0,5),(1,5),(0,6),(2,6),(3,6),(1,7),(2,7),(4,7),(1,8),(3,8),(5,8)]
inputs = literal('rawP')
width = literal('NN')
active_positive = literal('AA')
extra = literal('FPM')
mask = active_positive | extra | (active_positive << width)
expected = literal('TG') & mask
rows = []
for bit in range(mask.bit_length()):
    if (mask >> bit) & 1:
        x = tuple((p >> bit) & 1 for p in inputs)
        value = any(x[i] and x[j] for i,j in edges)
        assert bool((expected >> bit) & 1) == value
        rows.append((x,value))
print('active bit positions', len(rows), 'distinct assignments', len(set(rows)),
      'distinct true/false', sorted(Counter(v for x,v in set(rows)).items()))
print('shared chart sizes', [len(literal(f'g{i}_0')) for i in (4,3,2,1)])
cases = literal('six')
assert cases == [(69,0),(37,6),(5,6),(37,7),(5,7),(37,8),(5,8)]
names = ['NOT 5','AND 5,6','OR 5,6','AND 5,7','OR 5,7','AND 5,8','OR 5,8']
for i, name in enumerate(names):
    private = len(re.findall(r'^theorem oku_c'+str(i)+r'_u\d+ ',source,re.M))
    batches = len(re.findall(r'^theorem hc'+str(i)+r'_\d+ ',source,re.M))
    # The final theorem IC_i has one and only one bridge for this first gate.
    assert source.count('exact icase_'+str(i)+' (D.size - 1)') == 1
    print(i, name, 'additional local inequalities', private, 'root batches', batches)
