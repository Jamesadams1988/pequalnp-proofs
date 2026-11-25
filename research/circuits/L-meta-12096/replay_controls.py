"""Exercise exact positive and negative controls and audit the assigned sample count."""
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
TARGET = 0xfe80fe00fe00e800

def run(k, mono, table, expected):
    report = subprocess.check_output([HERE/'signed', str(k), str(mono), hex(table)], text=True)
    first = report.splitlines()[0]
    assert f'fits={expected} ' in first, first
    print(first)

def table(fn):
    return sum(fn(*[(r >> i) & 1 for i in range(6)]) << r for r in range(64))

def witness(k, mono, f):
    run(k-1,mono,f,0); run(k,mono,f,1)

conjunction = table(lambda a,b,c,d,e,f: a & b & c & d & e & f)
mixed = table(lambda a,b,c,d,e,f: (a & (1 ^ b)) & c & d & e & f)
earlier = 0xeaa8c080ea88c080
run(0,0,conjunction,0)
witness(5,0,conjunction)
witness(5,1,conjunction)
witness(5,0,mixed)
run(5,1,mixed,0)
witness(8,0,earlier)
witness(8,1,earlier)

ones = [x for x in range(64) if TARGET>>x&1]
zeros = [x for x in range(64) if not (TARGET>>x&1)]
mins = [x for x in ones if all(y==x or y&x!=y for y in ones)]
maxs = [x for x in zeros if all(y==x or y&x!=x for y in zeros)]
pairs = {(z,o) for z in maxs for o in mins} | {(z,o) for z in zeros for o in ones if (z^o).bit_count()==1}
assert len(pairs)==123
print(f'{len(mins)} minimal positives, {len(maxs)} maximal negatives, {len(pairs)} distinct sample pairs')
