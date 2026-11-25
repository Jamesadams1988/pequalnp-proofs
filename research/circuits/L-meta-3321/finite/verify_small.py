"""Find minimum clean circuits for all C4-free incidence masks through size three."""
import argparse
import itertools
import json
import subprocess
from collections import Counter
from pathlib import Path
from time import monotonic


def classes(n):
    permutations = list(itertools.permutations(range(n)))
    counts = Counter()
    for table in range(1 << (n*n)):
        rows = [(table >> (i*n)) & ((1<<n)-1) for i in range(n)]
        if any((r&s).bit_count() >= 2 for i,r in enumerate(rows) for s in rows[:i]):
            continue
        edges = [(i,j) for i in range(n) for j in range(n) if rows[i] >> j & 1]
        reps = []
        for a,b in itertools.product(permutations, repeat=2):
            reps.append(sum(1 << (a[i]*n+b[j]) for i,j in edges))
            reps.append(sum(1 << (b[j]*n+a[i]) for i,j in edges))
        counts[min(reps)] += 1
    return counts


def stars(n, edges):
    if not edges:
        return [], 2*n
    cover = min((S for S in range(1 << (2*n)) if all(S>>a&1 or S>>b&1 for a,b in edges)),
                key=int.bit_count)
    assignments = {}
    for a,b in edges:
        center, neighbor = (a,b) if cover>>a&1 else (b,a)
        assignments.setdefault(center, []).append(neighbor)
    gates = []

    def gate(op, a, b):
        gates.append((op, a, b))
        return 2*n + len(gates)-1

    def merge(inputs):
        out = inputs[0]
        for w in inputs[1:]:
            out = gate("or", out, w)
        return out

    out = merge([gate("and", c, merge(leaves)) for c,leaves in assignments.items()])
    return gates, out


def verify_star(n, edges, gates, out):
    pointside = (1<<n)-1
    def values(row):
        val = [bool(row>>i&1) for i in range(2*n)]
        for op,a,b in gates:
            assert op in ("and", "or") and 0<=a<len(val) and 0<=b<len(val)
            val.append(val[a] and val[b] if op=="and" else val[a] or val[b])
        return val
    for row in range(1 << (2*n)):
        val = values(row)
        target = any(row>>a & row>>b & 1 for a,b in edges)
        assert (val[out] if out<len(val) else False) == target
        p, l = values(row & pointside), values(row & ~pointside)
        for j,(op,a,b) in enumerate(gates, 2*n):
            if op == "and" and val[j]:
                assert p[j] or l[j] or target
                assert row.bit_count() != 1


class Formula:
    def __init__(self):
        self.nv = 0
        self.clauses = []

    def new(self):
        self.nv += 1
        return self.nv

    def one(self, choices):
        self.clauses.append(choices)
        self.clauses.extend([-a,-b] for a,b in itertools.combinations(choices,2))

    def write(self,path):
        with path.open('w') as out:
            print('p cnf',self.nv,len(self.clauses),file=out)
            for c in self.clauses:
                print(*c,0,file=out)


def lower_instance(edges, size):
    # Isolated inputs can all be fixed false and propagated. Only essential
    # input wires remain. Row evaluation is exact at monotone extremal rows.
    active = sorted({x for edge in edges for x in edge})
    m = len(active)
    edges = [(active.index(a),active.index(b)) for a,b in edges]
    pos = [(1<<a)|(1<<b) for a,b in edges]
    neg = [x for x in range(1<<m) if not any(x&p==p for p in pos)]
    maximal = [x for x in neg if all(x==y or x&y!=x for y in neg)]
    rows = pos+maximal
    f = Formula()
    v = [[f.new() for r in rows] for j in range(m+size)]
    for i in range(m):
        f.clauses += [[p if r>>i&1 else -p] for p,r in zip(v[i],rows)]
    f.clauses += [[p if t<len(pos) else -p] for t,p in enumerate(v[-1])]
    gates = []
    for j in range(m,m+size):
        options = {}
        for a,b in itertools.combinations(range(j),2):
            for op in (0,1):
                selector = options[a,b,op] = f.new()
                for A,B,Y in zip(v[a],v[b],v[j]):
                    if op:
                        f.clauses.extend([[-selector,-Y,A],[-selector,-Y,B],[-selector,Y,-A,-B]])
                    else:
                        f.clauses.extend([[-selector,Y,-A],[-selector,Y,-B],[-selector,-Y,A,B]])
        f.one(list(options.values()))
        gates.append(options)
    # Minimality implies every internal wire and every essential input has a consumer.
    for i in range(m+size-1):
        f.clauses.append([s for opt in gates for (a,b,op),s in opt.items() if i==a or i==b])
    # Choose the lexicographically first encoding among all topological orders.
    # Adjacent independent gates in descending order could have been swapped.
    for j in range(1,size):
        for (a,b,o),s in gates[j-1].items():
            for (c,d,p),t in gates[j].items():
                if d != m+j-1 and (a,b,o) > (c,d,p):
                    f.clauses.append([-s,-t])
    return f


def check_size(solver, timeout, n, work):
    work = work / f'n{n}'
    work.mkdir(parents=True, exist_ok=True)
    results_path = work / 'results.json'
    results_path.unlink(missing_ok=True)
    counts = classes(n)
    results = []
    for mask, orbit in sorted(counts.items()):
        edges = [(i, n+j) for i in range(n) for j in range(n) if mask >> (n*i+j) & 1]
        gates, out = stars(n, edges)
        verify_star(n, edges, gates, out)
        active = len({v for edge in edges for v in edge})
        tests = []
        for size in range(max(0, active-1), len(gates)):
            cnf = work / f'{mask:x}-{size}.cnf'
            proof = cnf.with_suffix('.lrat')
            proof.unlink(missing_ok=True)
            f = lower_instance(edges, size)
            f.write(cnf)
            start = monotonic()
            proc = subprocess.run(
                [solver, '--quiet', '--check=true', '--lrat=true', '--binary=false',
                 '-t', str(timeout), str(cnf), str(proof)],
                capture_output=True, text=True)
            if proc.returncode != 20:
                raise SystemExit(f'{cnf}: expected UNSAT (exit 20), got {proc.returncode}\n'
                                 f'{proc.stdout}\n{proc.stderr}')
            if not proof.is_file() or proof.stat().st_size == 0:
                raise SystemExit(f'{cnf}: solver produced no LRAT certificate')
            tests.append({'size': size, 'result': 'UNSAT', 'variables': f.nv,
                          'clauses': len(f.clauses), 'seconds': round(monotonic()-start, 3)})
        row = {'mask': hex(mask), 'orbit': orbit, 'essential': active, 'upper': len(gates),
               'gates': gates, 'output': out, 'tests': tests}
        results.append(row)
        print(f'N={n}, mask={mask:#x}, orbit={orbit}, minimum={len(gates)}, '
              f'refuted sizes={[t["size"] for t in tests]}', flush=True)
    results_path.write_text(json.dumps(results, indent=2)+'\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('solver', help='path or command name for CaDiCaL')
    parser.add_argument('--timeout', type=int, default=30, help='solver seconds per instance')
    parser.add_argument('--n', type=int, choices=range(4), help='one side size (default: all 0–3)')
    parser.add_argument('--output', type=Path, required=True, help='directory for CNFs, LRAT and JSON')
    args = parser.parse_args()
    if not __debug__:
        parser.error('Python assertions are required; remove -O or PYTHONOPTIMIZE')
    if args.timeout <= 0:
        parser.error('--timeout must be positive')
    for n in range(4) if args.n is None else [args.n]:
        check_size(args.solver, args.timeout, n, args.output)


if __name__ == '__main__':
    main()
