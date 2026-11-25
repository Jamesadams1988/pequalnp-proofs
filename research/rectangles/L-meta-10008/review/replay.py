"""Replay cover witnesses and inspect the exact upstream snapshot using the public assignment."""
import argparse
import ast
import hashlib
import collections
import itertools
import json
from pathlib import Path
import re
import subprocess



HERE = Path(__file__).resolve().parent
SNAPSHOT = '41fe834b000fc5190f11224bb9e6bc645249cc7b'
ROWS = ast.literal_eval(re.search(r'def rows : List ℕ := (\[[\d, ]+\])',
                                 (HERE / 'TwoSupports.lean').read_text())[1])
CELLS = set(itertools.product(range(31), repeat=2))
ZEROS = {(i,j) for i,j in CELLS if not ROWS[i] >> j & 1}
COLUMNS = [sum((ROWS[i] >> j & 1) << i for i in range(31)) for j in range(31)]


def bits(mask):
    if not 0 <= mask < 1 << 31:
        raise ValueError(mask)
    return [i for i in range(31) if mask >> i & 1]


def evaluate(boxes):
    multiplicity = collections.Counter(cell for a,b in boxes for cell in set(itertools.product(a,b)))
    covered = set(multiplicity)
    assert covered <= CELLS
    return dict(rectangles=len(boxes), missing=len(ZEROS - covered), invalid=len(covered - ZEROS),
                multiplicities=sorted(collections.Counter(multiplicity.values()).items()))


def masks_to_sets(boxes):
    return [(bits(a),bits(b)) for a,b in boxes]


def upstream(repo):
    checked = {
        'L-meta-10002': 'df87737a7910f45c27447a111dfb6823eb4acad36905abf63083e053c266fc50',
        'L-meta-10004': '2e9139c3c4a392de35761b397ce6df2c69b693b3339dab30640ee0d9117197aa',
        'L-meta-10011': 'a4fe21c36d25362c621f0f98b4906622a171e633cb668bff85de24101d158189',
        'L-meta-10013': '6311631d5254fd097fbf4e903e87a67a46917b0b4718f1433fa3b478fd673915',
        'L-meta-10015': 'f493216bbedb804ebcc0ec79c03aa7d353ffc3be141ecc248536178f17724b1f',
        'L-meta-10017': '0f40a9f267449f0302c98472953c5ae828bd365311371a3da9d9e3057fdf5ced',
    }
    result = {}
    for i in [10002,10004,10011,10013,10015,10017]:
        identifier = f'L-meta-{i}'
        path = f'lean/PEqualNP/Outside/L_meta_{i}.lean'
        content = subprocess.check_output(
            ['git','-C',str(repo),'show',f'{SNAPSHOT}:{path}'], text=True)
        assert hashlib.sha256(content.encode()).hexdigest() == checked[identifier]
        theorem = content[content.rfind('theorem PEqualNP.Outside.'):]
        matrices = re.findall(r'\[[\d,\s]+\]',theorem)
        assert matrices and all(ast.literal_eval(x)==ROWS for x in matrices)
        threshold = int(re.search(r'L.length ≤ (\d+)',theorem)[1])
        result[identifier] = {'kind':'lower' if '¬ (∃ L' in theorem else 'upper','threshold':threshold}
        if i == 10013:
            raw = content.split('def cover :',1)[1].split(':=',1)[1].split('end PEqualNP',1)[0]
            boxes = ast.literal_eval(raw.replace('{','[').replace('}',']').strip())
        elif i in [10011,10015,10017]:
            raw = re.search(r'def (?:boxes|P) : List .*? := (\[.*?\])\n', content)[1]
            boxes = masks_to_sets(ast.literal_eval(raw))
        else:
            continue
        result[identifier].update(evaluate(boxes))
        assert result[identifier]['missing'] == result[identifier]['invalid'] == 0
    return result


def main():
    for design in [ROWS,COLUMNS]:
        assert {row.bit_count() for row in design} == {6}
        assert {(a & b).bit_count() for a,b in itertools.combinations(design,2)} == {1}
    witness = [(8,25),(13,28),(16,12),(21,11),(18,20),(5,17)]
    assert set(witness) <= ZEROS
    assert all((p,m) not in ZEROS or (q,l) not in ZEROS
               for (p,l),(q,m) in itertools.combinations(witness,2))
    parser = argparse.ArgumentParser()
    parser.add_argument('--upstream-git', type=Path,
                        help='Git repository containing the pinned upstream commit')
    parser.add_argument('--cover', type=Path, action='append', default=[],
                        help='JSON array of row/column sets or decimal mask pairs')
    args = parser.parse_args()

    # Any seven-point Fano configuration has a quadrangle: take the complement
    # of one of its seven lines. Its three diagonals are the other three points.
    def unique_index(mask):
        assert mask.bit_count() == 1
        return mask.bit_length() - 1

    def join(p,q):
        return unique_index(ROWS[p] & ROWS[q])

    def meet(l,m):
        return unique_index(COLUMNS[l] & COLUMNS[m])

    quadrangles = 0
    collinear_diagonals = 0
    for a,b,c,d in itertools.combinations(range(31),4):
        sides = [join(x,y) for x,y in itertools.combinations((a,b,c,d),2)]
        if len(set(sides)) != 6:
            continue
        quadrangles += 1
        ab,ac,ad,bc,bd,cd = sides
        x,y,z = meet(ab,cd), meet(ac,bd), meet(ad,bc)
        collinear_diagonals += bool(ROWS[x] & ROWS[y] & ROWS[z])
    assert collinear_diagonals == 0
    report = {'upstream_sha':SNAPSHOT, 'zero_cells':len(ZEROS), 'fooling_set':witness,
              'quadrangles':quadrangles, 'collinear_diagonals':collinear_diagonals}
    if args.upstream_git:
        report['upstream'] = upstream(args.upstream_git)
    for path in args.cover:
        claimed_missing = None
        if path.suffix == '.json':
            data = json.loads(path.read_text())
            if isinstance(data, dict):
                if data.get('rows') != ROWS:
                    raise ValueError(f'{path} uses different rows')
                claimed_missing = data.get('missing')
                boxes = data['rectangles']
            else:
                boxes = data
            if boxes and isinstance(boxes[0][0],int):
                boxes = masks_to_sets(boxes)
        else:
            masks = [tuple(map(int,line.split())) for line in path.read_text().splitlines()
                     if line.strip()]
            boxes = masks_to_sets(masks)
        if claimed_missing is not None:
            covered = {cell for a,b in boxes for cell in itertools.product(a,b)}
            if sorted(ZEROS - covered) != sorted(map(tuple,claimed_missing)):
                raise ValueError(f'{path} lists different missing cells')
        report[str(path)] = evaluate(boxes)
    print(json.dumps(report,indent=2))


if __name__=='__main__':
    main()
