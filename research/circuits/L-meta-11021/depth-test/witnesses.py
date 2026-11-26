"""Find and verify depth-four circuits attaining both one-sided bounds."""
from itertools import combinations_with_replacement
import json
from pathlib import Path
import sys

EDGES = ((0,4), (0,5), (1,5), (2,6), (3,6), (0,7), (2,7), (4,7), (1,8), (3,8), (4,8), (6,8))
FULL = (1 << 512) - 1
VARIABLES = [sum(1 << x for x in range(512) if x & (1 << v)) for v in range(9)]
GOAL = sum(1 << x for x in range(512) if any((x >> a) & (x >> b) & 1 for a,b in EDGES))
EDGE_INPUTS = [(1 << a) | (1 << b) for a,b in EDGES]
MAX_NEG = [x for x in range(512) if not (GOAL >> x) & 1 and
           all((GOAL >> (x | (1 << v))) & 1 for v in range(9) if not x & (1 << v))]
EDGE_TABLE = sum(1 << x for x in EDGE_INPUTS)
CUT_TABLE = sum(1 << x for x in MAX_NEG)


def smaller_gates():
    gates = {t: i for i,t in enumerate(VARIABLES)}
    # Constants may be left out when searching for the two positive examples.
    for _ in range(2):
        for a,b in combinations_with_replacement(list(gates),2):
            if a & b not in gates:
                gates[a & b] = ["and", gates[a], gates[b]]
            if a | b not in gates:
                gates[a | b] = ["or", gates[a], gates[b]]
    return gates


def search():
    small = smaller_gates()
    sound, complete = {}, {}
    for a,b in combinations_with_replacement(list(small),2):
        for op,t in (("and",a & b),("or",a | b)):
            if not t & (FULL ^ GOAL):
                sound.setdefault(t & EDGE_TABLE, (op,a,b))
            if not GOAL & (FULL ^ t):
                complete.setdefault((FULL ^ t) & CUT_TABLE, (op,a,b))

    def witness(frontier, op, wanted):
        for a,b in combinations_with_replacement(frontier,2):
            if (a | b).bit_count() == wanted:
                def expand(mask):
                    gate,left,right = frontier[mask]
                    return [gate, small[left], small[right]]
                return [op, expand(a), expand(b)]
        raise ValueError("missing extremum witness")

    return {"or_root":witness(sound,"or",9),"and_root":witness(complete,"and",7)}


def evaluate(expr):
    if type(expr) is int and 0 <= expr < 9:
        return VARIABLES[expr],0
    if not isinstance(expr,list) or len(expr)!=3 or expr[0] not in ("and","or"):
        raise ValueError("invalid formula")
    a,da = evaluate(expr[1])
    b,db = evaluate(expr[2])
    return (a & b if expr[0]=="and" else a | b), 1 + max(da,db)


def check(data):
    if len(MAX_NEG)!=13 or (FULL ^ GOAL).bit_count()!=57:
        raise ValueError("unexpected truth table")
    for key, op in (("or_root","or"),("and_root","and")):
        tree = data[key]
        value,depth = evaluate(tree)
        if tree[0]!=op or depth!=4:
            raise ValueError("wrong root or depth")
        if op=="or":
            if value & (FULL ^ GOAL) or (value & EDGE_TABLE).bit_count()!=9:
                raise ValueError("incorrect sound witness")
        else:
            if GOAL & (FULL ^ value) or ((FULL ^ value) & CUT_TABLE).bit_count()!=7:
                raise ValueError("incorrect complete witness")


if __name__ == "__main__":
    if sys.argv[1:] == ["--search"]:
        data = search()
        check(data)
        print(json.dumps(data,separators=(",",":")))
    elif not sys.argv[1:]:
        data = json.loads(Path(__file__).with_name("witnesses.json").read_text())
        check(data)
        print("Both depth-four extremizers verified on all 512 inputs.")
    else:
        raise SystemExit("usage: python3 witnesses.py [--search]")
