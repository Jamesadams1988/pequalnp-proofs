"""Search minimal shift-invariant exact uniform multicovers by largest rectangles."""
from itertools import combinations_with_replacement
from pathlib import Path
import json
from fractional import six_by_ten, ALL, N


def rotate(x, k):
    return ((x << k) | (x >> (N-k))) & ALL


def main():
    rows = json.loads((Path(__file__).resolve().parent.parent / "degree" / "rows.json").read_text())
    offsets = [j for j in range(N) if rows[0] >> j & 1 == 0]
    groups = {}
    for ps, b in six_by_ten(rows):
        a=sum(1<<p for p in ps)
        can=min(rotate(a,k) for k in range(N))
        if a==can:
            v=tuple((b & rotate(a,j)).bit_count() for j in offsets)
            groups[a,b]=v
    assert len(groups)==100
    boxes=list(groups)
    vecs=list(groups.values())
    # If L complete shift orbits give a t-fold cover, L*60=25*t,
    # so the smallest positive possibility is L=5, t=12.
    # Digits for sums of at most 5 vectors are ≤30; no base-64 carries.
    ids=[sum(v<<(6*i) for i,v in enumerate(vs)) for vs in vecs]
    target=sum(12<<(6*i) for i in range(len(offsets)))
    pairs={}
    for a,b in combinations_with_replacement(range(len(ids)),2):
        pairs[ids[a]+ids[b]]=(a,b)
    for a,b,c in combinations_with_replacement(range(len(ids)),3):
        r=target-ids[a]-ids[b]-ids[c]
        if r in pairs:
            selected=(a,b,c,*pairs[r])
            assert all(sum(vecs[s][j] for s in selected)==12 for j in range(len(offsets)))
            print("Five shift orbits giving exact multiplicity twelve:",[boxes[s] for s in selected])
            return
    print("All five-orbit multisets excluded for 6-by-10 rectangles.")
if __name__=="__main__":
    main()
