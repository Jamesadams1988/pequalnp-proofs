"""Independently replay positive-hint LRAT against the regenerated pair-minimum encoding."""
import argparse
import gzip
from pathlib import Path
from pair_minimum import encode


def replay(path):
    formula = encode(10)
    live = dict(enumerate(formula.clauses, 1))
    seen = len(live)
    added = 0
    empty = False
    stream = gzip.open(path, "rt") if path.suffix == ".gz" else path.open()
    with stream:
        for line in stream:
            tokens = line.split()
            if tokens[1] == "d":
                assert tokens[-1] == "0"
                for value in tokens[2:-1]:
                    del live[int(value)]
                continue
            step = [int(n) for n in tokens]
            zero = step.index(0)
            number, clause, hints = step[0], step[1:zero], step[zero + 1:-1]
            assert step[-1] == 0 and number > seen
            seen = number
            assert all(0 < abs(v) <= formula.n for v in clause)
            assert all(h in live for h in hints)
            assigned = {-v for v in clause}
            assert not any(-v in assigned for v in assigned)
            for h in hints:
                origin = live[h]
                assert not any(lit in assigned for lit in origin)
                unfixed = {lit for lit in origin if -lit not in assigned}
                assert len(unfixed) <= 1
                if not unfixed:
                    break
                assigned.update(unfixed)
            else:
                raise ValueError(f"RUP failed on line {number}")
            live[number] = clause
            added += 1
            empty |= not clause
    assert empty
    print(f"10 lines excluded: {formula.n} variables, {len(formula.clauses)} clauses, {added} RUP additions.")


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run without Python -O to enable all checks.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("proof", type=Path)
    replay(parser.parse_args().proof)
