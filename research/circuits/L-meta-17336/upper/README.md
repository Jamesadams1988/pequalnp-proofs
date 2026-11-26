# Fixed first gates for L-meta-17336

The 12-edge function on nine inputs has a 16-gate circuit beginning with each of the gates `x5 OR x6`, `x5 OR x7`, and `x5 OR x8`. There is a 17-gate witness for each of the seven allowed first wires. Upstream subsequently established a 16-gate lower bound for all seven choices. The three OR-first constructions therefore attain the exact minimum. [Lower bound and attribution](../resolution/README.md)

| Value of wire 9 | Exact witness sizes |
| --- | --- |
| NOT x5 | 17 |
| x5 AND x6, x5 AND x7, x5 AND x8 | 17 for each |
| x5 OR x6, x5 OR x7, x5 OR x8 | 16 and 17 for each |

[Witnesses.lean](Witnesses.lean) contains ten literal gate lists in the repository’s `Circuit` type. Each specification proves `FanInTwo`, the exact gate count, the value of wire 9 on every assignment, and equality of `circuitFun 9` with the desk’s literal disjunction. Each 17-gate OR variant appends an OR gate with both inputs set to the 16-gate circuit’s output. The first gate can be unused by the output, as allowed by the assigned predicate. No claim about gate necessity is made.

## Replay

Use the public proofs repository at revision `c468e9f20b8fea4dc13ef9abde683cb439979a1c`, with Lean 4.36.0 and the `PEqualNP.Defs.MetaComplexityMinimal` module built. From this folder run

```bash
./check.sh /path/to/pequalnp-proofs/lean
python3 verify.py
```

The Lean proof exposes the input list, simplifies the concrete gates, distributes AND over OR, and normalizes associativity and commutativity. Each theorem prints its axiom list. [Lean output](lean.log)

The Python verifier reads the gate lists from the Lean file. It checks bounds and arity for each wire, then checks wire 9 and the final output on all 512 assignments per circuit. Dropping edge (0, 4) changes ten assignments in each comparison. When provided the original desk-assignment JSON as an argument, it also verifies that the Lean target is a byte-for-byte copy of the desk’s Boolean expression. [Independent replay](verify.py) · [Results](truth-tables.txt)

[make.py](make.py) regenerates the Lean file from the assignment JSON and the star-cover witness JSON. Pass those paths followed by the desired output filename. The Lean and Python checks run directly on the included gate lists.
