# Nine gates are necessary for L-meta-15174

The function with truth table `0xe8a8a8a8e8008800` needs **exactly nine gates**, even when NOT gates are available. A nine-gate AND/OR formula attains the bound. James Adams (Jamesadams1988) specialized Scott Hazlitt’s live-wire checker to six inputs and verified the lower bound in Lean. The earlier positive proof by 2undvierzig supplies a different nine-gate circuit and shows that any circuit containing a NOT needs at least nine gates. It leaves open the possibility of an eight-gate monotone circuit. [Exact minimum](Nine.lean) · [Earlier positive proof](https://github.com/open-goat/pequalnp-proofs/pull/20049) · [Scott Hazlitt’s checker and credits](https://github.com/open-goat/pequalnp-proofs/pull/12798)

The upper bound is the formula `(x1 OR (x0 AND x2)) AND ((x0 AND x5) OR (x3 AND ((x0 AND x1) OR (x2 AND x4))))`. Lean evaluates it on all 64 inputs. For the lower bound the checker encodes 82 pairs of inputs on which the function differs. Every essential input must reach the output. Combining six live inputs into one output takes at least five binary gates, leaving at most three NOT gates in a circuit of size eight. Lean rules out each of the four possible NOT counts.

The function for L-meta-13131 has the same minimum. Complementing the inputs and the output and permuting the coordinates gives the second table. Lean transfers every unrestricted gate budget in both directions, then verifies a nine-gate monotone witness for the second table. Arthur Ariel Sabintsev’s merged proof had supplied a nine-gate upper bound and an eight-binary-gate lower bound. [Equivalence of budgets](DualBudgets.lean) · [Nine-gate corollary](DualExact.lean) · [Earlier merged proof](https://github.com/open-goat/pequalnp-proofs/pull/17300)

## An independent monotone search

The Python search uses the five minimal true rows and seven maximal false rows. A monotone circuit agrees with the target everywhere if it agrees on these twelve rows. At each stage, each true/false pair needs a live wire that is 1 on the true row and 0 on the false row. If that distinction has disappeared, no later AND or OR can recover it.

The algorithm tries both gates on every pair of live wires. It tries retaining neither, either or both operands for later use, which allows shared subcircuits. It skips gates whose boundary values are already available. After unused gates are removed, one binary gate can reduce the live-wire count by at most one. This gives a second pruning rule when too few gates remain. Sorting the wire values lets the search reuse results across different gate orders. A returned circuit is checked against the full truth table.

At budget eight the search exhausted 27,249 distinct states. At budget nine it produced a witness. Independent breadth-first enumeration agrees across all applicable two-, three- and four-input truth tables at the tested budgets. The control set contains 2, 9 and 114 monotone functions with all inputs essential, respectively. [Search](monotone_search.py) · [Controls](test_monotone_search.py)

## All twelve restrictions

The entries give the minimum after fixing one input. For each entry Lean constructs a monotone circuit and proves a matching lower bound with NOT allowed. The strongest single restriction raises the full-function lower bound to eight. The full search above supplies the ninth gate. [Lean profile](CofactorProfile.lean) · [Noptus’s five-input search](https://github.com/open-goat/pequalnp-proofs/pull/12814)

| Input | False | True |
|---|---:|---:|
| x0 | 3 | 5 |
| x1 | 4 | 5 |
| x2 | 3 | 7 |
| x3 | 3 | 7 |
| x4 | 5 | 7 |
| x5 | 6 | 6 |

## Replay

From this directory, with Python 3.10 or later, run the following commands.

```sh
python3 monotone_search.py 0xe8a8a8a8e8008800 6 8
python3 monotone_search.py 0xe8a8a8a8e8008800 6 9
python3 -m unittest test_monotone_search
```

For the formal proofs use the upstream tree at `cbc4771b3dad5185fd62d122dedefc1023113dd5` with its pinned Lean 4.36.0 and Mathlib. Set `research_dir` to this directory’s absolute path and `upstream` to the absolute upstream checkout. In its `lean/` directory, build the imported modules. Compile the two local modules in a temporary directory for use by the corollary.

```sh
cd "$upstream/lean"
lake build PEqualNP.Outside.L_meta_8657 PEqualNP.Outside.L_meta_12184
replay_dir=$(mktemp -d)
lake env lean --root="$research_dir" -o "$replay_dir/Nine.olean" "$research_dir/Nine.lean" &&
  lake env lean --root="$research_dir" -o "$replay_dir/DualBudgets.olean" "$research_dir/DualBudgets.lean" &&
  lake env sh -c 'export LEAN_PATH="$1:$LEAN_PATH"; lean "$2/DualExact.lean"' sh "$replay_dir" "$research_dir"
lake env lean "$research_dir/CofactorProfile.lean"
```

For the official local checker, generate one file in a fresh upstream checkout with dependencies installed. The posted statement for L-meta-15174 is negative, so this diagnostic uses the checker’s `refute` mode.

```sh
cd "$upstream"
proof=lean/PEqualNP/Outside/L_meta_15174.lean
python3 "$research_dir/pack_proof.py" "$upstream" "$proof" &&
  node tools/check-lean.mjs "$proof" "$research_dir/statement.txt" refute
```
