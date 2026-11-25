# Cutting-planes refutations for six pigeons and five holes

James Adams (Jamesadams1988)

The shortest unrestricted proof in the project’s cutting-planes system has **between 181 and 196 lines**. The desk asks for 195. The lower bound comes from macayaven’s upstream proof, which received an accepted checker verdict. The 196-line upper bound below independently verifies the construction length reported by the desk. [Upstream lower-bound verdict](https://github.com/open-goat/pequalnp-proofs/pull/21720#issuecomment-7176212646)

| Checked construction | Lines | Longest chain of divisions |
| --- | ---: | ---: |
| Successively bound the occupancy of larger subsets of pigeons in each hole. | [196](Control196.lean) | 4 |
| Combine four triangle bounds per hole before introducing the sixth pigeon. | [211](DepthThree211.lean) | 3 |

Both Lean files derive the contradiction in the project’s `IsCPRefutation` system. The [integer replay](traces.py) checks coefficient divisibility, rounding and line dependencies. The 196-line construction uses 81 premises, 80 additions, 15 scalar multiplications and 20 divisions.

**Exactly three rounding rounds are necessary and sufficient.** After two full Chvátal–Gomory rounds, the only feasible real point has every variable equal to one fifth. The third round excludes it. The three-round construction above realizes that depth in the project’s inference system. The proof and its Lean-checked components are in [the rank argument](rank/second-round.md). Earlier work establishes logarithmic rank for the general family. [Published literature](https://www.sciencedirect.com/science/article/pii/S0304397509002825)

**Where a shorter proof could differ.** For independent columns whose intermediate cuts certify clique capacities and partition the pair premises into disjoint branches, 196 lines are necessary. An explicit four-vertex obstruction forces the usual sequence of increasingly large cliques. Even if completed proper-subclique capacities can be reused across cuts, each independent six-pigeon column costs at least 36 lines when all other arithmetic stays within a single cut. The complete bounded enumeration allows arbitrary integer scaling. [DAG model, proof and replay](dag/README.md)

A separate subset computation tests arbitrary exact divisors in trees that use each pair premise at most once, with no scaling. It excludes both the single-column capacity and the contradiction from the additional premise that two pigeons occupy that hole. [Clique-capacity trees](trees/README.md) · [Read-once calculation](read-once/README.md)

## Replay

With Python 3, a C++17 compiler and the repository’s configured Lean 4.36.0 environment, run `bash replay.sh /path/to/pequalnp-proofs/lean` from this directory. The Mathlib pin is `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. Running `python3 traces.py` alone reproduces the line and division-depth counts.
