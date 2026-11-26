# Independent verification of the prefix table

This checker recomputes leaf counts for seven first gates on the nine-input edge function in L-meta-17336. Each first gate has a baseline row and 100 choices for the second gate. The suffix is an AND/OR formula and may reuse both prefix outputs as leaves.

From this directory, run the following commands with Python 3 and a C++20 compiler. The executable is temporary. The default input is the prefix table `../expected.txt`, resolved relative to `audit.py`.

```sh
build_dir=$(mktemp -d)
trap 'rm -rf "$build_dir"' EXIT
c++ -std=c++20 -O3 -march=native split.cpp -o "$build_dir/split"
python3 audit.py --solver "$build_dir/split" --all
```

The full run checks 707 entries. Omitting `--all` runs each baseline and a representative of each reported second-gate cost per first gate. Both modes compare every entry whose separator collection has already been examined and report the number verified. Use `--expected PATH` to check another copy of the table. A discrepancy prints the first gate, the second gate or baseline, and the computed and expected values. The process exits with status 1.

## Calculation

The driver enumerates all 512 vertex subsets to obtain 12 minimal positive assignments and 13 maximal negative assignments. It evaluates each available wire on all 512 assignments and records the positive samples it accepts and the negative samples it rejects. A wire separates every subrectangle of these two sample sets. Keeping only maximal wire rectangles preserves all possible single-leaf separators.

For each nonempty rectangle the C++ solver considers a separating leaf and all proper bipartitions of its positive or negative side. An OR gate joins two solutions for a positive split. An AND gate joins two solutions for a negative split. Conversely, if a child fails to separate the parent rectangle, the root must split the appropriate side between its children. Overlapping samples can be assigned to either child. Processing negative subsets by increasing cardinality, and positive subsets by increasing mask within each cardinality, gives the exact minimum.

The result is an exact leaf count on these extremal samples. It bounds the leaf count on the full truth table from below, including when a prefix gate uses NOT.
