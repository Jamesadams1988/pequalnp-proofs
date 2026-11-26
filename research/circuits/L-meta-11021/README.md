# Exact size 16 and depth 5 for a nine-input edge function

**James Adams** · November 26, 2026

A single monotone circuit with **16 gates and depth 5** attains both minima for the twelve-edge graph in L-meta-11020. Allowing NOT gates and arbitrary sharing preserves both lower bounds. L-meta-11021 asks for a circuit with at most 15 gates for this same function. The lower bound rules it out. [Exact assigned statement](sources/assignment.json) · [Witness and 512-input replay](upper/README.md)

## Where the size lower bound comes from

Budleigh proved the normalization theorem. MrMaleficus proved the nine-way first-gate case split. Tmuniz1901-code, zakpgrove and dukfaar proved its individual cases. The zero-pivot case appears under L-meta-17103 and has exactly the proposition required by the split. James matched all ten premises, assembled the existing theorems into the 16-gate lower bound, and supplied the matching upper circuit. Each of the eleven upstream source files matches both the checked registry hash and its merged pull request. [Lean assembly](lower/README.md) · [Source hashes and author credits](sources/dependencies.json)

## Why depth five is necessary

A generic Lean theorem unfolds the output of any binary circuit of depth at most four and recompiles it with at most fifteen gates. An independent computation proves the depth bound directly, even if complemented inputs are free. If a depth-four circuit ends in OR and rejects all 57 false inputs, it can cover at most 9 of 12 edges. If it ends in AND and accepts all 455 true inputs, it can reject at most 7 of the 13 maximal false inputs. Explicit formulas attain both limits. [Lean depth proof](depth/README.md) · [Finite depth certificate, independent verifier and sharp examples](depth-test/README.md)

## Which intermediate products can an optimal circuit afford?

Suppose the prefix computes any number of conjunctions and the remaining circuit is a monotone formula that may reuse prefix wires. If the prefix must compute each edge product in a set S, the exact minimum is 11 + |S| + τ(E ∖ S), where τ is the minimum number of vertices meeting every edge of the indicated subgraph. An exhaustive check covers all 4,096 choices of S. Among nonempty choices, only (0,4) alone and (1,5) alone permit 16 gates. A separate calculation classifies all 81 choices of a paid first gate followed by a monotone formula. [Proof and enumeration](formulas/README.md) · [First-gate classifications](formulas/first-wire/README.md)

Lean checked the exact size of 16 and the exact depth of five. Eight of the nine lower-bound case files compiled as published. The zero-pivot case compiled from its original declaration bodies in 87 source-verified modules. The size witness also passed the project’s local checker, which rejected the same witness for a 15-gate bound. The full local replay reached its 14-minute wall-clock limit while the isolated mathematical checker was running. It returned no verdict on the refutation. [Verification record](sources/local-checks.json) · [Checker output](sources/local-checker-output.txt)

## Replay

The finite checks need Python 3.10 or newer and a C++20 compiler. Run the script from this directory.

```sh
bash replay-finite.sh
```

To replay the 16-gate checker verdict and its 15-gate negative control, run `bash upper/replay-checker.sh /path/to/pequalnp-proofs/lean`.

The full Lean replay uses the proofs repository at commit `6284ae5ebdec19cb4bce06d15e190de3560bc099`, Lean 4.36.0 and the project’s pinned Mathlib. With the dependencies installed, the following command checks the input hashes, compiles the upstream sources, proves the size and depth theorems and invokes the project’s mathematical checker in refutation mode. Rebuilding the nine case files is resource-intensive. The optional `--prebuilt` argument uses corresponding modules already compiled in the project’s Lean search path. The zero-pivot case can be rebuilt in 87 smaller modules while preserving every original declaration body. [Memory-bounded replay](lower/split17103/README.md)

```sh
bash replay-lean.sh /path/to/pequalnp-proofs/lean
```

The official assignment requests a proof of the negative statement with `PEqualNP.Defs` as its permitted project import. The refutation here uses eleven merged upstream modules on the research fork. The upstream intake bot closed the direct positive PR on November 26 because the attack no longer needed that step. The public desk export at 02:52 UTC had no direct checked entry for either statement. [Upstream closure](https://github.com/open-goat/pequalnp-proofs/pull/19150#issuecomment-7181128698) · [Public status at the time of this replay](sources/upstream-status.json)
