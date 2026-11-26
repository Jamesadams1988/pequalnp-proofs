# Formula continuations with a reusable negation

**The exact minimum in this model is 16 gates.** The seven baseline searches and all 70 searches with an additional reusable negation excluded a 15-gate circuit on the 25 mandatory tests.

The first gate computes one of the seven functions allowed in L-meta-17336. Its output and the nine raw input wires remain freely available. The continuation is a binary AND/OR formula: each of its gates is used once, while the available input wires may be used any number of times. A second version first pays for a NOT gate on any raw wire or on the output of the first gate. This new output may also be used any number of times in the subsequent formula. The two preprocessing gates can have fanout. Later shared gates and negations of compounds built by the continuation are outside this model.

A formula with $L$ leaves uses $L-1$ gates. A 15-gate counterexample therefore allows 15 leaves after one preprocessing gate, or 14 leaves after two. Either preprocessing gate can be unused. The fixed first gate's stipulated truth table makes its syntactic choice of operands immaterial.

A 16-gate construction sets $s=x_5\lor x_8$ at the first gate, then ORs the following five terms. The continuation has 16 leaves and hence 15 binary gates. The expression was checked on all 512 assignments.

$$x_0(x_4\lor x_5\lor x_6),\quad x_6(x_2\lor x_3),\quad x_7(x_1\lor x_2\lor x_4),\quad x_1s,\quad x_8(x_3\lor x_5).$$

## Exhaustive recurrence

The 12 positive tests set exactly the two endpoints of an edge. The 13 negative tests set a maximal independent set. Every correct circuit must pass these 25 tests. On these inputs, represent an intermediate expression by its set of mistakes relative to the target. If $P$ and $N$ are the masks of positive and negative tests, AND combines two error sets $A,B$ as

$$((A\cup B)\cap P)\cup((A\cap B)\cap N).$$

OR exchanges the union and intersection. Both operations are monotone under inclusion of error sets. An expression can therefore replace another in any AND/OR continuation whenever it has no more leaves and its mistakes form a subset. This remains valid if a leaf names a negative feature. It uses the monotonicity of the **continuation operations** with respect to errors, irrespective of the raw-input polarity of the available features.

Start with one-leaf expressions for every available feature. At each new leaf count, combine the retained signatures over all positive splits of that count, in both gate types. Keep only signatures undominated by a formula of the same or lower cost. Any discarded child has a cheaper or equally costly replacement; applying the same parent operation produces a cheaper or equally costly expression with no new mistakes. Thus absence of the empty signature through the budget excludes every such formula. Dominance is tested by marking supersets in a 25-bit error-mask space. The program runs independently of the communication-protocol dynamic program.

For monotone expressions in raw inputs, success on this boundary certifies the full function. With a negative feature, a successful boundary transcript needs an all-512-input check. Exclusion on the boundary still proves exclusion on the full cube. For example, the expression `NOT ((x4 AND x6) OR ((x2 OR x7) AND (x3 OR x5 OR x8)))` passes all 25 tests and disagrees with the target on 387 of the 512 assignments, including the all-zero input. Its existence illustrates why an unconstrained signed transcript cannot be published as a circuit witness.

Compile and replay with a C++20 compiler. In the last argument, 0 through 8 selects a raw input to negate, and 9 selects the first gate. Omitting that argument tests just the first preprocessing gate.

```sh
c++ -O3 -std=c++20 pareto.cpp -o ./pareto17336
./pareto17336 and 8
./pareto17336 and 8 9
```

To reproduce all 77 records in the order used in `replay-results.txt`, run this after compiling.

```sh
for first in "or 8" "and 8" "not 5" "and 6" "and 7" "or 6" "or 7"; do
    set -- $first
    ./pareto17336 "$1" "$2"
    for feature in 9 0 1 2 3 4 5 6 7 8; do
        ./pareto17336 "$1" "$2" "$feature"
    done
done | diff - replay-results.txt
```
