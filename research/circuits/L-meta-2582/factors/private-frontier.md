# Charging private frontier gates

Let a safe binary conjunction block have an OR-clause frontier. Let $t$ be the number of active rows and let $E$ count their accepted incident pairs. Suppose the rows have degrees from 3 through $m$, inclusive, and two distinct ambient rows have at most one common neighbor. If $t\ge m$, replacing those accepted pairs by their row stars fits the block's private gate budget whenever at most two frontier OR outputs must be retained. With no retained frontier output the saving is at least two gates, including when $t=m$.

The gate accounting uses physical wire IDs. The conjunction gates have unique IDs and every one of them is private. Each frontier wire is classified as a raw point input, a raw line input or the output of an OR gate. AND and OR gate IDs are disjoint. The external set must include every wire the surviving circuit needs, including transitive dependencies of retained gates. Inner OR subcircuits can be shared freely. Counting only frontier OR outputs makes the bound independent of the cost of those inner subcircuits.

* `all_or` proves that every frontier wire is an OR output. A point input misses the accepted edges of a different row. A line input misses one of the two or more accepted lines in any row.
* `dense_private` uses the backwards conjunction graph and the factor bound in `FactorCount.lean`. If the frontier has $F$ distinct outputs, the graph needs at least $F-1$ conjunction gates. At least $F-s$ frontier OR outputs are private, where $s$ is the number of frontier IDs in the external set. The factor bound yields $F\ge 1+t+\binom{t}{2}$, giving at least $t^2+t+1-s$ private gates.
* `star_budget` compares that charge with the $E+t-1$ gates of the row-star construction. The inequality $E\le tm\le t^2$ gives $E+t-1+2\le\text{private gates}+s$.

To apply this result to the replacement of a top-level disjunct, take the rows to include **all** its accepted pair supports and use `FactorCount.replaceAtTop` for the function identity. Constructing, reindexing and pruning an upstream `Circuit`, and proving the resulting circuit's read bound, require a further implementation. The theorem directly treats the abstract `Join` program, the explicit gate classifications and the set of wires marked external.

Run the package-level replay to compile these results against the pinned project.
