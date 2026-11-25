# A 189-leaf ordinary-resolution tree for PHP(5,4)

`Tree377.lean` proves `Row169.refutation377` and `Row169.tree377`. The latter constructs the empty clause in any family of predicates closed under the ordinary axiom and resolution rules, with exactly 189 leaves. `PureTree189.lean` instantiates the predicate with the separately defined `Row169.OrdinaryTree.PureTree` and proves `Row169.pureTree189`. The trace has 65 pigeon-axiom occurrences, 124 collision-axiom occurrences, and 188 resolution occurrences. Each of the 376 non-root lines is used exactly once.

Prepare the pinned upstream Lean project as described in the [Hall witness instructions](../../witness/README.md). From this directory run

```sh
./replay.sh path/to/upstream/lean
```

Replay verifies the hashes, uses the shared generator to check the parent occurrences and regenerate the source byte for byte, checks all three theorems in the standard kernel, and prints their axiom lists.
