#!/usr/bin/env python3
"""Rebuild the single-file L-meta-13646 diagnostic from hash-pinned Lean sources.

Usage: python3 pack_refutation.py /path/to/pequalnp-proofs /tmp/L_meta_13646.lean
The assigned upstream revision is b0bb9eaa703fa256d5ebc1540bc1d419f160e57c.
Keep CofactorBound.lean and statement.txt alongside this script. The output
must be a new file. Use the official checker in refute mode.
"""

import argparse
from hashlib import sha256
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROW = "PEqualNP.Outside.L_meta_13646"
DEFS = "import PEqualNP.Defs"
ELIM = "PEqualNP.Outside.L_meta_4795_aux"
FIVE = "PEqualNP.Outside.L_meta_8657"


def checked_text(path, expected):
    data = path.read_bytes()
    actual = sha256(data).hexdigest()
    if actual != expected:
        raise ValueError(f"{path}: expected SHA-256 {expected}, got {actual}")
    return data.decode("utf-8")


def excerpt(source, namespace, next_declaration, local_name):
    """Copy the source through the last needed theorem, retaining header credits."""
    head, body = source.split(f"namespace {namespace}\n", 1)
    imports = [line for line in head.splitlines() if line.startswith("import ")]
    if imports != ["import Mathlib", DEFS]:
        raise ValueError(f"unexpected imports in {namespace}")
    credits = "\n".join(line for line in head.splitlines() if line not in imports).strip()
    prefix, _ = body.split("\n" + next_declaration, 1)
    return f"{credits}\n\nnamespace {local_name}\n{prefix.rstrip()}\n\nend {local_name}".strip()


def assemble(upstream):
    outside = upstream / "lean" / "PEqualNP" / "Outside"
    eliminate = checked_text(outside / "L_meta_4795.lean",
        "5e85e410b1778e17b12481072680e6bdc76b5a8de2aa1d9ac6d69d1ee1c43c33")
    five = checked_text(outside / "L_meta_8657.lean",
        "03fac36312d27e81e651bf4222042a4d6cc80411ea9762b2d7c54394a31410ae")
    research = checked_text(HERE / "CofactorBound.lean",
        "9e145b6f7dae0cb498f627d59411f7fb52517f73820173f92e0a7551a73a77d9")
    statement = checked_text(HERE / "statement.txt",
        "3b7d539d97600a31e9f038243dbf56163fa077124f40ca6648ea5baecefe085c")
    if research.count(f"theorem assignedStatementFalse : ¬ ({statement}) := by\n") != 1:
        raise ValueError("CofactorBound.lean must refute the literal assignment in statement.txt")

    lines = research.splitlines()
    imports = [line for line in lines if line.startswith("import ")]
    if imports != ["import PEqualNP.Outside.L_meta_4795", f"import {FIVE}"]:
        raise ValueError("unexpected imports in CofactorBound.lean")
    research = "\n".join(line for line in lines if line not in imports
                         and not line.startswith("#print axioms ")).strip()
    research = research.replace(ELIM, ROW + ".Elimination").replace(FIVE, ROW + ".FiveInput")
    research = research.replace("namespace CofactorBound\n", f"namespace {ROW}.Research\n")
    research = research.replace("end CofactorBound", f"end {ROW}.Research")

    sections = [
        DEFS,
        "/-! L-meta-13646 refutation diagnostic by James Adams.\n"
        "Gate elimination and relabeling come from Nico Habets (nicohabets), "
        "L-meta-4795 (#9322),\n"
        "drawing on sanchan's L-meta-927 (#1992). The five-input lower bound "
        "comes from Noptus,\nL-meta-8657 (#12814). -/",
        excerpt(eliminate, ELIM, "theorem gate_elim_at ", ROW + ".Elimination"),
        excerpt(five, FIVE, "def witness : Circuit", ROW + ".FiveInput"),
        research,
        f"theorem {ROW} : ¬ ({statement}) :=\n  {ROW}.Research.Row13646.assignedStatementFalse",
    ]
    result = "\n\n".join(sections) + "\n"
    if [line for line in result.splitlines() if line.startswith("import ")] != [DEFS]:
        raise ValueError("assembled diagnostic must import only PEqualNP.Defs")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("upstream", type=Path, help="root of the upstream source checkout")
    parser.add_argument("output", type=Path, help="new path for the assembled Lean source")
    args = parser.parse_args()
    try:
        source = assemble(args.upstream)
        with args.output.open("xb") as output:
            output.write(source.encode("utf-8"))
    except (OSError, ValueError) as error:
        parser.exit(1, f"{parser.prog}: {error}\n")


if __name__ == "__main__":
    main()
