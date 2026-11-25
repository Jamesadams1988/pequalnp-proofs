#!/usr/bin/env python3
"""Pack the assigned L-meta-15094 negative row's refutation diagnostic.

Keep ExactMinimum.lean and statement.txt beside this script. Run
  python3 pack_refutation.py /path/to/pequalnp-proofs /tmp/L_meta_15094.lean
and run the official checker in refute mode. The output must be a new file.
"""
import argparse
from hashlib import sha256
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROW = "PEqualNP.Outside.L_meta_15094"
ELIM = "PEqualNP.Outside.L_meta_4795_aux"
FIVE = "PEqualNP.Outside.L_meta_8637"
DEFS = "import PEqualNP.Defs"


def checked_text(path, digest):
    data = path.read_bytes()
    actual = sha256(data).hexdigest()
    if actual != digest:
        raise ValueError(f"{path}: expected SHA-256 {digest}, got {actual}")
    return data.decode("utf-8")


def assemble(upstream):
    outside = upstream / "lean/PEqualNP/Outside"
    elim = checked_text(outside / "L_meta_4795.lean",
        "5e85e410b1778e17b12481072680e6bdc76b5a8de2aa1d9ac6d69d1ee1c43c33")
    five = checked_text(outside / "L_meta_8637.lean",
        "f4368112226ad31cfcbce12f37a6f42b5d62ffbda92e84f6e3c769e2b90e2399")
    research = checked_text(HERE / "ExactMinimum.lean",
        "92da2f5f80986773167ca932c80c142fe69967884a5f12d82083644ae5cbc259")
    statement = checked_text(HERE / "statement.txt",
        "dde6d9559de38ffd373abbfa3e4d074dff3af4d23991f2e252ce3ad76e3c45a5")

    # Keep the one-gate proof and relabeling, omitting the two-gate proof.
    _, elim = elim.split(f"namespace {ELIM}\n", 1)
    first, rest = elim.split("\ntheorem simplify_const ", 1)
    _, relabel = rest.split("\ndef wmap ", 1)
    relabel, _ = relabel.split("\ntheorem gate_elim_at ", 1)
    elim = first.rstrip() + "\n\ndef wmap " + relabel.rstrip()

    # The checked table certificate s0Stock is the last helper in the donor's
    # namespace. Its positive row theorem and its upper-bound circuit are unused.
    _, five = five.split(f"namespace {FIVE}\n", 1)
    five, _ = five.split(f"\nend {FIVE}\n", 1)
    _, research = research.split("namespace Row15094\n", 1)
    research, _ = research.split("\nend Row15094\n", 1)
    if f"theorem assignedStatementFalse : ¬ ({statement}) := by\n" not in research:
        raise ValueError("research proof must refute the literal assigned statement")
    research = research.replace(ELIM, ROW + ".Elimination").replace(FIVE, ROW + ".FiveInput")

    credits = (
        "/-! Six-input factorization and cofactor proof by James Adams. The elimination\n"
        "and relabeling lemmas are from Nico Habets (nicohabets), L-meta-4795 (PR 9322),\n"
        "drawing on sanchan's L-meta-927 (PR 1992). The five-input certificate\n"
        "comes from odinfree's L-meta-8637 (PR 12773). Stasana666 (PR 19866) and\n"
        "nicohabets (PR 20007) previously supplied proofs of L-meta-15093. -/"
    )
    sections = [DEFS, credits]
    for name, body in [("Elimination", elim), ("FiveInput", five), ("Certificate", research)]:
        namespace = f"{ROW}.{name}"
        sections.append(f"namespace {namespace}\n\n{body.strip()}\n\nend {namespace}")
    sections.append(f"theorem {ROW} : ¬ ({statement}) :=\n  {ROW}.Certificate.assignedStatementFalse")
    return "\n".join(line.rstrip() for line in "\n\n".join(sections).splitlines()) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("upstream", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    try:
        source = assemble(args.upstream)
        with args.output.open("xb") as out:
            out.write(source.encode("utf-8"))
    except (ValueError, OSError) as error:
        parser.exit(1, f"{parser.prog}: {error}\n")


if __name__ == "__main__":
    main()
