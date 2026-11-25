#!/usr/bin/env python3
"""Pack the six-input specialization of Scott Hazlitt's live-wire search.

Run python3 pack_proof.py /path/to/pequalnp-proofs /tmp/L_meta_15174.lean
for the negative row's refutation diagnostic. Choose L_meta_15173.lean
for the positive statement. Keep Nine.lean and statement.txt next to this
script. The checkout argument is accepted for compatibility with the earlier
generator. Both inputs are read from this directory. The output must be new.
"""
import argparse
from hashlib import sha256
from pathlib import Path


HERE = Path(__file__).resolve().parent
DEFS = "import PEqualNP.Defs"
REVIEWED = "PEqualNP.Outside.Row15174Review"


def checked_text(path, digest):
    data = path.read_bytes()
    actual = sha256(data).hexdigest()
    if actual != digest:
        raise ValueError(f"{path}: expected SHA-256 {digest}, got {actual}")
    return data.decode("utf-8")


def assemble(filename):
    if filename not in {"L_meta_15173.lean", "L_meta_15174.lean"}:
        raise ValueError("output name must be L_meta_15173.lean or L_meta_15174.lean")
    diagnostic = filename == "L_meta_15174.lean"
    module = f"PEqualNP.Outside.{Path(filename).stem}"
    own = module + ".Certificate"

    source = checked_text(HERE / "Nine.lean",
        "da862e62b579e33c70b42a63dba70aa0ef25128c47b8f456a0cde975b2f4ca33")
    _, remaining = source.split(f"namespace {REVIEWED}\n", 1)
    body, audit = remaining.split(f"\nend {REVIEWED}\n", 1)
    if audit.strip() != f"#print axioms {REVIEWED}.exactMinimum":
        raise ValueError("unexpected final audit in Nine.lean")
    statement = checked_text(HERE / "statement.txt",
        "525d80eecc500cc8e2eb97d8eca5b6905a4d6beaa1d3897ebab681010db2b71b")
    if not (statement.startswith("¬ (") and statement.endswith(")")):
        raise ValueError("unexpected form of the posted statement")
    wanted = f"¬ ({statement})" if diagnostic else statement[len("¬ ("):-1]
    intro = "  intro claim\n  apply claim\n" if diagnostic else ""
    final = (
        f"open {own} in\ntheorem {module} : {wanted} := by\n"
        f"{intro}  intro s h\n"
        "  obtain ⟨bound, mono, size, computes⟩ := exactMinimum\n"
        "  exact ⟨nine, mono, size.le.trans (bound s h), computes⟩"
    )
    credits = (
        "/-! Six-input certificate by James Adams. The live-wire checker is adapted\n"
        "from Scott Hazlitt (scott-cmd11), L-meta-8650 (PR 12798), and L-meta-1421,\n"
        "which credits ljste (PR 2918) and jfsantoropereira (L-meta-1007). Apache-2.0.\n"
        "The nine-gate formula and the restriction to at most three NOT gates are\n"
        "checked below. The earlier proof by 2undvierzig (PR 20049) gives a different\n"
        "nine-gate circuit for this table. -/"
    )
    sections = [DEFS, credits, f"namespace {own}\n{body.rstrip()}\n\nend {own}", final]
    return "\n\n".join(sections) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("upstream", type=Path, help="checkout path retained for CLI compatibility")
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    try:
        data = assemble(args.output.name).encode("utf-8")
        with args.output.open("xb") as out:
            out.write(data)
    except (ValueError, OSError) as error:
        parser.exit(1, f"{parser.prog}: {error}\n")


if __name__ == "__main__":
    main()
