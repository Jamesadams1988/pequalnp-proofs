#!/usr/bin/env python3
"""Assemble a standalone certificate from the hash-pinned research and upstream proofs.

Place ExactMinimum.lean and statement.txt next to this script. Run
  python3 pack_proof.py /path/to/pequalnp-proofs /tmp/L_meta_15250.lean
for the refutation diagnostic. Choose L_meta_15249.lean for the positive proof.
The output file must be new.
"""

import argparse
from hashlib import sha256
from pathlib import Path


HERE = Path(__file__).resolve().parent
DEFS = "import PEqualNP.Defs"
ELIM = "PEqualNP.Outside.L_meta_4795_aux"
FIVE = "PEqualNP.Outside.L_meta_8650_aux"


def checked_text(path, digest):
    data = path.read_bytes()
    actual = sha256(data).hexdigest()
    if actual != digest:
        raise ValueError(f"{path}: expected SHA-256 {digest}, got {actual}")
    return data.decode("utf-8")


def excerpt(source, namespace, stop, new_namespace):
    """Retain original author credits and the declarations through the required lemma."""
    head, tail = source.split(f"namespace {namespace}\n", 1)
    imports = "import Mathlib\n" + DEFS + "\n"
    if not head.startswith(imports):
        raise ValueError(f"unexpected imports in {namespace}")
    credits = head[len(imports):].strip()
    body, _ = tail.split("\n" + stop, 1)
    return f"{credits}\n\nnamespace {new_namespace}\n{body.rstrip()}\n\nend {new_namespace}"


def assemble(upstream, filename):
    if filename not in {"L_meta_15249.lean", "L_meta_15250.lean"}:
        raise ValueError("output file must be L_meta_15249.lean or L_meta_15250.lean")
    diagnostic = filename == "L_meta_15250.lean"
    namespace = f"PEqualNP.Outside.{Path(filename).stem}"
    outside = upstream / "lean" / "PEqualNP" / "Outside"
    elim_source = checked_text(outside / "L_meta_4795.lean",
        "5e85e410b1778e17b12481072680e6bdc76b5a8de2aa1d9ac6d69d1ee1c43c33")
    five_source = checked_text(outside / "L_meta_8650.lean",
        "db130f124d2d40de6a6c055c44d7b0cea22f3bcc7121a777e9aa68b263716a4f")
    research = checked_text(HERE / "ExactMinimum.lean",
        "679c332f8b2bff9ecc7e0d8de4bfd029690f3557230768debbcbb8903a324a67")
    statement = checked_text(HERE / "statement.txt",
        "11f28158ee4f5a22570f93e4073c3b90151cce94387350fd3a12eba6a7086b4a")
    if not (statement.startswith("¬ (") and statement.endswith(")")):
        raise ValueError("expected the posted negative statement")
    positive = statement[len("¬ ("):-1]

    # Keep the one-gate elimination and relabeling proofs. The intervening
    # two-gate elimination argument is independent and unused here.
    elim_name, five_name = namespace + ".Elimination", namespace + ".FiveInput"
    eliminate = excerpt(elim_source, ELIM, "theorem gate_elim_at ", elim_name)
    before, rest = eliminate.split("\ntheorem simplify_const ", 1)
    _, after = rest.split("\ndef wmap ", 1)
    eliminate = before + "\ndef wmap " + after
    five = excerpt(five_source, FIVE, "def witnessCircuit ", five_name)

    imports = "import PEqualNP.Outside.L_meta_4795\nimport PEqualNP.Outside.L_meta_8650\n"
    if not research.startswith(imports):
        raise ValueError("unexpected research dependencies")
    research_name = namespace + ".Certificate"
    research = research[len(imports):].strip()
    research = research.replace(ELIM, elim_name).replace(FIVE, five_name)
    research = research.replace("namespace Row15250\n", f"namespace {research_name}\n")
    body, rest = research.split(f"\ntheorem assignedStatementFalse : ¬ ({statement}) := by\n", 1)
    proof, _ = rest.split("\nend Row15250\n", 1)
    preamble = "  intro claim\n  apply claim\n"
    if not proof.startswith(preamble):
        raise ValueError("could not locate the constructive positive proof")

    body += f"\nend {research_name}"
    wanted = f"¬ ({statement})" if diagnostic else positive
    proof = proof if diagnostic else proof[len(preamble):]
    final = f"open {research_name} in\ntheorem {namespace} : {wanted} := by\n{proof.rstrip()}"
    credits = (
        "/-! Six-input cofactor proof by James Adams. The eight-gate witness is equivalent\n"
        "to the earlier circuit by edisonhello (PR 20398).\n"
        "Gate elimination and relabeling are from Nico Habets (nicohabets), L-meta-4795\n"
        "(PR 9322), drawing on sanchan's L-meta-927 (PR 1992). The five-input lower\n"
        "bound is from scott-cmd11's L-meta-8650 (PR 12798), adapted from L-meta-1421\n"
        "and the live-wire checker by ljste and jfsantoropereira. -/"
    )
    sections = [DEFS, credits, eliminate, five, body, final]
    return "\n\n".join(sections) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("upstream", type=Path, help="root of the upstream source checkout")
    parser.add_argument("output", type=Path, help="new path for the assembled Lean source")
    args = parser.parse_args()
    try:
        source = assemble(args.upstream, args.output.name)
        with args.output.open("xb") as output:
            output.write(source.encode("utf-8"))
    except (OSError, ValueError) as error:
        parser.exit(1, f"{parser.prog}: {error}\n")


if __name__ == "__main__":
    main()
