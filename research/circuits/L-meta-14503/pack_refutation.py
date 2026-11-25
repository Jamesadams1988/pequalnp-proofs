"""Assemble a Defs-only diagnostic for the official checker's refute mode."""
import argparse
from hashlib import sha256
from pathlib import Path

ROW = "PEqualNP.Outside.L_meta_14503"


def helper(upstream, module, digest, namespace, end_marker, label):
    path = upstream / "lean/PEqualNP/Outside" / (module + ".lean")
    data = path.read_bytes()
    if sha256(data).hexdigest() != digest:
        raise ValueError(f"Unexpected source version for {module}")
    source = data.decode()
    begin = f"namespace PEqualNP.Outside.{namespace}\n"
    prefix, found, rest = source.partition(begin)
    body, ended, _ = rest.partition(end_marker)
    if not found or not ended or prefix.count("import PEqualNP.Defs") != 1:
        raise ValueError(f"Unexpected module structure for {module}")
    return f"namespace {ROW}.{label}\n{body}\nend {ROW}.{label}\n"


def assemble(upstream, research, statement):
    eliminate = helper(upstream, "L_meta_4795",
        "5e85e410b1778e17b12481072680e6bdc76b5a8de2aa1d9ac6d69d1ee1c43c33",
        "L_meta_4795_aux", "/-! Section 2:", "Elimination")
    clique = helper(upstream, "L_meta_9526",
        "f0b349c8769119a77e899f1dcf0027f3f08e784994841d27ee59006ae631e838",
        "L_meta_9526", "def edgesG ", "FourClique")
    theorem = research.read_text()
    if f"theorem assignedStatementFalse : ¬ ({statement})" not in theorem:
        raise ValueError("The source must refute the literal assignment")
    theorem = "\n".join(line for line in theorem.splitlines()
                        if not line.startswith(("import ", "#print axioms ")))
    theorem = theorem.replace("PEqualNP.Outside.L_meta_4795_aux", ROW + ".Elimination")
    theorem = theorem.replace("PEqualNP.Outside.L_meta_9526", ROW + ".FourClique")
    theorem = theorem.replace("L14503Exact", ROW + ".Research")
    credits = ("-- Circuit elimination from nicohabets's L-meta-4795, crediting sanchan's L-meta-927.\n"
               "-- Four-clique certificate from hilelyos's L-meta-9526.\n"
               "-- Eight-vertex restriction proof and diagnostic by James Adams.\n")
    target = f"theorem {ROW} : ¬ ({statement}) :=\n  {ROW}.Research.assignedStatementFalse\n"
    return "\n".join(["import PEqualNP.Defs", credits, eliminate, clique, theorem, target])


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("upstream", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    result = assemble(args.upstream, here / "ExactMinimum.lean", (here / "statement.txt").read_text())
    with args.output.open("x", encoding="utf-8") as output:
        output.write(result)
