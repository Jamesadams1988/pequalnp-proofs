"""Build the adjacent 63-gate checker statement from the posted 62-gate question."""
import json
import sys
from pathlib import Path

here = Path(__file__).resolve().parent
dest = Path(sys.argv[1])
dest.mkdir(parents=True, exist_ok=True)
row = json.loads((here.parent / "assignment.json").read_text())
statement = row["statement"]
if row["id"] != "L-meta-9742" or not statement.startswith("¬ (∃ ") or not statement.endswith(")"):
    raise ValueError("unexpected desk statement")
original = statement[3:-1]
if original.count("C.size ≤ 62") != 1:
    raise ValueError("unexpected gate budget")
adjacent = original.replace("C.size ≤ 62", "C.size ≤ 63")
name = "PEqualNP.Outside.ForkUpper9742"
source = (here / "Upper63.lean").read_text()
if source.count("namespace ProjectiveEdge9742") != 1 or source.count("end ProjectiveEdge9742") != 1:
    raise ValueError("unexpected witness namespace")
source = source.replace("ProjectiveEdge9742", name)
source += f"""
theorem {name} : {adjacent} := by
  obtain ⟨C, mono, size, _, computes⟩ := {name}.upper
  exact ⟨C, mono, size.le, computes⟩
"""
module = dest / "source" / "PEqualNP" / "Outside" / "ForkUpper9742.lean"
module.parent.mkdir(parents=True, exist_ok=True)
module.write_text(source)
(dest / "upper63.txt").write_text(adjacent + "\n")
(dest / "control62.txt").write_text(original + "\n")
