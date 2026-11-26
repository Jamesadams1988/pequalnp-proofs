"""Print the ordered bipartite graph recorded in the assigned Lean proposition."""
import json
import re
from pathlib import Path
s = json.loads((Path(__file__).resolve().parents[1]/"assignment.json").read_text())["statement"]
pairs = [(int(a),int(b)) for a,b in re.findall(r"\((\d+), (\d+)\)", s)]
if len(pairs) != 51 or len(set(pairs)) != 51 or not all(0 <= a < 13 <= b < 26 for a,b in pairs):
    raise ValueError("unexpected graph")
print(13,13,len(pairs))
for a,b in pairs:
    print(a,b)
