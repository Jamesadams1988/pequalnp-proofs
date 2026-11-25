"""Write the assigned row masks and a JSON donor's mask pairs for exchange.cpp."""
import ast
import json
from pathlib import Path
import re
import sys

root = Path(__file__).resolve().parent
statement = json.loads((root / "assignment.json").read_text())["statement"]
rows = ast.literal_eval(re.search(r"\[\d+[^\]]*\]", statement)[0])
boxes = json.loads(Path(sys.argv[1]).read_text())
print(*rows)
for row_mask, column_mask in boxes:
    if not all(type(x) is int and 0 <= x < (1 << len(rows)) for x in (row_mask, column_mask)):
        raise ValueError("invalid rectangle mask")
    print(row_mask, column_mask)
