"""Build the requested local Lean sources and their local imports in a fresh directory."""
from pathlib import Path
import os
import re
import subprocess
import sys
import tempfile

here = Path(__file__).resolve().parent
previous = here.parent / "L-meta-4201"
directories = [previous, here, here / "filters", here / "unions"]
sources = {}
for directory in directories:
    for source in sorted(directory.glob("*.lean")):
        if source.stem in sources:
            raise SystemExit(f"Duplicate local module {source.stem}")
        sources[source.stem] = source

targets = sys.argv[1:] or [name for name, source in sources.items() if source.parent != previous]
if not targets:
    raise SystemExit("No local Lean modules found")

def dependency_order(name, visited, order):
    if name in visited:
        return
    visited.add(name)
    source = sources[name]
    for dependency in re.findall(r"^import ([A-Za-z_][A-Za-z_0-9.]*)\s*$", source.read_text(), re.M):
        if dependency in sources:
            dependency_order(dependency, visited, order)
    order.append(source)

ordered = []
visited = set()
for target in targets:
    dependency_order(target, visited, ordered)
with tempfile.TemporaryDirectory(prefix="pg4-lean-") as build:
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join((build, env.get("LEAN_PATH", "")))
    for source in ordered:
        output = Path(build) / (source.stem + ".olean")
        print("Checking", source.stem, flush=True)
        subprocess.run(["lean", "-j1", "--root=" + str(source.parent),
                        "-o", str(output), str(source)], env=env, check=True)
