"""Make one visible PEqualNP package containing the selected compiled modules."""
import os
from pathlib import Path
import sys

destination = Path(sys.argv[1]).resolve()
mode = sys.argv[2]
if mode not in ("yes", "no", "upper"):
    raise SystemExit("expected yes, no, or upper")
reuse_cases = mode == "yes"
paths = [Path(value).resolve() for value in os.environ["LEAN_PATH"].split(os.pathsep) if value]
packages = [path / "PEqualNP" for path in paths if path != destination and (path / "PEqualNP").is_dir()]
package = destination / "PEqualNP"
outside = package / "Outside"
outside.mkdir(parents=True, exist_ok=True)


def link(source, target):
    if not target.exists() and not target.is_symlink():
        target.parent.mkdir(parents=True, exist_ok=True)
        target.symlink_to(source.resolve(), target_is_directory=source.is_dir())


defs = next((p for p in packages if (p / "Defs.olean").is_file() and (p / "Defs").is_dir()), None)
if defs is None:
    raise SystemExit("build PEqualNP.Defs before running the replay")
for source in [defs / "Defs", *defs.glob("Defs.*")]:
    link(source, package / source.name)

if mode == "upper":
    raise SystemExit(0)

helper = Path("MetaComplexity/Helpers")
shannon = next((p / helper for p in packages if (p / helper / "Shannon.olean").is_file()), None)
if shannon is None:
    raise SystemExit("build PEqualNP.MetaComplexity.Helpers.Shannon before running the replay")
for source in shannon.glob("Shannon.*"):
    link(source, package / helper / source.name)

if reuse_cases:
    modules = [534,17107,17103,17269,17271,17273,17275,17277,17279,17281,17283]
    for number in modules:
        stem = f"L_meta_{number}"
        base = next((p / "Outside" for p in packages if (p / "Outside" / (stem + ".olean")).is_file()), None)
        if base is None:
            raise SystemExit(f"missing prebuilt PEqualNP.Outside.{stem}")
        for source in base.glob(stem + ".*"):
            link(source, outside / source.name)
    for p in packages:
        split = p / "Outside" / "Split17103"
        if split.is_dir():
            link(split, outside / split.name)
