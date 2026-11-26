"""Generate modules from the pinned L_meta_17103 source without editing its declarations."""
import argparse
import hashlib
import json
from pathlib import Path
import re

EXPECTED_HASH = "a654cdd548538c5a0a6d9444a2e101052b446d240443570a939dcd9d2a68ab01"
NAMESPACE = "PEqualNP.Outside.L_meta_17103"


def generate(source, destination):
    data = source.read_bytes()
    if hashlib.sha256(data).hexdigest() != EXPECTED_HASH:
        raise ValueError("source differs from the pinned donor")
    lines = data.decode().splitlines(keepends=True)
    # The checked boundaries are one-based and inclusive. Every appended
    # wrapper closes scopes, and the next module restores the same local context.
    setup = [7, 97, 187, 298, 366, 448, 500, 599, 621]
    parts = [(a, b - 1, "", "") for a, b in zip(setup, setup[1:])]
    hz = "".join(lines[620:622])
    end_hz = lines[874]
    declarations = [n for n in range(671, 875) if re.match(r"(lemma|theorem) ", lines[n-1])]
    starts = [623]
    for n in declarations:
        while lines[n-2].startswith("set_option ") and lines[n-2].rstrip().endswith(" in"):
            n -= 1
        starts.append(n)
    for first, stop in zip(starts, starts[1:] + [875]):
        parts.append((first, stop - 1, hz, end_hz))
    # Only one variable declaration is live at these root-scope boundaries.
    # The final block includes the original namespace close and exported theorem.
    boundaries = [876, 1204, 1544, 1869, 2153, 2613, 2994, 3328, 3705, 3867,
                  4345, 4637, 4992, 5336, 5554, 5928, 6327, len(lines) + 1]
    for first, stop in zip(boundaries, boundaries[1:]):
        parts.append((first, stop - 1, "" if first == 876 else lines[885], ""))

    destination.mkdir(parents=True, exist_ok=True)
    module_dir = destination / "PEqualNP" / "Outside" / "Split17103"
    module_dir.mkdir(parents=True, exist_ok=True)
    manifest = []
    previous = "PEqualNP.Defs"
    for number, (first, last, reopen, close) in enumerate(parts):
        module = f"PEqualNP.Outside.Split17103.P{number:03}"
        body = "".join(lines[first-1:last])
        header = "".join(lines[:6]) if number == 0 else f"import {previous}\nnamespace {NAMESPACE}\n"
        footer = "" if last == len(lines) else f"end {NAMESPACE}\n"
        # The first and last hz20 wrappers copy original section lines as well.
        text = header + reopen + body + close + footer
        path = module_dir / f"P{number:03}.lean"
        path.write_bytes(text.encode("utf-8"))
        manifest.append({"module": module, "first": first, "last": last,
                         "body_sha256": hashlib.sha256(body.encode()).hexdigest(),
                         "body_offset": len((header + reopen).encode()), "body_length": len(body.encode()),
                         "module_sha256": hashlib.sha256(text.encode()).hexdigest()})
        previous = module
    wrapper = destination / "PEqualNP" / "Outside" / "L_meta_17103.lean"
    wrapper.parent.mkdir(parents=True, exist_ok=True)
    wrapper.write_text(f"import {previous}\n#print axioms {NAMESPACE}\n")
    encoded_manifest = (json.dumps(manifest, indent=2) + "\n").encode()
    expected = json.loads(Path(__file__).with_name("observed.json").read_text())
    if hashlib.sha256(encoded_manifest).hexdigest() != expected["generated_manifest_sha256"]:
        raise ValueError("generated module manifest differs from the checked replay")
    (destination / "manifest.json").write_bytes(encoded_manifest)
    # Independently reread the generated files, strip their new import/scope
    # wrappers, and reconstruct the exact original bytes. The two original
    # section delimiters occur in every hz20 submodule; retain each once.
    recovered = bytearray()
    for entry in manifest:
        path = destination.joinpath(*entry["module"].split(".")).with_suffix(".lean")
        payload = path.read_bytes()
        offset, length = entry["body_offset"], entry["body_length"]
        if entry["first"] == 7:
            recovered.extend(payload[:offset])
        if entry["first"] == 623:
            recovered.extend(payload[offset-len(hz.encode()):offset])
        recovered.extend(payload[offset:offset + length])
        if entry["last"] == 874:
            recovered.extend(payload[offset + length:offset + length + len(end_hz.encode())])
    if hashlib.sha256(recovered).hexdigest() != EXPECTED_HASH:
        raise ValueError("reassembled source differs from the original")
    final = lines[-2]
    start = f"theorem {NAMESPACE} : "
    if not final.startswith(start) or not final.endswith(" :=\n"):
        raise ValueError("unexpected exported theorem declaration")
    (destination / "donor.statement").write_text(final[len(start):-4] + "\n")
    return manifest


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("destination", type=Path)
    args = parser.parse_args()
    print(f"Generated {len(generate(args.source, args.destination))} modules")
