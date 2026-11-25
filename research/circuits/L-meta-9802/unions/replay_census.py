"""Regenerate and compare the published Lean neighborhood-union certificates.

The default run uses a temporary directory. Supply --output DIR to keep the
regenerated files. The destination must have neither generated filename.
"""
import argparse
import hashlib
from pathlib import Path
from tempfile import TemporaryDirectory


PUBLISHED = Path(__file__).resolve().parent
FILES = ("UnionRows.lean", "UnionData.lean")


def read_rows(edge_file):
    edges = [tuple(map(int, line.split())) for line in edge_file.read_text().splitlines() if line.strip()]
    if len(set(edges)) != 95 or len(edges) != 95:
        raise ValueError("expected 95 distinct edges")
    if not all(0 <= point < 20 <= line < 40 for point, line in edges):
        raise ValueError("edge endpoints must be in the two specified parts")
    return [sum(1 << (line - 20) for point, line in edges if point == index)
            for index in range(20)]


def representatives(rows):
    # At step i the dictionary contains exactly the unions of the first i rows.
    # Every such union either keeps or omits the newly introduced row.
    witness = {0: 0}
    for index, row in enumerate(rows):
        added = {mask | row: points | (1 << index) for mask, points in witness.items()}
        witness.update(added)
    return sorted(witness.items())


def write_certificate(entries, output):
    block_size = 96
    records = []
    output.write('import UnionBlocks\nnamespace Row9802.Unions\n')
    output.write('set_option maxRecDepth 50000\nset_option maxHeartbeats 0\n')
    for index, start in enumerate(range(0, len(entries), block_size)):
        end = min(start + block_size, len(entries))
        group = entries[start:end]
        lo = group[0][0]
        hi = entries[end][0] if end < len(entries) else 2**20
        name = f'b{index}'
        records.append((lo, hi, len(group), name))
        words = [word for _, word in group]
        output.write(f'\ndef {name} : Block {lo} {hi} {len(group)} :=\n')
        output.write(f'  ofCheck {words!r} (by decide +kernel) (by decide +kernel)\n')

    level = 0
    while len(records) > 1:
        merged = []
        for index in range(0, len(records), 2):
            if index + 1 == len(records):
                merged.append(records[index])
                continue
            lo, mid, left_count, left = records[index]
            next_lo, hi, right_count, right = records[index + 1]
            assert mid == next_lo
            count = left_count + right_count
            name = f'm{level}_{index // 2}'
            output.write(f'def {name} : Block {lo} {hi} {count} := merge {left} {right}\n')
            merged.append((lo, hi, count, name))
        records = merged
        level += 1
    output.write(f'def all : Block 0 {2**20} {len(entries)} := {records[0][-1]}\n')
    output.write('end Row9802.Unions\n')



def regenerate(edge_file, destination):
    destination.mkdir(parents=True, exist_ok=True)
    for name in FILES:
        output = destination / name
        if output.exists() or output.is_symlink():
            raise FileExistsError(f"destination already contains {name}")
    rows = read_rows(edge_file)
    entries = representatives(rows)
    if len(entries) != 16870:
        raise ValueError(f"unexpected census: {len(entries)} unions")
    with (destination / FILES[0]).open('x', encoding='utf-8', newline='\n') as output:
        output.write('import Mathlib.Data.List.Pairwise\nnamespace Row9802.Unions\n\n')
        output.write(f'def rows : List Nat := {rows!r}\nend Row9802.Unions\n')
    with (destination / FILES[1]).open('x', encoding='utf-8', newline='\n') as output:
        write_certificate(entries, output)
    for name in FILES:
        data = (destination / name).read_bytes()
        if data != (PUBLISHED / name).read_bytes():
            raise RuntimeError(f"regenerated {name} differs from the published source")
        print(f"{name} matches ({hashlib.sha256(data).hexdigest()})")
    print(f"{len(entries)} distinct neighborhood unions")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--edges', type=Path, default=PUBLISHED.parent / 'rewrites' / 'edges.txt')
    parser.add_argument('--output', type=Path, help='directory for the two generated Lean sources')
    args = parser.parse_args()
    if args.output is None:
        with TemporaryDirectory() as scratch:
            regenerate(args.edges, Path(scratch))
    else:
        regenerate(args.edges, args.output)


if __name__ == '__main__':
    main()
