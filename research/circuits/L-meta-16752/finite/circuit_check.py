"""Replay the unrestricted core search and check both circuit constructions.

core_search.cpp is the unchanged local L-meta-13646/test/search.cpp enumerator.
Use `python3 circuit_check.py`; the build lives in a temporary directory.
"""
from pathlib import Path
from subprocess import run
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
TARGET = (4276809450 << 32) + 4276808362
CORE = 0xE8A8E880

# Upstream PEqualNP.Outside.L_meta_8642.witness. Wire 6 has two consumers.
CORE_GATES = [('|', 1, 2), ('&', 1, 2), ('|', 4, 6), ('&', 0, 5),
              ('|', 6, 8), ('&', 0, 7), ('|', 3, 10), ('&', 9, 11)]
# Independently obtained by partitioning the extremal true and false rows.
TREE_GATES = [('|', 4, 5), ('&', 6, 1), ('|', 2, 3), ('&', 7, 8),
              ('|', 0, 9), ('&', 3, 2), ('|', 1, 4), ('&', 11, 12), ('|', 10, 13)]


def truth(n, gates):
    """Evaluate each gate for every row, indexing input 0 by the low bit."""
    table = 0
    for r in range(1 << n):
        wires = [(r >> i) & 1 for i in range(n)]
        for op, a, b in gates:
            assert op in ('&', '|') and 0 <= a < len(wires) and 0 <= b < len(wires)
            wires.append(wires[a] & wires[b] if op == '&' else wires[a] | wires[b])
        table |= wires[-1] << r
    return table


def main():
    lifted = [(op, a + 1, b + 1) for op, a, b in CORE_GATES] + [('|', 0, 13)]
    assert len(CORE_GATES) == 8 and truth(5, CORE_GATES) == CORE
    assert len(TREE_GATES) == len(lifted) == 9
    assert truth(6, TREE_GATES) == truth(6, lifted) == TARGET
    assert sum(((TARGET >> (2*r)) & 1) << r for r in range(32)) == CORE
    assert all((TARGET >> (2*r + 1)) & 1 for r in range(32))
    assert (TARGET & 3) == 2  # pin coordinate 0 is essential
    print(f'Core = 0x{CORE:08x}; target = 0x{TARGET:016x}.')
    print('Both monotone nine-gate witnesses match every row. Pin x0=false gives the core; x0=true gives constant true.')
    with TemporaryDirectory() as tmp:
        exe = str(Path(tmp) / 'core_search')
        run(['c++', '-O3', '-std=c++20', str(HERE / 'core_search.cpp'), '-o', exe], check=True)
        result = run([exe, '5', '7', hex(CORE)], check=True, capture_output=True, text=True)
    assert result.stdout.split() == [str(CORE), '-1']
    print(result.stderr, end='')
    print('No unrestricted core witness through seven gates; exact core minimum is eight.')
    print('Essential-input gate elimination then gives exact unrestricted and monotone six-input minima of nine.')


if __name__ == '__main__':
    main()
