"""Read the two Lean circuit literals and print an auditable comparison as JSON."""
import argparse
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
TARGET = (4269866496 << 32) + 4261472256
GATE = r'⟨\s*\.(and|or)\s*,\s*\[\s*(\d+)\s*,\s*(\d+)\s*\]\s*⟩'


def parse(source, name):
    gate_list = rf'(?P<gates>{GATE}(?:\s*,\s*{GATE})*)'
    pattern = (rf'^def {re.escape(name)}\s*:\s*Circuit\s*:=\s*⟨\s*\[\s*'
               + gate_list + r'\s*\]\s*,\s*(?P<output>\d+)\s*⟩')
    declarations = list(re.finditer(pattern, source, re.MULTILINE))
    if len(declarations) != 1:
        raise ValueError(f'Expected one complete binary AND/OR circuit literal for {name}')
    match = declarations[0]
    return [(op, int(a), int(b)) for op, a, b in re.findall(GATE, match['gates'])], int(match['output'])


def check(author, filename, name):
    raw = filename.read_bytes()
    gates, output = parse(raw.decode(), name)
    depths = [0] * 6
    for op, a, b in gates:
        assert 0 <= a < len(depths) and 0 <= b < len(depths)
        depths.append(1 + max(depths[a], depths[b]))
    assert 0 <= output < len(depths)
    bits = []
    for row in range(64):
        wires = [(row >> i) & 1 for i in range(6)]
        for op, a, b in gates:
            wires.append(wires[a] & wires[b] if op == 'and' else wires[a] | wires[b])
        bits.append(wires[output])
    table = sum(bit << row for row, bit in enumerate(bits))
    assert table == TARGET
    return {'author': author, 'source': filename.name, 'source_sha256': hashlib.sha256(raw).hexdigest(),
            'lean_definition': name, 'gate_count': len(gates), 'output_wire': output,
            'output_depth': depths[output], 'truth_table_hex': f'0x{table:016x}',
            'outputs_rows_0_to_63': ''.join(map(str, bits))}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('merged_source', type=Path, help='path to the merged L_meta_12096.lean')
    args = parser.parse_args()
    results = [
        check('edmoreno', args.merged_source, 'smallCircuit'),
        check('James Adams', HERE / 'ThresholdCircuit.lean', 'witness'),
    ]
    print(json.dumps({'row': 'L-meta-12096', 'inputs': 6,
                      'row_order': 'row = sum(x[i] * 2**i); bit row of truth_table_hex is the output',
                      'depth_convention': 'input depth 0; gate depth 1 + maximum operand depth',
                      'assigned_mask': f'0x{TARGET:016x}', 'witnesses': results}, indent=2))
