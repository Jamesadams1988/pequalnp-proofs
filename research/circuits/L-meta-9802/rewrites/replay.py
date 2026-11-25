"""Run exact circuit rewrites. Pass --full to reproduce all 64 layouts."""
import argparse
import itertools
from pathlib import Path
import re
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
SEEDS = [0, 4201, 9802, 19604, *range(1, 13)]

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--full', action='store_true')
    args = parser.parse_args()
    with tempfile.TemporaryDirectory() as tmp:
        executable = str(Path(tmp) / 'contextual')
        subprocess.run(['c++', '-std=c++20', '-O3', '-Wall', 'contextual.cpp',
                        '-o', executable], cwd=HERE, check=True)
        def test(*arguments):
            return subprocess.check_output([executable, *map(str, arguments)], cwd=HERE, text=True)
        positive = test(0, 1, 0, 'positive')
        if 'improvement=1' not in positive or 'three found' not in positive:
            raise RuntimeError(f'Positive controls failed: {positive}')
        print(positive.strip())
        layouts = 0
        counts = [0] * 4
        for seed in SEEDS if args.full else [0]:
            for orientation, shape in itertools.product([0, 1], repeat=2):
                result = test(orientation, shape, seed)
                match = re.fullmatch(r'orientation=\d balanced=\d seed=\d+ nodes=114 '
                                     r'mintrue=95 maxfalse=16870 windows=([0-9,]+) '
                                     r'improvement=0\n', result)
                if not match:
                    raise RuntimeError(result)
                for k, number in enumerate(map(int, match[1].split(','))):
                    counts[k] += number
                layouts += 1
        expected = [7296, 7232, 8960, 12256] if args.full else [456, 452, 560, 766]
        if counts != expected:
            raise RuntimeError(f'Unexpected window counts: {counts}')
        print(f'{layouts} layouts, {sum(counts)} windows, no improvement. '
              f'Counts by size: {counts}.')

if __name__ == '__main__':
    main()
