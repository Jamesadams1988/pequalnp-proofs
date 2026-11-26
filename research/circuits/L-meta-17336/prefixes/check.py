"""Compile the checker, rerun all prefixes, and compare every leaf count."""
import argparse
import collections
import concurrent.futures
import os
from pathlib import Path
import subprocess
import tempfile

PREFIXES = [(0, 5), (1, 6), (1, 7), (1, 8), (2, 6), (2, 7), (2, 8)]
HERE = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=1)
    args = parser.parse_args()
    if not 1 <= args.jobs <= 7:
        parser.error("--jobs must be between 1 and 7")
    reference = (HERE / "expected.txt").read_text().splitlines()
    if len(reference) != len(PREFIXES) * 101:
        raise ValueError("invalid expected table size")
    with tempfile.TemporaryDirectory() as temp:
        executable = Path(temp) / "two_prefix"
        subprocess.run([os.environ.get("CXX", "c++"), "-std=c++20", "-O3",
                        "-march=native", str(HERE / "two_prefix.cpp"),
                        "-o", str(executable)], check=True)

        def run(prefix):
            first, rhs = prefix
            result = subprocess.run([str(executable), str(first), str(rhs)],
                                    capture_output=True, text=True, check=True)
            return result.stdout.splitlines()

        with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
            for i, (prefix, rows) in enumerate(zip(PREFIXES, pool.map(run, PREFIXES))):
                if rows != reference[101*i:101*(i+1)]:
                    raise RuntimeError(f"prefix {prefix} differs from expected.txt")
                histogram = collections.Counter(int(row.split()[3]) for row in rows[1:])
                print(f"{prefix}: {dict(sorted(histogram.items()))}", flush=True)
    print("Verified all 700 two-gate prefixes.")


if __name__ == "__main__":
    main()
