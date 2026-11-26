#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")" && pwd)
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
cd "$root"
python3 -B upper/construct.py | diff -u upper/expected.txt -
c++ -std=c++20 -O3 depth-test/full.cpp -o "$build/full"
"$build/full" | diff -u depth-test/full-expected.txt -
c++ -std=c++20 -O3 depth-test/samples.cpp -o "$build/samples"
"$build/samples" | diff -u depth-test/expected.txt -
python3 -B depth-test/witnesses.py
python3 -B depth-test/independent.py | diff -u depth-test/independent-expected.txt -
c++ -std=c++20 -O3 formulas/residual.cpp -o "$build/residual"
python3 -B formulas/verify.py "$build/residual"
c++ -std=c++20 -O3 formulas/first-wire/first.cpp -o "$build/first"
python3 -B formulas/first-wire/verify.py "$build/first"
