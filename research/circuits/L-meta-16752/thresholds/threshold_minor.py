"""Generate a Lean lower-bound transfer from a two-pin threshold restriction.

Bits are indexed by input rows in little-endian variable order. A pin is
eligible only if its variable is essential in the truth table at that step.
Requires Python 3.10 or later.
"""
import argparse
from dataclasses import dataclass


def cofactor(table, n, pin, value):
    low = (1 << pin) - 1
    result = 0
    for small in range(1 << (n - 1)):
        full = (small & low) | (value << pin) | ((small & ~low) << 1)
        result |= ((table >> full) & 1) << small
    return result


@dataclass(frozen=True)
class Pin:
    position: int
    value: int
    essential_row: int
    image: int


def eligible_pins(table, n):
    for p in range(n):
        a, b = (cofactor(table, n, p, v) for v in (0, 1))
        differing = a ^ b
        if differing:
            small = (differing & -differing).bit_length() - 1
            low = (1 << p) - 1
            row = (small & low) | ((small & ~low) << 1)
            yield Pin(p, 0, row, a)
            yield Pin(p, 1, row, b)


THRESHOLDS = {sum(1 << r for r in range(16) if r.bit_count() >= t): t
              for t in (2, 3)}


def threshold_minor(table):
    if not 0 <= table < 1 << 64:
        raise ValueError("expected an unsigned 64-bit truth table")
    for first in eligible_pins(table, 6):
        for second in eligible_pins(first.image, 5):
            if second.image in THRESHOLDS:
                return first, second
    return None


def transfer_step(n, name, small_name, pin, k, lower):
    # All images found here are nonconstant, but the intermediate five-input
    # function need not be monotone. Supply literal rows of opposite sign.
    zero = next(i for i in range(1 << (n - 1)) if not (pin.image >> i & 1))
    one = next(i for i in range(1 << (n - 1)) if pin.image >> i & 1)
    labels = [i if i < pin.position else 0 if i == pin.position else i-1 for i in range(n)]
    label = ','.join(map(str, labels))
    value = 'true' if pin.value else 'false'
    return f"""set_option maxRecDepth 16384 in
theorem {name}_bound (k : ℕ) (floor : Lower four k) : Lower {name} ({k}+1) := by
  apply ofPinnedImage (g := {small_name}) {pin.position} {value} (![{label}])
  · exact ⟨fun i => ({pin.essential_row} : ℕ).testBit i, by decide +kernel⟩
  · decide +kernel
  · exact ⟨fun i => ({zero} : ℕ).testBit i, fun i => ({one} : ℕ).testBit i, by decide +kernel⟩
  · exact {lower}
"""


def lean_certificate(table, pair):
    first, second = pair
    return f"""import CofactorBound

namespace ThresholdMinor
open CofactorBound

def table {{n : ℕ}} (mask : ℕ) (x : Fin n → Bool) : Bool :=
  mask.testBit (∑ i : Fin n, if x i then 2 ^ (i : ℕ) else 0)

def six : BFn 6 := table ({table >> 32} * 2^32 + {table & 0xffffffff})
def five : BFn 5 := table {first.image}
def four : BFn 4 := table {second.image}

{transfer_step(5, 'five', 'four', second, 'k', 'floor')}
{transfer_step(6, 'six', 'five', first, 'k+1', 'five_bound k floor')}
end ThresholdMinor
"""


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('table', type=lambda s: int(s, 0))
    parser.add_argument('--lean', action='store_true', help='emit a kernel-checkable two-pin lower-bound implication')
    args = parser.parse_args()
    try:
        pair = threshold_minor(args.table)
    except ValueError as e:
        parser.error(str(e))
    if pair is None:
        print("No eligible two-pin threshold restriction")
        raise SystemExit(1)
    if args.lean:
        print(lean_certificate(args.table, pair), end='')
    else:
        for n, pin in zip((6, 5), pair):
            print(f"On {n} inputs fix position {pin.position} to {pin.value}. Image {pin.image:#x}")
        print(f"Final restriction: at least {THRESHOLDS[pair[-1].image]} of 4")
