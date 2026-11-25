"""Match a six-input cofactor to a five-input truth table by permuting inputs.

Bit r is the output on row r. Input i is bit i of r. Tables are unsigned
integer literals. Exit 0 prints the first witness, 1 means no eligible match,
and 2 indicates invalid input. Python 3.10+.
"""
import argparse
import json
from itertools import permutations


def bit(number, index):
    return (number >> index) & 1


def first_match(six, five):
    """Return the first witness in (pin, value, free labels) order, or None."""
    if not 0 <= six < 1 << 64 or not 0 <= five < 1 << 32:
        raise ValueError("expected unsigned 64-bit and 32-bit truth tables")
    if five in (0, (1 << 32) - 1):
        return None
    u = next(y for y in range(32) if not bit(five, y))
    v = next(y for y in range(32) if bit(five, y))
    for pin in range(6):
        flip = 1 << pin
        x = next((r for r in range(64) if bit(six, r) != bit(six, r ^ flip)), None)
        if x is None:
            continue
        for value in (False, True):
            for free_labels in permutations(range(5)):
                # Indexed by source coordinate i, label[i] names an input of y.
                label = list(free_labels)
                label.insert(pin, 0)
                for y in range(32):
                    row = sum((value if i == pin else bit(y, j)) << i
                              for i, j in enumerate(label))
                    if bit(six, row) != bit(five, y):
                        break
                else:
                    return dict(pin=pin, value=value, label=label,
                                essential_rows=[x, x ^ flip], nonconstant_rows=[u, v])
    return None


def lean_certificate(six, five, match):
    """Emit the three finite hypotheses consumed by CofactorBound.ofPinnedImage."""
    p = match["pin"]
    b = "true" if match["value"] else "false"
    label = ", ".join(map(str, match["label"]))
    x, _ = match["essential_rows"]
    u, v = match["nonconstant_rows"]
    high, low = divmod(six, 1 << 32)
    return f"""import PEqualNP.Defs

namespace PinnedMatch

def fn6 (x : Fin 6 → Bool) : Bool :=
  Nat.testBit ({high} * 2^32 + {low}) (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0)

def fn5 (y : Fin 5 → Bool) : Bool :=
  Nat.testBit {five} (∑ i : Fin 5, if y i then 2^(i : ℕ) else 0)

def label : Fin 6 → Fin 5 := ![{label}]

theorem essential : ∃ x, fn6 (Function.update x {p} (!x {p})) ≠ fn6 x :=
  ⟨fun i => ({x} : Nat).testBit i, by decide +kernel⟩

set_option maxRecDepth 8192 in
theorem image : ∀ y, fn6 (Function.update (y ∘ label) {p} {b}) = fn5 y := by
  decide +kernel

theorem nonconstant : ∃ u v, fn5 u ≠ fn5 v :=
  ⟨fun i => ({u} : Nat).testBit i, fun i => ({v} : Nat).testBit i, by decide +kernel⟩

end PinnedMatch"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("six", help="64-bit truth table, decimal or 0x-prefixed hex")
    parser.add_argument("five", help="32-bit truth table, decimal or 0x-prefixed hex")
    parser.add_argument("--lean", action="store_true", help="emit the witness as Lean source")
    args = parser.parse_args()
    try:
        six, five = (int(s, 10) if s.isdecimal() else int(s, 0)
                     for s in (args.six, args.five))
        match = first_match(six, five)
    except ValueError as exc:
        parser.error(str(exc))
    if match is None:
        print("null")
        return 1
    print(lean_certificate(six, five, match) if args.lean else json.dumps(match))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
