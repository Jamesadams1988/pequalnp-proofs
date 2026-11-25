"""Emit a portable Lean proof of a bound or a refutation of the assignment.

Usage: python make_certificate.py assignment.json rectangles.json output.lean
Rectangles are pairs of decimal natural-number masks or pairs of lists of indices.
"""
import argparse
import ast
import json
import re
from pathlib import Path


def mask(value, size):
    if isinstance(value, list):
        if any(type(i) is not int or not 0 <= i < size for i in value):
            raise ValueError(f"vertex outside Fin {size}")
        return sum(1 << i for i in set(value))
    if type(value) is not int or not 0 <= value < (1 << size):
        raise ValueError(f"mask outside {size} bits")
    return value


def generate(assignment, rectangles, name, refute):
    statement = assignment["statement"]
    match = re.fullmatch(r"¬ \((∃ L : List \(Finset \(Fin (\d+)\) × Finset \(Fin \2\)\), L.length ≤ (\d+) ∧ .*)\)", statement)
    if not match:
        raise ValueError("expected the assigned negated equal-dimension rectangle claim")
    goal, size, threshold = match[1], int(match[2]), int(match[3])
    literals = re.findall(r"\[\d+(?:, \d+)*\](?= : List ℕ)", goal)
    if len(literals) != 2 or literals[0] != literals[1]:
        raise ValueError("the soundness and coverage matrices differ")
    rows = ast.literal_eval(literals[0])
    if len(rows) != size or any(mask(r, size) != r for r in rows):
        raise ValueError("wrong matrix dimensions")
    pairs = [(mask(r, size), mask(c, size)) for r,c in rectangles]
    covered = [0] * size
    for k, (r,c) in enumerate(pairs):
        for i in range(size):
            if r & (1 << i):
                if c & rows[i]:
                    raise ValueError(f"rectangle {k} contains a one in row {i}")
                covered[i] |= c
    for i, row in enumerate(rows):
        missing = ((1 << size) - 1) ^ (row | covered[i])
        if missing:
            raise ValueError(f"uncovered zero at {(i, (missing & -missing).bit_length() - 1)}")
    if refute and len(pairs) > threshold:
        raise ValueError(f"need at most {threshold} rectangles for a refutation")
    if not re.fullmatch(r"[a-zA-Z_][a-zA-Z_0-9]*(?:\.[a-zA-Z_][a-zA-Z_0-9]*)*", name):
        raise ValueError("unsafe Lean declaration name")
    witness_goal = goal if refute else goal.replace(f"L.length ≤ {threshold}", f"L.length ≤ {len(pairs)}")
    # The reflection technique and mask-to-finset bridge follow L-meta-10011 and L-meta-10015.
    return f"""import PEqualNP.Defs

-- The mask verification strategy is adapted from L-meta-10011 and L-meta-10015.
namespace {name}_aux

private def rows : List ℕ := {rows}
private def masks : List (ℕ × ℕ) := {pairs}
private def verts (m : ℕ) : Finset (Fin {size}) := Finset.univ.filter (fun i => m.testBit i.val)

set_option maxRecDepth 100000 in
private theorem inside : ∀ p ∈ masks, ∀ i : Fin {size}, p.1.testBit i.val = true →
    ∀ j : Fin {size}, p.2.testBit j.val = true → (rows.getD i.val 0).testBit j.val = false := by decide +kernel

set_option maxRecDepth 100000 in
private theorem covered : ∀ i j : Fin {size}, (rows.getD i.val 0).testBit j.val = false →
    ∃ p ∈ masks, p.1.testBit i.val = true ∧ p.2.testBit j.val = true := by decide +kernel

theorem witness : {witness_goal} := by
  refine ⟨masks.map (fun p => (verts p.1, verts p.2)), by decide, ?_, ?_⟩
  · intro r hr i hi j hj
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    exact inside p hp i (Finset.mem_filter.mp hi).2 j (Finset.mem_filter.mp hj).2
  · intro i j h
    obtain ⟨p, hp, hi, hj⟩ := covered i j h
    exact ⟨_, List.mem_map_of_mem hp, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩

end {name}_aux

""" + (f"theorem {name} : ¬ ({statement}) := fun h => h {name}_aux.witness\n"
       if refute else f"theorem {name} : {witness_goal} := {name}_aux.witness\n")


if __name__ == "__main__":
    args = argparse.ArgumentParser(description=__doc__)
    args.add_argument("assignment", type=Path)
    args.add_argument("rectangles", type=Path)
    args.add_argument("output", type=Path)
    args.add_argument("--name", default="RectangleCover.witnessBound")
    args.add_argument("--refute", action="store_true")
    opts = args.parse_args()
    opts.output.write_text(generate(json.loads(opts.assignment.read_text()),
                                    json.loads(opts.rectangles.read_text()), opts.name, opts.refute))
