"""Write FamilyExact.lean to standard output from the two public TSV manifests.

Usage: python3 generate_exact.py --rows rows.tsv --family family.tsv > FamilyExact.lean
"""
import argparse
import ast
import csv
from pathlib import Path
import re


def rows(path):
    with path.open() as f:
        return list(csv.DictReader(f, delimiter='\t'))


def compile_tree(text):
    gates = []
    def visit(node):
        if isinstance(node, ast.Name) and re.fullmatch('x[0-5]', node.id):
            return int(node.id[1])
        assert isinstance(node, ast.BinOp) and isinstance(node.op, (ast.BitOr, ast.BitAnd))
        a, b = visit(node.left), visit(node.right)
        op = 'or' if isinstance(node.op, ast.BitOr) else 'and'
        gates.append(f'⟨.{op}, [{a}, {b}]⟩')
        return 5 + len(gates)
    out = visit(ast.parse(text, mode='eval').body)
    assert len(gates) == 9 and out == 14
    return ', '.join(gates)

here = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--rows', type=Path, default=here.parent/'thresholds/rows.tsv')
parser.add_argument('--family', type=Path, default=here/'family.tsv')
args = parser.parse_args()
lowers = {r['positive_id']: int(r['table'], 16) for r in rows(args.rows)}
family = rows(args.family)
assert lowers == {r['positive_row']: int(r['mask'],16) for r in family}
successes = [r for r in family if r['minimum_monotone_tree_gates'] == '9']
assert len(successes) == 50
print('''import ThresholdBatch

/-! Each explicit nine-gate AND/OR witness is evaluated on every assignment.
`ThresholdBatch` supplies the unrestricted lower bound by two essential pins.
-/
namespace FamilyExact
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CofactorBound

def ExactNine (f : BFn 6) : Prop :=
  Lower f 9 ∧ HasCircuitSize 6 f 9 ∧ ∃ C : Circuit, Monotone2 C ∧ C.size = 9 ∧
    ∀ x, C.eval (List.ofFn x) = f x

theorem fromWitness {f : BFn 6} (C : Circuit) (lower : Lower f 9)
    (hm : Monotone2 C) (hs : C.size = 9) (he : ∀ x, C.eval (List.ofFn x) = f x) :
    ExactNine f := by
  have fan : FanInTwo C := by
    intro gate hg
    obtain ⟨op, ar⟩ := hm gate hg
    exact ⟨op.elim Or.inl (fun ho => Or.inr (Or.inl ho)), ar⟩
  exact ⟨lower, ⟨C, fan, hs.le, he⟩, C, hm, hs, he⟩

theorem positive {f : BFn 6} (h : ExactNine f) (s : ℕ) (budget : HasCircuitSize 6 f s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x, C.eval (List.ofFn x) = f x := by
  obtain ⟨hl, _, C, hm, hs, he⟩ := h
  exact ⟨C, hm, hs.le.trans (hl s budget), he⟩

set_option maxRecDepth 16384''')
for r in successes:
    name = 'Row' + r['positive_row'].split('-')[-1]
    print(f'''
namespace {name}

def witness : Circuit := ⟨[{compile_tree(r['witness'])}], 14⟩

theorem exactNine : ExactNine ThresholdBatch.{name}.six :=
  fromWitness witness ThresholdBatch.{name}.nine (by simp [Monotone2, witness]) rfl
    (by decide +kernel)

#print axioms exactNine
end {name}''')
print('\nend FamilyExact')
