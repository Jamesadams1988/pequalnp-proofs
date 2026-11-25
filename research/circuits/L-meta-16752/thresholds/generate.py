"""Regenerate the unrestricted nine-gate lower bounds for rows.tsv.

The pinned-image generator and row manifest accompany this script. Invoke
python generate.py in any directory to emit the complete Lean module.
"""
import csv
import sys
from pathlib import Path

sys.dont_write_bytecode = True
from threshold_minor import threshold_minor, transfer_step, THRESHOLDS

print("""import CofactorBound
import PEqualNP.Outside.L_meta_12184

namespace ThresholdBatch
open CofactorBound
open PEqualNP.Outside.L_meta_12184
open PEqualNP.MetaComplexity

def table {n : ℕ} (mask : ℕ) (x : Fin n → Bool) : Bool :=
  mask.testBit (∑ i : Fin n, if x i then 2 ^ (i : ℕ) else 0)

theorem twoFloor : Lower (table (n := 4) 0xfee8) 7 := by
  have image : (table (n := 4) 0xfee8) = Transfer.small := funext (by decide +kernel)
  rw [image]
  exact Foundation.lower

theorem threeFloor : Lower (table (n := 4) 0xe880) 7 := by
  intro s h
  have dual := Transfer.dual_size (table (n := 4) 0xe880) ⟨fun _ => true, by decide +kernel⟩ s h
  have image : (fun x : Fin 4 → Bool => !(table 0xe880 (fun i => !x i))) = Transfer.small :=
    funext (by decide +kernel)
  rw [image] at dual
  exact Foundation.lower s dual
""")
rows = list(csv.DictReader(Path(__file__).with_name('rows.tsv').read_text().splitlines(), delimiter='\t'))
assert len(rows) == len({row['table'] for row in rows}) == len({row['positive_id'] for row in rows}) == 87
for row in rows:
    mask = int(row['table'], 0)
    first, second = threshold_minor(mask)
    assert THRESHOLDS[second.image] == int(row['threshold'])
    ns = 'Row' + row['positive_id'].removeprefix('L-meta-')
    print(f'namespace {ns}\n')
    print(f'def six : BFn 6 := table ({mask >> 32} * 2^32 + {mask & 0xffffffff})')
    print(f'def five : BFn 5 := table {first.image}')
    print(f'def four : BFn 4 := table {second.image}\n')
    print(transfer_step(5, 'five', 'four', second, 'k', 'floor'))
    print(transfer_step(6, 'six', 'five', first, 'k+1', 'five_bound k floor'))
    donor = 'twoFloor' if row['threshold'] == '2' else 'threeFloor'
    print(f'theorem nine : Lower six 9 := six_bound 7 {donor}\n')
    print(f'#print axioms nine\nend {ns}\n')
print('end ThresholdBatch')
