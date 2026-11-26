"""Generate literal Lean witnesses from the named star-cover gate lists."""
import argparse
import json
import re
from pathlib import Path

def parse_args():
    parser=argparse.ArgumentParser()
    parser.add_argument('assignment',type=Path)
    parser.add_argument('witnesses',type=Path)
    parser.add_argument('output',type=Path)
    return parser.parse_args()

def main():
    args=parse_args()
    desk=json.loads(args.assignment.read_text())
    assert desk['id']=='L-meta-17336'
    body,=re.findall(r'\(fun x : Fin 9 → Bool => (.*?)\) → 16 ≤ C.size',desk['statement'])
    witnesses=json.loads(args.witnesses.read_text())
    assert set(witnesses)=={'not5',*(f'{op}5_{j}' for op in ['or','and'] for j in [6,7,8])}
    doc=['import PEqualNP.Defs.MetaComplexityMinimal','',
         'namespace FirstWire17336','open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity','',
         'set_option maxRecDepth 16000','set_option maxHeartbeats 2000000','',
         'def target (x : Fin 9 → Bool) : Bool :=','  '+body,'',
         'private theorem inputs (x : Fin 9 → Bool) :',
         '    List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8] := rfl', '',
         'def Meets (C : Circuit) (s : Nat) (first : (Fin 9 → Bool) → Bool) : Prop :=',
         '  FanInTwo C ∧ C.size = s ∧',
         '    (∀ x, (C.wires (List.ofFn x)).getD 9 false = first x) ∧',
         '    circuitFun 9 C = target','']
    instances=[]
    for name, item in witnesses.items():
        gates=item['gates']
        assert len(gates)==(16 if name.startswith('or') else 17)
        instances.append((name, gates, item['output']))
        if len(gates)==16:
            instances.append((name+'Padded',gates+[['or',item['output'],item['output']]],9+16))
    for name,gates,output in instances:
        ls=[]
        for i, (op,*inputs) in enumerate(gates):
            assert len(inputs)==(1 if op=='not' else 2)
            assert all(0 <= a < 9+i for a in inputs)
            ls.append(f'⟨.{op}, {inputs}⟩')
        first=gates[0]; assert first[1]==5
        if first[0]=='not':
            assert name=='not5'; fp='!(x 5)'
        else:
            j=first[2]; assert name.startswith(f'{first[0]}5_{j}') and 6<=j<=8
            fp=f'(x 5 {"&&" if first[0]=="and" else "||"} x {j})'
        doc += [f'def {name} : Circuit :=','  ⟨['+',\n    '.join(', '.join(ls[i:i+3]) for i in range(0,len(ls),3))+f'], {output}⟩','',
                f'theorem {name}_spec : Meets {name} {len(gates)} (fun x => {fp}) := by',
                '  refine ⟨?_, rfl, ?_, ?_⟩', f'  · simp [{name}, FanInTwo]',
                '  · intro x', '    rw [inputs]',
                f'    simp [Circuit.wires, {name}, GateOp.eval, List.getD]',
                '  · funext x', f'    change {name}.eval (List.ofFn x) = target x',
                '    rw [inputs]', f'    simp [Circuit.eval, Circuit.wires, {name}, GateOp.eval, List.getD, target,',
                '      Bool.and_or_distrib_left]', '    ac_rfl', '']
    doc += [f'#print axioms {name}_spec' for name,_,_ in instances]
    args.output.write_text('\n'.join(doc+['','end FirstWire17336','']))

if __name__=='__main__': main()
