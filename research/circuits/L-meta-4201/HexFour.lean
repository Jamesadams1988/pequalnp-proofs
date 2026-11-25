import HexSignature
namespace Row4201.HexFour

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem noFour (p : Program) : ¬ agrees p := by
  rcases p with ⟨a,b,c,d,e,f,g,h,z⟩
  unfold agrees run step meet BitVec.cons
  simp only [BitVec.cast_eq]
  dsimp
  bv_decide

end Row4201.HexFour
#print axioms Row4201.HexFour.noFour
