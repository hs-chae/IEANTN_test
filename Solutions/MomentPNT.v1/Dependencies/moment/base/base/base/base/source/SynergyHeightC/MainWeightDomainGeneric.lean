/- Decode the finite domain check with abstract inputs before instantiating the
large numerical evaluator. The original checker and arithmetic remain unchanged. -/
import SynergyHeightC.MainWeightAbstract
namespace SynergyHeightC.MainWeightModel
open ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 20000

def InputsOK (left right c d : ProofBox) : Prop :=
  0 ≤ left.lo ∧ left.lo ≤ left.hi ∧ left.hi ≤ 64*ProofBox.scale 128 ∧
  0 ≤ right.lo ∧ right.lo ≤ right.hi ∧ right.hi ≤ 64*ProofBox.scale 128 ∧
  0 ≤ (adjustedC c).hi ∧ 0 ≤ d.hi ∧ d.hi < 330*ProofBox.scale 128 ∧
  0 ≤ (term left right c d).lo ∧
  (term left right c d).lo ≤ (term left right c d).hi ∧
  (term left right c d).hi ≤ ProofBox.scale 128

theorem abstract_domain_decode
    (grid : Nat → Option ProofBox)
    (evaluate : ProofBox → Option (ProofBox×ProofBox))
    (calculate : ProofBox → ProofBox → ProofBox → ProofBox → ProofBox)
    (adjust : ProofBox → ProofBox) {i : Nat}
    (h : abstractDomain grid evaluate calculate adjust i=true) :
    ∃ left right c d, grid i=some left ∧ grid (i+1)=some right ∧
      evaluate right=some (c,d) ∧
      (0 ≤ left.lo ∧ left.lo ≤ left.hi ∧ left.hi ≤ 64*ProofBox.scale 128 ∧
      0 ≤ right.lo ∧ right.lo ≤ right.hi ∧ right.hi ≤ 64*ProofBox.scale 128 ∧
      0 ≤ (adjust c).hi ∧ 0 ≤ d.hi ∧ d.hi < 330*ProofBox.scale 128 ∧
      0 ≤ (calculate left right c d).lo ∧
      (calculate left right c d).lo ≤ (calculate left right c d).hi ∧
      (calculate left right c d).hi ≤ ProofBox.scale 128) := by
  unfold abstractDomain at h
  split at h
  next left right hl hr =>
    split at h
    next c d hm =>
      refine ⟨left,right,c,d,hl,hr,hm,?_⟩
      exact of_decide_eq_true h
    next => contradiction
  next => contradiction

theorem cell_domain_decode {i : Nat} (h : cellDomain i=true) :
    ∃ left right c d, SynergyAnalytic.HeightPoint.logCell i=some left ∧
      SynergyAnalytic.HeightPoint.logCell (i+1)=some right ∧
      PointExecuteAPI.modelOutputs right=some (c,d) ∧ InputsOK left right c d := by
  have transported : abstractDomain SynergyAnalytic.HeightPoint.logCell
      PointExecuteAPI.modelOutputs term adjustedC i=true :=
    Eq.mp (congrArg (fun f : Nat→Bool=>f i=true) actual_domain_function_exact) h
  exact abstract_domain_decode SynergyAnalytic.HeightPoint.logCell
    PointExecuteAPI.modelOutputs term adjustedC transported

#print axioms abstract_domain_decode
#print axioms cell_domain_decode
end SynergyHeightC.MainWeightModel
