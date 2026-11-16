/- Pure numerical word cache model, with no C execution proof imports.
Raw proposals acquire mathematical status only after independent kernel checks. -/
import SynergyAnalytic.HeightPointLogGridDefs
namespace SynergyMomentMath.WordModel
open ScopedNumerical SynergyAnalytic.HeightPoint
set_option autoImplicit false
set_option maxHeartbeats 200000

def modelOutputs (input : ProofBox) : Option (ProofBox × ProofBox) := do
  let values ← point constantValues input
  let c ← values[mainIndex]?
  let d ← values[slopeIndex]?
  pure (c,d)
@[irreducible] def outputs (i : Nat) : ProofBox × ProofBox :=
  (modelOutputs ((logCell (i+1)).getD ⟨0,0⟩)).getD (⟨0,0⟩,⟨0,0⟩)
def highPair (pair : ProofBox × ProofBox) : Int × Int :=
  ((ProofBox.add pair.1 (ProofBox.literal 128 21600 1)).hi,pair.2.hi)
theorem outputs_function_exact : outputs=(fun i=>
    (modelOutputs ((logCell (i+1)).getD ⟨0,0⟩)).getD (⟨0,0⟩,⟨0,0⟩)) := by
  unfold outputs
  rfl

theorem from_all (actual : List (ProofBox × ProofBox)) (words : List (Int × Int))
    (checked : (actual.zip words).all (fun x=>decide (highPair x.1=x.2))=true)
    (pair : ProofBox × ProofBox) (word : Int × Int)
    (member : (pair,word) ∈ actual.zip words) : highPair pair=word :=
  of_decide_eq_true ((List.all_eq_true.mp checked) (pair,word) member)

#print axioms outputs_function_exact
#print axioms from_all
end SynergyMomentMath.WordModel
