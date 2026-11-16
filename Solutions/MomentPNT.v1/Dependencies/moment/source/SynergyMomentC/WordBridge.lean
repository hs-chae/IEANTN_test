/- Exact functional bridge from pure cached computations to the unchanged C model.
No application execution or numerical word is postulated. -/
import SynergyMomentC.Model
import SynergyMomentMath.WordModel
namespace SynergyMomentC.WordBridge
open ScopedNumerical SynergyAnalytic.HeightPoint SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000

theorem model_outputs_exact : SynergyMomentMath.WordModel.modelOutputs=
    SynergyHeightC.PointExecuteAPI.modelOutputs := rfl

theorem model_pair_exact : modelPair=SynergyMomentMath.WordModel.outputs := by
  have grid := congrArg
    (fun get : Nat → ProofBox=>fun i=>
      (SynergyHeightC.PointExecuteAPI.modelOutputs (get (i+1))).getD (⟨0,0⟩,⟨0,0⟩))
    gridInput_function_exact
  have evaluate := congrArg
    (fun get : ProofBox → Option (ProofBox × ProofBox)=>fun i=>
      (get ((logCell (i+1)).getD ⟨0,0⟩)).getD (⟨0,0⟩,⟨0,0⟩)) model_outputs_exact.symm
  exact modelPair_function_exact.trans
    (grid.trans (evaluate.trans SynergyMomentMath.WordModel.outputs_function_exact.symm))

theorem high_pair_exact : Model.highPair=SynergyMomentMath.WordModel.highPair := rfl

theorem source_words {i : Nat} {word : Int × Int}
    (checked : SynergyMomentMath.WordModel.highPair
      (SynergyMomentMath.WordModel.outputs i)=word) :
    Model.highPair (modelPair i)=word := by
  have pair := congrFun model_pair_exact i
  rw [pair,high_pair_exact]
  exact checked

#print axioms model_outputs_exact
#print axioms model_pair_exact
#print axioms high_pair_exact
#print axioms source_words
end SynergyMomentC.WordBridge
