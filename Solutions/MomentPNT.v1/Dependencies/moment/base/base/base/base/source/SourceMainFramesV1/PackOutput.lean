/- Pack model/actual-pointer records without normalizing closed numerical boxes. -/
import SynergyHeightC.FramedPointReplayAPI
namespace SourceMainFramesV1
open ScopedC ScopedC.Machine ScopedNumerical SynergyAnalytic.HeightPoint
open SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0

theorem pack_output {i : Nat} {base : State} {input : ProofBox}
    {pair : ProofBox × ProofBox}
    (defined : logCell (i+1)=some input)
    (model : modelOutputs input=some pair)
    (source : SourcePointOutputs base input pair.1 pair.2) :
    ∃ base input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
      SourcePointOutputs base input c d := by
  rcases pair with ⟨c,d⟩
  exact ⟨base,input,c,d,defined,model,source⟩
#print axioms pack_output
end SourceMainFramesV1
