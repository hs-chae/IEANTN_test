/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0464
import SourceMainFramesV1.Point0465
import SourceMainFramesV1.Point0466
import SourceMainFramesV1.Point0467
import SourceMainFramesV1.Point0468
import SourceMainFramesV1.Point0469
import SourceMainFramesV1.Point0470
import SourceMainFramesV1.Point0471
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block58
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0464.outputs.2.hi,
 SourceMainFramesV1.Point0465.outputs.2.hi,
 SourceMainFramesV1.Point0466.outputs.2.hi,
 SourceMainFramesV1.Point0467.outputs.2.hi,
 SourceMainFramesV1.Point0468.outputs.2.hi,
 SourceMainFramesV1.Point0469.outputs.2.hi,
 SourceMainFramesV1.Point0470.outputs.2.hi,
 SourceMainFramesV1.Point0471.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 464 ≤ i) (high : i < 472)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=464) domain
     SourceMainFramesV1.Point0464.input_defined SourceMainFramesV1.Point0464.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0464.outputs.2.hi (by
         change SourceMainFramesV1.Point0464.outputs.2.hi ∈ [SourceMainFramesV1.Point0464.outputs.2.hi, SourceMainFramesV1.Point0465.outputs.2.hi, SourceMainFramesV1.Point0466.outputs.2.hi, SourceMainFramesV1.Point0467.outputs.2.hi, SourceMainFramesV1.Point0468.outputs.2.hi, SourceMainFramesV1.Point0469.outputs.2.hi, SourceMainFramesV1.Point0470.outputs.2.hi, SourceMainFramesV1.Point0471.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=465) domain
     SourceMainFramesV1.Point0465.input_defined SourceMainFramesV1.Point0465.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0465.outputs.2.hi (by
         change SourceMainFramesV1.Point0465.outputs.2.hi ∈ [SourceMainFramesV1.Point0464.outputs.2.hi, SourceMainFramesV1.Point0465.outputs.2.hi, SourceMainFramesV1.Point0466.outputs.2.hi, SourceMainFramesV1.Point0467.outputs.2.hi, SourceMainFramesV1.Point0468.outputs.2.hi, SourceMainFramesV1.Point0469.outputs.2.hi, SourceMainFramesV1.Point0470.outputs.2.hi, SourceMainFramesV1.Point0471.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=466) domain
     SourceMainFramesV1.Point0466.input_defined SourceMainFramesV1.Point0466.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0466.outputs.2.hi (by
         change SourceMainFramesV1.Point0466.outputs.2.hi ∈ [SourceMainFramesV1.Point0464.outputs.2.hi, SourceMainFramesV1.Point0465.outputs.2.hi, SourceMainFramesV1.Point0466.outputs.2.hi, SourceMainFramesV1.Point0467.outputs.2.hi, SourceMainFramesV1.Point0468.outputs.2.hi, SourceMainFramesV1.Point0469.outputs.2.hi, SourceMainFramesV1.Point0470.outputs.2.hi, SourceMainFramesV1.Point0471.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=467) domain
     SourceMainFramesV1.Point0467.input_defined SourceMainFramesV1.Point0467.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0467.outputs.2.hi (by
         change SourceMainFramesV1.Point0467.outputs.2.hi ∈ [SourceMainFramesV1.Point0464.outputs.2.hi, SourceMainFramesV1.Point0465.outputs.2.hi, SourceMainFramesV1.Point0466.outputs.2.hi, SourceMainFramesV1.Point0467.outputs.2.hi, SourceMainFramesV1.Point0468.outputs.2.hi, SourceMainFramesV1.Point0469.outputs.2.hi, SourceMainFramesV1.Point0470.outputs.2.hi, SourceMainFramesV1.Point0471.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=468) domain
     SourceMainFramesV1.Point0468.input_defined SourceMainFramesV1.Point0468.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0468.outputs.2.hi (by
         change SourceMainFramesV1.Point0468.outputs.2.hi ∈ [SourceMainFramesV1.Point0464.outputs.2.hi, SourceMainFramesV1.Point0465.outputs.2.hi, SourceMainFramesV1.Point0466.outputs.2.hi, SourceMainFramesV1.Point0467.outputs.2.hi, SourceMainFramesV1.Point0468.outputs.2.hi, SourceMainFramesV1.Point0469.outputs.2.hi, SourceMainFramesV1.Point0470.outputs.2.hi, SourceMainFramesV1.Point0471.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=469) domain
     SourceMainFramesV1.Point0469.input_defined SourceMainFramesV1.Point0469.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0469.outputs.2.hi (by
         change SourceMainFramesV1.Point0469.outputs.2.hi ∈ [SourceMainFramesV1.Point0464.outputs.2.hi, SourceMainFramesV1.Point0465.outputs.2.hi, SourceMainFramesV1.Point0466.outputs.2.hi, SourceMainFramesV1.Point0467.outputs.2.hi, SourceMainFramesV1.Point0468.outputs.2.hi, SourceMainFramesV1.Point0469.outputs.2.hi, SourceMainFramesV1.Point0470.outputs.2.hi, SourceMainFramesV1.Point0471.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=470) domain
     SourceMainFramesV1.Point0470.input_defined SourceMainFramesV1.Point0470.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0470.outputs.2.hi (by
         change SourceMainFramesV1.Point0470.outputs.2.hi ∈ [SourceMainFramesV1.Point0464.outputs.2.hi, SourceMainFramesV1.Point0465.outputs.2.hi, SourceMainFramesV1.Point0466.outputs.2.hi, SourceMainFramesV1.Point0467.outputs.2.hi, SourceMainFramesV1.Point0468.outputs.2.hi, SourceMainFramesV1.Point0469.outputs.2.hi, SourceMainFramesV1.Point0470.outputs.2.hi, SourceMainFramesV1.Point0471.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=471) domain
     SourceMainFramesV1.Point0471.input_defined SourceMainFramesV1.Point0471.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0471.outputs.2.hi (by
         change SourceMainFramesV1.Point0471.outputs.2.hi ∈ [SourceMainFramesV1.Point0464.outputs.2.hi, SourceMainFramesV1.Point0465.outputs.2.hi, SourceMainFramesV1.Point0466.outputs.2.hi, SourceMainFramesV1.Point0467.outputs.2.hi, SourceMainFramesV1.Point0468.outputs.2.hi, SourceMainFramesV1.Point0469.outputs.2.hi, SourceMainFramesV1.Point0470.outputs.2.hi, SourceMainFramesV1.Point0471.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block58
