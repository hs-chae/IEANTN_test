/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0312
import SourceMainFramesV1.Point0313
import SourceMainFramesV1.Point0314
import SourceMainFramesV1.Point0315
import SourceMainFramesV1.Point0316
import SourceMainFramesV1.Point0317
import SourceMainFramesV1.Point0318
import SourceMainFramesV1.Point0319
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block39
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0312.outputs.2.hi,
 SourceMainFramesV1.Point0313.outputs.2.hi,
 SourceMainFramesV1.Point0314.outputs.2.hi,
 SourceMainFramesV1.Point0315.outputs.2.hi,
 SourceMainFramesV1.Point0316.outputs.2.hi,
 SourceMainFramesV1.Point0317.outputs.2.hi,
 SourceMainFramesV1.Point0318.outputs.2.hi,
 SourceMainFramesV1.Point0319.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 312 ≤ i) (high : i < 320)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=312) domain
     SourceMainFramesV1.Point0312.input_defined SourceMainFramesV1.Point0312.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0312.outputs.2.hi (by
         change SourceMainFramesV1.Point0312.outputs.2.hi ∈ [SourceMainFramesV1.Point0312.outputs.2.hi, SourceMainFramesV1.Point0313.outputs.2.hi, SourceMainFramesV1.Point0314.outputs.2.hi, SourceMainFramesV1.Point0315.outputs.2.hi, SourceMainFramesV1.Point0316.outputs.2.hi, SourceMainFramesV1.Point0317.outputs.2.hi, SourceMainFramesV1.Point0318.outputs.2.hi, SourceMainFramesV1.Point0319.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=313) domain
     SourceMainFramesV1.Point0313.input_defined SourceMainFramesV1.Point0313.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0313.outputs.2.hi (by
         change SourceMainFramesV1.Point0313.outputs.2.hi ∈ [SourceMainFramesV1.Point0312.outputs.2.hi, SourceMainFramesV1.Point0313.outputs.2.hi, SourceMainFramesV1.Point0314.outputs.2.hi, SourceMainFramesV1.Point0315.outputs.2.hi, SourceMainFramesV1.Point0316.outputs.2.hi, SourceMainFramesV1.Point0317.outputs.2.hi, SourceMainFramesV1.Point0318.outputs.2.hi, SourceMainFramesV1.Point0319.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=314) domain
     SourceMainFramesV1.Point0314.input_defined SourceMainFramesV1.Point0314.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0314.outputs.2.hi (by
         change SourceMainFramesV1.Point0314.outputs.2.hi ∈ [SourceMainFramesV1.Point0312.outputs.2.hi, SourceMainFramesV1.Point0313.outputs.2.hi, SourceMainFramesV1.Point0314.outputs.2.hi, SourceMainFramesV1.Point0315.outputs.2.hi, SourceMainFramesV1.Point0316.outputs.2.hi, SourceMainFramesV1.Point0317.outputs.2.hi, SourceMainFramesV1.Point0318.outputs.2.hi, SourceMainFramesV1.Point0319.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=315) domain
     SourceMainFramesV1.Point0315.input_defined SourceMainFramesV1.Point0315.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0315.outputs.2.hi (by
         change SourceMainFramesV1.Point0315.outputs.2.hi ∈ [SourceMainFramesV1.Point0312.outputs.2.hi, SourceMainFramesV1.Point0313.outputs.2.hi, SourceMainFramesV1.Point0314.outputs.2.hi, SourceMainFramesV1.Point0315.outputs.2.hi, SourceMainFramesV1.Point0316.outputs.2.hi, SourceMainFramesV1.Point0317.outputs.2.hi, SourceMainFramesV1.Point0318.outputs.2.hi, SourceMainFramesV1.Point0319.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=316) domain
     SourceMainFramesV1.Point0316.input_defined SourceMainFramesV1.Point0316.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0316.outputs.2.hi (by
         change SourceMainFramesV1.Point0316.outputs.2.hi ∈ [SourceMainFramesV1.Point0312.outputs.2.hi, SourceMainFramesV1.Point0313.outputs.2.hi, SourceMainFramesV1.Point0314.outputs.2.hi, SourceMainFramesV1.Point0315.outputs.2.hi, SourceMainFramesV1.Point0316.outputs.2.hi, SourceMainFramesV1.Point0317.outputs.2.hi, SourceMainFramesV1.Point0318.outputs.2.hi, SourceMainFramesV1.Point0319.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=317) domain
     SourceMainFramesV1.Point0317.input_defined SourceMainFramesV1.Point0317.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0317.outputs.2.hi (by
         change SourceMainFramesV1.Point0317.outputs.2.hi ∈ [SourceMainFramesV1.Point0312.outputs.2.hi, SourceMainFramesV1.Point0313.outputs.2.hi, SourceMainFramesV1.Point0314.outputs.2.hi, SourceMainFramesV1.Point0315.outputs.2.hi, SourceMainFramesV1.Point0316.outputs.2.hi, SourceMainFramesV1.Point0317.outputs.2.hi, SourceMainFramesV1.Point0318.outputs.2.hi, SourceMainFramesV1.Point0319.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=318) domain
     SourceMainFramesV1.Point0318.input_defined SourceMainFramesV1.Point0318.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0318.outputs.2.hi (by
         change SourceMainFramesV1.Point0318.outputs.2.hi ∈ [SourceMainFramesV1.Point0312.outputs.2.hi, SourceMainFramesV1.Point0313.outputs.2.hi, SourceMainFramesV1.Point0314.outputs.2.hi, SourceMainFramesV1.Point0315.outputs.2.hi, SourceMainFramesV1.Point0316.outputs.2.hi, SourceMainFramesV1.Point0317.outputs.2.hi, SourceMainFramesV1.Point0318.outputs.2.hi, SourceMainFramesV1.Point0319.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=319) domain
     SourceMainFramesV1.Point0319.input_defined SourceMainFramesV1.Point0319.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0319.outputs.2.hi (by
         change SourceMainFramesV1.Point0319.outputs.2.hi ∈ [SourceMainFramesV1.Point0312.outputs.2.hi, SourceMainFramesV1.Point0313.outputs.2.hi, SourceMainFramesV1.Point0314.outputs.2.hi, SourceMainFramesV1.Point0315.outputs.2.hi, SourceMainFramesV1.Point0316.outputs.2.hi, SourceMainFramesV1.Point0317.outputs.2.hi, SourceMainFramesV1.Point0318.outputs.2.hi, SourceMainFramesV1.Point0319.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block39
