/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0288
import SourceMainFramesV1.Point0289
import SourceMainFramesV1.Point0290
import SourceMainFramesV1.Point0291
import SourceMainFramesV1.Point0292
import SourceMainFramesV1.Point0293
import SourceMainFramesV1.Point0294
import SourceMainFramesV1.Point0295
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block36
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0288.outputs.2.hi,
 SourceMainFramesV1.Point0289.outputs.2.hi,
 SourceMainFramesV1.Point0290.outputs.2.hi,
 SourceMainFramesV1.Point0291.outputs.2.hi,
 SourceMainFramesV1.Point0292.outputs.2.hi,
 SourceMainFramesV1.Point0293.outputs.2.hi,
 SourceMainFramesV1.Point0294.outputs.2.hi,
 SourceMainFramesV1.Point0295.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 288 ≤ i) (high : i < 296)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=288) domain
     SourceMainFramesV1.Point0288.input_defined SourceMainFramesV1.Point0288.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0288.outputs.2.hi (by
         change SourceMainFramesV1.Point0288.outputs.2.hi ∈ [SourceMainFramesV1.Point0288.outputs.2.hi, SourceMainFramesV1.Point0289.outputs.2.hi, SourceMainFramesV1.Point0290.outputs.2.hi, SourceMainFramesV1.Point0291.outputs.2.hi, SourceMainFramesV1.Point0292.outputs.2.hi, SourceMainFramesV1.Point0293.outputs.2.hi, SourceMainFramesV1.Point0294.outputs.2.hi, SourceMainFramesV1.Point0295.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=289) domain
     SourceMainFramesV1.Point0289.input_defined SourceMainFramesV1.Point0289.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0289.outputs.2.hi (by
         change SourceMainFramesV1.Point0289.outputs.2.hi ∈ [SourceMainFramesV1.Point0288.outputs.2.hi, SourceMainFramesV1.Point0289.outputs.2.hi, SourceMainFramesV1.Point0290.outputs.2.hi, SourceMainFramesV1.Point0291.outputs.2.hi, SourceMainFramesV1.Point0292.outputs.2.hi, SourceMainFramesV1.Point0293.outputs.2.hi, SourceMainFramesV1.Point0294.outputs.2.hi, SourceMainFramesV1.Point0295.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=290) domain
     SourceMainFramesV1.Point0290.input_defined SourceMainFramesV1.Point0290.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0290.outputs.2.hi (by
         change SourceMainFramesV1.Point0290.outputs.2.hi ∈ [SourceMainFramesV1.Point0288.outputs.2.hi, SourceMainFramesV1.Point0289.outputs.2.hi, SourceMainFramesV1.Point0290.outputs.2.hi, SourceMainFramesV1.Point0291.outputs.2.hi, SourceMainFramesV1.Point0292.outputs.2.hi, SourceMainFramesV1.Point0293.outputs.2.hi, SourceMainFramesV1.Point0294.outputs.2.hi, SourceMainFramesV1.Point0295.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=291) domain
     SourceMainFramesV1.Point0291.input_defined SourceMainFramesV1.Point0291.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0291.outputs.2.hi (by
         change SourceMainFramesV1.Point0291.outputs.2.hi ∈ [SourceMainFramesV1.Point0288.outputs.2.hi, SourceMainFramesV1.Point0289.outputs.2.hi, SourceMainFramesV1.Point0290.outputs.2.hi, SourceMainFramesV1.Point0291.outputs.2.hi, SourceMainFramesV1.Point0292.outputs.2.hi, SourceMainFramesV1.Point0293.outputs.2.hi, SourceMainFramesV1.Point0294.outputs.2.hi, SourceMainFramesV1.Point0295.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=292) domain
     SourceMainFramesV1.Point0292.input_defined SourceMainFramesV1.Point0292.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0292.outputs.2.hi (by
         change SourceMainFramesV1.Point0292.outputs.2.hi ∈ [SourceMainFramesV1.Point0288.outputs.2.hi, SourceMainFramesV1.Point0289.outputs.2.hi, SourceMainFramesV1.Point0290.outputs.2.hi, SourceMainFramesV1.Point0291.outputs.2.hi, SourceMainFramesV1.Point0292.outputs.2.hi, SourceMainFramesV1.Point0293.outputs.2.hi, SourceMainFramesV1.Point0294.outputs.2.hi, SourceMainFramesV1.Point0295.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=293) domain
     SourceMainFramesV1.Point0293.input_defined SourceMainFramesV1.Point0293.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0293.outputs.2.hi (by
         change SourceMainFramesV1.Point0293.outputs.2.hi ∈ [SourceMainFramesV1.Point0288.outputs.2.hi, SourceMainFramesV1.Point0289.outputs.2.hi, SourceMainFramesV1.Point0290.outputs.2.hi, SourceMainFramesV1.Point0291.outputs.2.hi, SourceMainFramesV1.Point0292.outputs.2.hi, SourceMainFramesV1.Point0293.outputs.2.hi, SourceMainFramesV1.Point0294.outputs.2.hi, SourceMainFramesV1.Point0295.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=294) domain
     SourceMainFramesV1.Point0294.input_defined SourceMainFramesV1.Point0294.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0294.outputs.2.hi (by
         change SourceMainFramesV1.Point0294.outputs.2.hi ∈ [SourceMainFramesV1.Point0288.outputs.2.hi, SourceMainFramesV1.Point0289.outputs.2.hi, SourceMainFramesV1.Point0290.outputs.2.hi, SourceMainFramesV1.Point0291.outputs.2.hi, SourceMainFramesV1.Point0292.outputs.2.hi, SourceMainFramesV1.Point0293.outputs.2.hi, SourceMainFramesV1.Point0294.outputs.2.hi, SourceMainFramesV1.Point0295.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=295) domain
     SourceMainFramesV1.Point0295.input_defined SourceMainFramesV1.Point0295.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0295.outputs.2.hi (by
         change SourceMainFramesV1.Point0295.outputs.2.hi ∈ [SourceMainFramesV1.Point0288.outputs.2.hi, SourceMainFramesV1.Point0289.outputs.2.hi, SourceMainFramesV1.Point0290.outputs.2.hi, SourceMainFramesV1.Point0291.outputs.2.hi, SourceMainFramesV1.Point0292.outputs.2.hi, SourceMainFramesV1.Point0293.outputs.2.hi, SourceMainFramesV1.Point0294.outputs.2.hi, SourceMainFramesV1.Point0295.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block36
