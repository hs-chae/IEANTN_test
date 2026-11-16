/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0304
import SourceMainFramesV1.Point0305
import SourceMainFramesV1.Point0306
import SourceMainFramesV1.Point0307
import SourceMainFramesV1.Point0308
import SourceMainFramesV1.Point0309
import SourceMainFramesV1.Point0310
import SourceMainFramesV1.Point0311
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block38
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0304.outputs.2.hi,
 SourceMainFramesV1.Point0305.outputs.2.hi,
 SourceMainFramesV1.Point0306.outputs.2.hi,
 SourceMainFramesV1.Point0307.outputs.2.hi,
 SourceMainFramesV1.Point0308.outputs.2.hi,
 SourceMainFramesV1.Point0309.outputs.2.hi,
 SourceMainFramesV1.Point0310.outputs.2.hi,
 SourceMainFramesV1.Point0311.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 304 ≤ i) (high : i < 312)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=304) domain
     SourceMainFramesV1.Point0304.input_defined SourceMainFramesV1.Point0304.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0304.outputs.2.hi (by
         change SourceMainFramesV1.Point0304.outputs.2.hi ∈ [SourceMainFramesV1.Point0304.outputs.2.hi, SourceMainFramesV1.Point0305.outputs.2.hi, SourceMainFramesV1.Point0306.outputs.2.hi, SourceMainFramesV1.Point0307.outputs.2.hi, SourceMainFramesV1.Point0308.outputs.2.hi, SourceMainFramesV1.Point0309.outputs.2.hi, SourceMainFramesV1.Point0310.outputs.2.hi, SourceMainFramesV1.Point0311.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=305) domain
     SourceMainFramesV1.Point0305.input_defined SourceMainFramesV1.Point0305.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0305.outputs.2.hi (by
         change SourceMainFramesV1.Point0305.outputs.2.hi ∈ [SourceMainFramesV1.Point0304.outputs.2.hi, SourceMainFramesV1.Point0305.outputs.2.hi, SourceMainFramesV1.Point0306.outputs.2.hi, SourceMainFramesV1.Point0307.outputs.2.hi, SourceMainFramesV1.Point0308.outputs.2.hi, SourceMainFramesV1.Point0309.outputs.2.hi, SourceMainFramesV1.Point0310.outputs.2.hi, SourceMainFramesV1.Point0311.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=306) domain
     SourceMainFramesV1.Point0306.input_defined SourceMainFramesV1.Point0306.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0306.outputs.2.hi (by
         change SourceMainFramesV1.Point0306.outputs.2.hi ∈ [SourceMainFramesV1.Point0304.outputs.2.hi, SourceMainFramesV1.Point0305.outputs.2.hi, SourceMainFramesV1.Point0306.outputs.2.hi, SourceMainFramesV1.Point0307.outputs.2.hi, SourceMainFramesV1.Point0308.outputs.2.hi, SourceMainFramesV1.Point0309.outputs.2.hi, SourceMainFramesV1.Point0310.outputs.2.hi, SourceMainFramesV1.Point0311.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=307) domain
     SourceMainFramesV1.Point0307.input_defined SourceMainFramesV1.Point0307.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0307.outputs.2.hi (by
         change SourceMainFramesV1.Point0307.outputs.2.hi ∈ [SourceMainFramesV1.Point0304.outputs.2.hi, SourceMainFramesV1.Point0305.outputs.2.hi, SourceMainFramesV1.Point0306.outputs.2.hi, SourceMainFramesV1.Point0307.outputs.2.hi, SourceMainFramesV1.Point0308.outputs.2.hi, SourceMainFramesV1.Point0309.outputs.2.hi, SourceMainFramesV1.Point0310.outputs.2.hi, SourceMainFramesV1.Point0311.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=308) domain
     SourceMainFramesV1.Point0308.input_defined SourceMainFramesV1.Point0308.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0308.outputs.2.hi (by
         change SourceMainFramesV1.Point0308.outputs.2.hi ∈ [SourceMainFramesV1.Point0304.outputs.2.hi, SourceMainFramesV1.Point0305.outputs.2.hi, SourceMainFramesV1.Point0306.outputs.2.hi, SourceMainFramesV1.Point0307.outputs.2.hi, SourceMainFramesV1.Point0308.outputs.2.hi, SourceMainFramesV1.Point0309.outputs.2.hi, SourceMainFramesV1.Point0310.outputs.2.hi, SourceMainFramesV1.Point0311.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=309) domain
     SourceMainFramesV1.Point0309.input_defined SourceMainFramesV1.Point0309.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0309.outputs.2.hi (by
         change SourceMainFramesV1.Point0309.outputs.2.hi ∈ [SourceMainFramesV1.Point0304.outputs.2.hi, SourceMainFramesV1.Point0305.outputs.2.hi, SourceMainFramesV1.Point0306.outputs.2.hi, SourceMainFramesV1.Point0307.outputs.2.hi, SourceMainFramesV1.Point0308.outputs.2.hi, SourceMainFramesV1.Point0309.outputs.2.hi, SourceMainFramesV1.Point0310.outputs.2.hi, SourceMainFramesV1.Point0311.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=310) domain
     SourceMainFramesV1.Point0310.input_defined SourceMainFramesV1.Point0310.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0310.outputs.2.hi (by
         change SourceMainFramesV1.Point0310.outputs.2.hi ∈ [SourceMainFramesV1.Point0304.outputs.2.hi, SourceMainFramesV1.Point0305.outputs.2.hi, SourceMainFramesV1.Point0306.outputs.2.hi, SourceMainFramesV1.Point0307.outputs.2.hi, SourceMainFramesV1.Point0308.outputs.2.hi, SourceMainFramesV1.Point0309.outputs.2.hi, SourceMainFramesV1.Point0310.outputs.2.hi, SourceMainFramesV1.Point0311.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=311) domain
     SourceMainFramesV1.Point0311.input_defined SourceMainFramesV1.Point0311.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0311.outputs.2.hi (by
         change SourceMainFramesV1.Point0311.outputs.2.hi ∈ [SourceMainFramesV1.Point0304.outputs.2.hi, SourceMainFramesV1.Point0305.outputs.2.hi, SourceMainFramesV1.Point0306.outputs.2.hi, SourceMainFramesV1.Point0307.outputs.2.hi, SourceMainFramesV1.Point0308.outputs.2.hi, SourceMainFramesV1.Point0309.outputs.2.hi, SourceMainFramesV1.Point0310.outputs.2.hi, SourceMainFramesV1.Point0311.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block38
