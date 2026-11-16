/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0064
import SourceMainFramesV1.Point0065
import SourceMainFramesV1.Point0066
import SourceMainFramesV1.Point0067
import SourceMainFramesV1.Point0068
import SourceMainFramesV1.Point0069
import SourceMainFramesV1.Point0070
import SourceMainFramesV1.Point0071
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block08
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0064.outputs.2.hi,
 SourceMainFramesV1.Point0065.outputs.2.hi,
 SourceMainFramesV1.Point0066.outputs.2.hi,
 SourceMainFramesV1.Point0067.outputs.2.hi,
 SourceMainFramesV1.Point0068.outputs.2.hi,
 SourceMainFramesV1.Point0069.outputs.2.hi,
 SourceMainFramesV1.Point0070.outputs.2.hi,
 SourceMainFramesV1.Point0071.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 64 ≤ i) (high : i < 72)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=64) domain
     SourceMainFramesV1.Point0064.input_defined SourceMainFramesV1.Point0064.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0064.outputs.2.hi (by
         change SourceMainFramesV1.Point0064.outputs.2.hi ∈ [SourceMainFramesV1.Point0064.outputs.2.hi, SourceMainFramesV1.Point0065.outputs.2.hi, SourceMainFramesV1.Point0066.outputs.2.hi, SourceMainFramesV1.Point0067.outputs.2.hi, SourceMainFramesV1.Point0068.outputs.2.hi, SourceMainFramesV1.Point0069.outputs.2.hi, SourceMainFramesV1.Point0070.outputs.2.hi, SourceMainFramesV1.Point0071.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=65) domain
     SourceMainFramesV1.Point0065.input_defined SourceMainFramesV1.Point0065.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0065.outputs.2.hi (by
         change SourceMainFramesV1.Point0065.outputs.2.hi ∈ [SourceMainFramesV1.Point0064.outputs.2.hi, SourceMainFramesV1.Point0065.outputs.2.hi, SourceMainFramesV1.Point0066.outputs.2.hi, SourceMainFramesV1.Point0067.outputs.2.hi, SourceMainFramesV1.Point0068.outputs.2.hi, SourceMainFramesV1.Point0069.outputs.2.hi, SourceMainFramesV1.Point0070.outputs.2.hi, SourceMainFramesV1.Point0071.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=66) domain
     SourceMainFramesV1.Point0066.input_defined SourceMainFramesV1.Point0066.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0066.outputs.2.hi (by
         change SourceMainFramesV1.Point0066.outputs.2.hi ∈ [SourceMainFramesV1.Point0064.outputs.2.hi, SourceMainFramesV1.Point0065.outputs.2.hi, SourceMainFramesV1.Point0066.outputs.2.hi, SourceMainFramesV1.Point0067.outputs.2.hi, SourceMainFramesV1.Point0068.outputs.2.hi, SourceMainFramesV1.Point0069.outputs.2.hi, SourceMainFramesV1.Point0070.outputs.2.hi, SourceMainFramesV1.Point0071.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=67) domain
     SourceMainFramesV1.Point0067.input_defined SourceMainFramesV1.Point0067.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0067.outputs.2.hi (by
         change SourceMainFramesV1.Point0067.outputs.2.hi ∈ [SourceMainFramesV1.Point0064.outputs.2.hi, SourceMainFramesV1.Point0065.outputs.2.hi, SourceMainFramesV1.Point0066.outputs.2.hi, SourceMainFramesV1.Point0067.outputs.2.hi, SourceMainFramesV1.Point0068.outputs.2.hi, SourceMainFramesV1.Point0069.outputs.2.hi, SourceMainFramesV1.Point0070.outputs.2.hi, SourceMainFramesV1.Point0071.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=68) domain
     SourceMainFramesV1.Point0068.input_defined SourceMainFramesV1.Point0068.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0068.outputs.2.hi (by
         change SourceMainFramesV1.Point0068.outputs.2.hi ∈ [SourceMainFramesV1.Point0064.outputs.2.hi, SourceMainFramesV1.Point0065.outputs.2.hi, SourceMainFramesV1.Point0066.outputs.2.hi, SourceMainFramesV1.Point0067.outputs.2.hi, SourceMainFramesV1.Point0068.outputs.2.hi, SourceMainFramesV1.Point0069.outputs.2.hi, SourceMainFramesV1.Point0070.outputs.2.hi, SourceMainFramesV1.Point0071.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=69) domain
     SourceMainFramesV1.Point0069.input_defined SourceMainFramesV1.Point0069.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0069.outputs.2.hi (by
         change SourceMainFramesV1.Point0069.outputs.2.hi ∈ [SourceMainFramesV1.Point0064.outputs.2.hi, SourceMainFramesV1.Point0065.outputs.2.hi, SourceMainFramesV1.Point0066.outputs.2.hi, SourceMainFramesV1.Point0067.outputs.2.hi, SourceMainFramesV1.Point0068.outputs.2.hi, SourceMainFramesV1.Point0069.outputs.2.hi, SourceMainFramesV1.Point0070.outputs.2.hi, SourceMainFramesV1.Point0071.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=70) domain
     SourceMainFramesV1.Point0070.input_defined SourceMainFramesV1.Point0070.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0070.outputs.2.hi (by
         change SourceMainFramesV1.Point0070.outputs.2.hi ∈ [SourceMainFramesV1.Point0064.outputs.2.hi, SourceMainFramesV1.Point0065.outputs.2.hi, SourceMainFramesV1.Point0066.outputs.2.hi, SourceMainFramesV1.Point0067.outputs.2.hi, SourceMainFramesV1.Point0068.outputs.2.hi, SourceMainFramesV1.Point0069.outputs.2.hi, SourceMainFramesV1.Point0070.outputs.2.hi, SourceMainFramesV1.Point0071.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=71) domain
     SourceMainFramesV1.Point0071.input_defined SourceMainFramesV1.Point0071.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0071.outputs.2.hi (by
         change SourceMainFramesV1.Point0071.outputs.2.hi ∈ [SourceMainFramesV1.Point0064.outputs.2.hi, SourceMainFramesV1.Point0065.outputs.2.hi, SourceMainFramesV1.Point0066.outputs.2.hi, SourceMainFramesV1.Point0067.outputs.2.hi, SourceMainFramesV1.Point0068.outputs.2.hi, SourceMainFramesV1.Point0069.outputs.2.hi, SourceMainFramesV1.Point0070.outputs.2.hi, SourceMainFramesV1.Point0071.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block08
