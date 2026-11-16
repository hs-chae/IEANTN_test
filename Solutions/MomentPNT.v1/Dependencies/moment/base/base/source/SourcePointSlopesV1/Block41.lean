/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0328
import SourceMainFramesV1.Point0329
import SourceMainFramesV1.Point0330
import SourceMainFramesV1.Point0331
import SourceMainFramesV1.Point0332
import SourceMainFramesV1.Point0333
import SourceMainFramesV1.Point0334
import SourceMainFramesV1.Point0335
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block41
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0328.outputs.2.hi,
 SourceMainFramesV1.Point0329.outputs.2.hi,
 SourceMainFramesV1.Point0330.outputs.2.hi,
 SourceMainFramesV1.Point0331.outputs.2.hi,
 SourceMainFramesV1.Point0332.outputs.2.hi,
 SourceMainFramesV1.Point0333.outputs.2.hi,
 SourceMainFramesV1.Point0334.outputs.2.hi,
 SourceMainFramesV1.Point0335.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 328 ≤ i) (high : i < 336)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=328) domain
     SourceMainFramesV1.Point0328.input_defined SourceMainFramesV1.Point0328.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0328.outputs.2.hi (by
         change SourceMainFramesV1.Point0328.outputs.2.hi ∈ [SourceMainFramesV1.Point0328.outputs.2.hi, SourceMainFramesV1.Point0329.outputs.2.hi, SourceMainFramesV1.Point0330.outputs.2.hi, SourceMainFramesV1.Point0331.outputs.2.hi, SourceMainFramesV1.Point0332.outputs.2.hi, SourceMainFramesV1.Point0333.outputs.2.hi, SourceMainFramesV1.Point0334.outputs.2.hi, SourceMainFramesV1.Point0335.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=329) domain
     SourceMainFramesV1.Point0329.input_defined SourceMainFramesV1.Point0329.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0329.outputs.2.hi (by
         change SourceMainFramesV1.Point0329.outputs.2.hi ∈ [SourceMainFramesV1.Point0328.outputs.2.hi, SourceMainFramesV1.Point0329.outputs.2.hi, SourceMainFramesV1.Point0330.outputs.2.hi, SourceMainFramesV1.Point0331.outputs.2.hi, SourceMainFramesV1.Point0332.outputs.2.hi, SourceMainFramesV1.Point0333.outputs.2.hi, SourceMainFramesV1.Point0334.outputs.2.hi, SourceMainFramesV1.Point0335.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=330) domain
     SourceMainFramesV1.Point0330.input_defined SourceMainFramesV1.Point0330.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0330.outputs.2.hi (by
         change SourceMainFramesV1.Point0330.outputs.2.hi ∈ [SourceMainFramesV1.Point0328.outputs.2.hi, SourceMainFramesV1.Point0329.outputs.2.hi, SourceMainFramesV1.Point0330.outputs.2.hi, SourceMainFramesV1.Point0331.outputs.2.hi, SourceMainFramesV1.Point0332.outputs.2.hi, SourceMainFramesV1.Point0333.outputs.2.hi, SourceMainFramesV1.Point0334.outputs.2.hi, SourceMainFramesV1.Point0335.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=331) domain
     SourceMainFramesV1.Point0331.input_defined SourceMainFramesV1.Point0331.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0331.outputs.2.hi (by
         change SourceMainFramesV1.Point0331.outputs.2.hi ∈ [SourceMainFramesV1.Point0328.outputs.2.hi, SourceMainFramesV1.Point0329.outputs.2.hi, SourceMainFramesV1.Point0330.outputs.2.hi, SourceMainFramesV1.Point0331.outputs.2.hi, SourceMainFramesV1.Point0332.outputs.2.hi, SourceMainFramesV1.Point0333.outputs.2.hi, SourceMainFramesV1.Point0334.outputs.2.hi, SourceMainFramesV1.Point0335.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=332) domain
     SourceMainFramesV1.Point0332.input_defined SourceMainFramesV1.Point0332.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0332.outputs.2.hi (by
         change SourceMainFramesV1.Point0332.outputs.2.hi ∈ [SourceMainFramesV1.Point0328.outputs.2.hi, SourceMainFramesV1.Point0329.outputs.2.hi, SourceMainFramesV1.Point0330.outputs.2.hi, SourceMainFramesV1.Point0331.outputs.2.hi, SourceMainFramesV1.Point0332.outputs.2.hi, SourceMainFramesV1.Point0333.outputs.2.hi, SourceMainFramesV1.Point0334.outputs.2.hi, SourceMainFramesV1.Point0335.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=333) domain
     SourceMainFramesV1.Point0333.input_defined SourceMainFramesV1.Point0333.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0333.outputs.2.hi (by
         change SourceMainFramesV1.Point0333.outputs.2.hi ∈ [SourceMainFramesV1.Point0328.outputs.2.hi, SourceMainFramesV1.Point0329.outputs.2.hi, SourceMainFramesV1.Point0330.outputs.2.hi, SourceMainFramesV1.Point0331.outputs.2.hi, SourceMainFramesV1.Point0332.outputs.2.hi, SourceMainFramesV1.Point0333.outputs.2.hi, SourceMainFramesV1.Point0334.outputs.2.hi, SourceMainFramesV1.Point0335.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=334) domain
     SourceMainFramesV1.Point0334.input_defined SourceMainFramesV1.Point0334.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0334.outputs.2.hi (by
         change SourceMainFramesV1.Point0334.outputs.2.hi ∈ [SourceMainFramesV1.Point0328.outputs.2.hi, SourceMainFramesV1.Point0329.outputs.2.hi, SourceMainFramesV1.Point0330.outputs.2.hi, SourceMainFramesV1.Point0331.outputs.2.hi, SourceMainFramesV1.Point0332.outputs.2.hi, SourceMainFramesV1.Point0333.outputs.2.hi, SourceMainFramesV1.Point0334.outputs.2.hi, SourceMainFramesV1.Point0335.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=335) domain
     SourceMainFramesV1.Point0335.input_defined SourceMainFramesV1.Point0335.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0335.outputs.2.hi (by
         change SourceMainFramesV1.Point0335.outputs.2.hi ∈ [SourceMainFramesV1.Point0328.outputs.2.hi, SourceMainFramesV1.Point0329.outputs.2.hi, SourceMainFramesV1.Point0330.outputs.2.hi, SourceMainFramesV1.Point0331.outputs.2.hi, SourceMainFramesV1.Point0332.outputs.2.hi, SourceMainFramesV1.Point0333.outputs.2.hi, SourceMainFramesV1.Point0334.outputs.2.hi, SourceMainFramesV1.Point0335.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block41
