/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0344
import SourceMainFramesV1.Point0345
import SourceMainFramesV1.Point0346
import SourceMainFramesV1.Point0347
import SourceMainFramesV1.Point0348
import SourceMainFramesV1.Point0349
import SourceMainFramesV1.Point0350
import SourceMainFramesV1.Point0351
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block43
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0344.outputs.2.hi,
 SourceMainFramesV1.Point0345.outputs.2.hi,
 SourceMainFramesV1.Point0346.outputs.2.hi,
 SourceMainFramesV1.Point0347.outputs.2.hi,
 SourceMainFramesV1.Point0348.outputs.2.hi,
 SourceMainFramesV1.Point0349.outputs.2.hi,
 SourceMainFramesV1.Point0350.outputs.2.hi,
 SourceMainFramesV1.Point0351.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 344 ≤ i) (high : i < 352)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=344) domain
     SourceMainFramesV1.Point0344.input_defined SourceMainFramesV1.Point0344.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0344.outputs.2.hi (by
         change SourceMainFramesV1.Point0344.outputs.2.hi ∈ [SourceMainFramesV1.Point0344.outputs.2.hi, SourceMainFramesV1.Point0345.outputs.2.hi, SourceMainFramesV1.Point0346.outputs.2.hi, SourceMainFramesV1.Point0347.outputs.2.hi, SourceMainFramesV1.Point0348.outputs.2.hi, SourceMainFramesV1.Point0349.outputs.2.hi, SourceMainFramesV1.Point0350.outputs.2.hi, SourceMainFramesV1.Point0351.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=345) domain
     SourceMainFramesV1.Point0345.input_defined SourceMainFramesV1.Point0345.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0345.outputs.2.hi (by
         change SourceMainFramesV1.Point0345.outputs.2.hi ∈ [SourceMainFramesV1.Point0344.outputs.2.hi, SourceMainFramesV1.Point0345.outputs.2.hi, SourceMainFramesV1.Point0346.outputs.2.hi, SourceMainFramesV1.Point0347.outputs.2.hi, SourceMainFramesV1.Point0348.outputs.2.hi, SourceMainFramesV1.Point0349.outputs.2.hi, SourceMainFramesV1.Point0350.outputs.2.hi, SourceMainFramesV1.Point0351.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=346) domain
     SourceMainFramesV1.Point0346.input_defined SourceMainFramesV1.Point0346.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0346.outputs.2.hi (by
         change SourceMainFramesV1.Point0346.outputs.2.hi ∈ [SourceMainFramesV1.Point0344.outputs.2.hi, SourceMainFramesV1.Point0345.outputs.2.hi, SourceMainFramesV1.Point0346.outputs.2.hi, SourceMainFramesV1.Point0347.outputs.2.hi, SourceMainFramesV1.Point0348.outputs.2.hi, SourceMainFramesV1.Point0349.outputs.2.hi, SourceMainFramesV1.Point0350.outputs.2.hi, SourceMainFramesV1.Point0351.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=347) domain
     SourceMainFramesV1.Point0347.input_defined SourceMainFramesV1.Point0347.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0347.outputs.2.hi (by
         change SourceMainFramesV1.Point0347.outputs.2.hi ∈ [SourceMainFramesV1.Point0344.outputs.2.hi, SourceMainFramesV1.Point0345.outputs.2.hi, SourceMainFramesV1.Point0346.outputs.2.hi, SourceMainFramesV1.Point0347.outputs.2.hi, SourceMainFramesV1.Point0348.outputs.2.hi, SourceMainFramesV1.Point0349.outputs.2.hi, SourceMainFramesV1.Point0350.outputs.2.hi, SourceMainFramesV1.Point0351.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=348) domain
     SourceMainFramesV1.Point0348.input_defined SourceMainFramesV1.Point0348.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0348.outputs.2.hi (by
         change SourceMainFramesV1.Point0348.outputs.2.hi ∈ [SourceMainFramesV1.Point0344.outputs.2.hi, SourceMainFramesV1.Point0345.outputs.2.hi, SourceMainFramesV1.Point0346.outputs.2.hi, SourceMainFramesV1.Point0347.outputs.2.hi, SourceMainFramesV1.Point0348.outputs.2.hi, SourceMainFramesV1.Point0349.outputs.2.hi, SourceMainFramesV1.Point0350.outputs.2.hi, SourceMainFramesV1.Point0351.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=349) domain
     SourceMainFramesV1.Point0349.input_defined SourceMainFramesV1.Point0349.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0349.outputs.2.hi (by
         change SourceMainFramesV1.Point0349.outputs.2.hi ∈ [SourceMainFramesV1.Point0344.outputs.2.hi, SourceMainFramesV1.Point0345.outputs.2.hi, SourceMainFramesV1.Point0346.outputs.2.hi, SourceMainFramesV1.Point0347.outputs.2.hi, SourceMainFramesV1.Point0348.outputs.2.hi, SourceMainFramesV1.Point0349.outputs.2.hi, SourceMainFramesV1.Point0350.outputs.2.hi, SourceMainFramesV1.Point0351.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=350) domain
     SourceMainFramesV1.Point0350.input_defined SourceMainFramesV1.Point0350.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0350.outputs.2.hi (by
         change SourceMainFramesV1.Point0350.outputs.2.hi ∈ [SourceMainFramesV1.Point0344.outputs.2.hi, SourceMainFramesV1.Point0345.outputs.2.hi, SourceMainFramesV1.Point0346.outputs.2.hi, SourceMainFramesV1.Point0347.outputs.2.hi, SourceMainFramesV1.Point0348.outputs.2.hi, SourceMainFramesV1.Point0349.outputs.2.hi, SourceMainFramesV1.Point0350.outputs.2.hi, SourceMainFramesV1.Point0351.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=351) domain
     SourceMainFramesV1.Point0351.input_defined SourceMainFramesV1.Point0351.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0351.outputs.2.hi (by
         change SourceMainFramesV1.Point0351.outputs.2.hi ∈ [SourceMainFramesV1.Point0344.outputs.2.hi, SourceMainFramesV1.Point0345.outputs.2.hi, SourceMainFramesV1.Point0346.outputs.2.hi, SourceMainFramesV1.Point0347.outputs.2.hi, SourceMainFramesV1.Point0348.outputs.2.hi, SourceMainFramesV1.Point0349.outputs.2.hi, SourceMainFramesV1.Point0350.outputs.2.hi, SourceMainFramesV1.Point0351.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block43
