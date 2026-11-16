/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0152
import SourceMainFramesV1.Point0153
import SourceMainFramesV1.Point0154
import SourceMainFramesV1.Point0155
import SourceMainFramesV1.Point0156
import SourceMainFramesV1.Point0157
import SourceMainFramesV1.Point0158
import SourceMainFramesV1.Point0159
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block19
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0152.outputs.2.hi,
 SourceMainFramesV1.Point0153.outputs.2.hi,
 SourceMainFramesV1.Point0154.outputs.2.hi,
 SourceMainFramesV1.Point0155.outputs.2.hi,
 SourceMainFramesV1.Point0156.outputs.2.hi,
 SourceMainFramesV1.Point0157.outputs.2.hi,
 SourceMainFramesV1.Point0158.outputs.2.hi,
 SourceMainFramesV1.Point0159.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 152 ≤ i) (high : i < 160)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=152) domain
     SourceMainFramesV1.Point0152.input_defined SourceMainFramesV1.Point0152.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0152.outputs.2.hi (by
         change SourceMainFramesV1.Point0152.outputs.2.hi ∈ [SourceMainFramesV1.Point0152.outputs.2.hi, SourceMainFramesV1.Point0153.outputs.2.hi, SourceMainFramesV1.Point0154.outputs.2.hi, SourceMainFramesV1.Point0155.outputs.2.hi, SourceMainFramesV1.Point0156.outputs.2.hi, SourceMainFramesV1.Point0157.outputs.2.hi, SourceMainFramesV1.Point0158.outputs.2.hi, SourceMainFramesV1.Point0159.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=153) domain
     SourceMainFramesV1.Point0153.input_defined SourceMainFramesV1.Point0153.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0153.outputs.2.hi (by
         change SourceMainFramesV1.Point0153.outputs.2.hi ∈ [SourceMainFramesV1.Point0152.outputs.2.hi, SourceMainFramesV1.Point0153.outputs.2.hi, SourceMainFramesV1.Point0154.outputs.2.hi, SourceMainFramesV1.Point0155.outputs.2.hi, SourceMainFramesV1.Point0156.outputs.2.hi, SourceMainFramesV1.Point0157.outputs.2.hi, SourceMainFramesV1.Point0158.outputs.2.hi, SourceMainFramesV1.Point0159.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=154) domain
     SourceMainFramesV1.Point0154.input_defined SourceMainFramesV1.Point0154.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0154.outputs.2.hi (by
         change SourceMainFramesV1.Point0154.outputs.2.hi ∈ [SourceMainFramesV1.Point0152.outputs.2.hi, SourceMainFramesV1.Point0153.outputs.2.hi, SourceMainFramesV1.Point0154.outputs.2.hi, SourceMainFramesV1.Point0155.outputs.2.hi, SourceMainFramesV1.Point0156.outputs.2.hi, SourceMainFramesV1.Point0157.outputs.2.hi, SourceMainFramesV1.Point0158.outputs.2.hi, SourceMainFramesV1.Point0159.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=155) domain
     SourceMainFramesV1.Point0155.input_defined SourceMainFramesV1.Point0155.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0155.outputs.2.hi (by
         change SourceMainFramesV1.Point0155.outputs.2.hi ∈ [SourceMainFramesV1.Point0152.outputs.2.hi, SourceMainFramesV1.Point0153.outputs.2.hi, SourceMainFramesV1.Point0154.outputs.2.hi, SourceMainFramesV1.Point0155.outputs.2.hi, SourceMainFramesV1.Point0156.outputs.2.hi, SourceMainFramesV1.Point0157.outputs.2.hi, SourceMainFramesV1.Point0158.outputs.2.hi, SourceMainFramesV1.Point0159.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=156) domain
     SourceMainFramesV1.Point0156.input_defined SourceMainFramesV1.Point0156.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0156.outputs.2.hi (by
         change SourceMainFramesV1.Point0156.outputs.2.hi ∈ [SourceMainFramesV1.Point0152.outputs.2.hi, SourceMainFramesV1.Point0153.outputs.2.hi, SourceMainFramesV1.Point0154.outputs.2.hi, SourceMainFramesV1.Point0155.outputs.2.hi, SourceMainFramesV1.Point0156.outputs.2.hi, SourceMainFramesV1.Point0157.outputs.2.hi, SourceMainFramesV1.Point0158.outputs.2.hi, SourceMainFramesV1.Point0159.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=157) domain
     SourceMainFramesV1.Point0157.input_defined SourceMainFramesV1.Point0157.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0157.outputs.2.hi (by
         change SourceMainFramesV1.Point0157.outputs.2.hi ∈ [SourceMainFramesV1.Point0152.outputs.2.hi, SourceMainFramesV1.Point0153.outputs.2.hi, SourceMainFramesV1.Point0154.outputs.2.hi, SourceMainFramesV1.Point0155.outputs.2.hi, SourceMainFramesV1.Point0156.outputs.2.hi, SourceMainFramesV1.Point0157.outputs.2.hi, SourceMainFramesV1.Point0158.outputs.2.hi, SourceMainFramesV1.Point0159.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=158) domain
     SourceMainFramesV1.Point0158.input_defined SourceMainFramesV1.Point0158.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0158.outputs.2.hi (by
         change SourceMainFramesV1.Point0158.outputs.2.hi ∈ [SourceMainFramesV1.Point0152.outputs.2.hi, SourceMainFramesV1.Point0153.outputs.2.hi, SourceMainFramesV1.Point0154.outputs.2.hi, SourceMainFramesV1.Point0155.outputs.2.hi, SourceMainFramesV1.Point0156.outputs.2.hi, SourceMainFramesV1.Point0157.outputs.2.hi, SourceMainFramesV1.Point0158.outputs.2.hi, SourceMainFramesV1.Point0159.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=159) domain
     SourceMainFramesV1.Point0159.input_defined SourceMainFramesV1.Point0159.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0159.outputs.2.hi (by
         change SourceMainFramesV1.Point0159.outputs.2.hi ∈ [SourceMainFramesV1.Point0152.outputs.2.hi, SourceMainFramesV1.Point0153.outputs.2.hi, SourceMainFramesV1.Point0154.outputs.2.hi, SourceMainFramesV1.Point0155.outputs.2.hi, SourceMainFramesV1.Point0156.outputs.2.hi, SourceMainFramesV1.Point0157.outputs.2.hi, SourceMainFramesV1.Point0158.outputs.2.hi, SourceMainFramesV1.Point0159.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block19
