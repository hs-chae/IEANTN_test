/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0616
import SourceMainFramesV1.Point0617
import SourceMainFramesV1.Point0618
import SourceMainFramesV1.Point0619
import SourceMainFramesV1.Point0620
import SourceMainFramesV1.Point0621
import SourceMainFramesV1.Point0622
import SourceMainFramesV1.Point0623
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block77
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0616.outputs.2.hi,
 SourceMainFramesV1.Point0617.outputs.2.hi,
 SourceMainFramesV1.Point0618.outputs.2.hi,
 SourceMainFramesV1.Point0619.outputs.2.hi,
 SourceMainFramesV1.Point0620.outputs.2.hi,
 SourceMainFramesV1.Point0621.outputs.2.hi,
 SourceMainFramesV1.Point0622.outputs.2.hi,
 SourceMainFramesV1.Point0623.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 616 ≤ i) (high : i < 624)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=616) domain
     SourceMainFramesV1.Point0616.input_defined SourceMainFramesV1.Point0616.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0616.outputs.2.hi (by
         change SourceMainFramesV1.Point0616.outputs.2.hi ∈ [SourceMainFramesV1.Point0616.outputs.2.hi, SourceMainFramesV1.Point0617.outputs.2.hi, SourceMainFramesV1.Point0618.outputs.2.hi, SourceMainFramesV1.Point0619.outputs.2.hi, SourceMainFramesV1.Point0620.outputs.2.hi, SourceMainFramesV1.Point0621.outputs.2.hi, SourceMainFramesV1.Point0622.outputs.2.hi, SourceMainFramesV1.Point0623.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=617) domain
     SourceMainFramesV1.Point0617.input_defined SourceMainFramesV1.Point0617.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0617.outputs.2.hi (by
         change SourceMainFramesV1.Point0617.outputs.2.hi ∈ [SourceMainFramesV1.Point0616.outputs.2.hi, SourceMainFramesV1.Point0617.outputs.2.hi, SourceMainFramesV1.Point0618.outputs.2.hi, SourceMainFramesV1.Point0619.outputs.2.hi, SourceMainFramesV1.Point0620.outputs.2.hi, SourceMainFramesV1.Point0621.outputs.2.hi, SourceMainFramesV1.Point0622.outputs.2.hi, SourceMainFramesV1.Point0623.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=618) domain
     SourceMainFramesV1.Point0618.input_defined SourceMainFramesV1.Point0618.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0618.outputs.2.hi (by
         change SourceMainFramesV1.Point0618.outputs.2.hi ∈ [SourceMainFramesV1.Point0616.outputs.2.hi, SourceMainFramesV1.Point0617.outputs.2.hi, SourceMainFramesV1.Point0618.outputs.2.hi, SourceMainFramesV1.Point0619.outputs.2.hi, SourceMainFramesV1.Point0620.outputs.2.hi, SourceMainFramesV1.Point0621.outputs.2.hi, SourceMainFramesV1.Point0622.outputs.2.hi, SourceMainFramesV1.Point0623.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=619) domain
     SourceMainFramesV1.Point0619.input_defined SourceMainFramesV1.Point0619.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0619.outputs.2.hi (by
         change SourceMainFramesV1.Point0619.outputs.2.hi ∈ [SourceMainFramesV1.Point0616.outputs.2.hi, SourceMainFramesV1.Point0617.outputs.2.hi, SourceMainFramesV1.Point0618.outputs.2.hi, SourceMainFramesV1.Point0619.outputs.2.hi, SourceMainFramesV1.Point0620.outputs.2.hi, SourceMainFramesV1.Point0621.outputs.2.hi, SourceMainFramesV1.Point0622.outputs.2.hi, SourceMainFramesV1.Point0623.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=620) domain
     SourceMainFramesV1.Point0620.input_defined SourceMainFramesV1.Point0620.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0620.outputs.2.hi (by
         change SourceMainFramesV1.Point0620.outputs.2.hi ∈ [SourceMainFramesV1.Point0616.outputs.2.hi, SourceMainFramesV1.Point0617.outputs.2.hi, SourceMainFramesV1.Point0618.outputs.2.hi, SourceMainFramesV1.Point0619.outputs.2.hi, SourceMainFramesV1.Point0620.outputs.2.hi, SourceMainFramesV1.Point0621.outputs.2.hi, SourceMainFramesV1.Point0622.outputs.2.hi, SourceMainFramesV1.Point0623.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=621) domain
     SourceMainFramesV1.Point0621.input_defined SourceMainFramesV1.Point0621.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0621.outputs.2.hi (by
         change SourceMainFramesV1.Point0621.outputs.2.hi ∈ [SourceMainFramesV1.Point0616.outputs.2.hi, SourceMainFramesV1.Point0617.outputs.2.hi, SourceMainFramesV1.Point0618.outputs.2.hi, SourceMainFramesV1.Point0619.outputs.2.hi, SourceMainFramesV1.Point0620.outputs.2.hi, SourceMainFramesV1.Point0621.outputs.2.hi, SourceMainFramesV1.Point0622.outputs.2.hi, SourceMainFramesV1.Point0623.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=622) domain
     SourceMainFramesV1.Point0622.input_defined SourceMainFramesV1.Point0622.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0622.outputs.2.hi (by
         change SourceMainFramesV1.Point0622.outputs.2.hi ∈ [SourceMainFramesV1.Point0616.outputs.2.hi, SourceMainFramesV1.Point0617.outputs.2.hi, SourceMainFramesV1.Point0618.outputs.2.hi, SourceMainFramesV1.Point0619.outputs.2.hi, SourceMainFramesV1.Point0620.outputs.2.hi, SourceMainFramesV1.Point0621.outputs.2.hi, SourceMainFramesV1.Point0622.outputs.2.hi, SourceMainFramesV1.Point0623.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=623) domain
     SourceMainFramesV1.Point0623.input_defined SourceMainFramesV1.Point0623.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0623.outputs.2.hi (by
         change SourceMainFramesV1.Point0623.outputs.2.hi ∈ [SourceMainFramesV1.Point0616.outputs.2.hi, SourceMainFramesV1.Point0617.outputs.2.hi, SourceMainFramesV1.Point0618.outputs.2.hi, SourceMainFramesV1.Point0619.outputs.2.hi, SourceMainFramesV1.Point0620.outputs.2.hi, SourceMainFramesV1.Point0621.outputs.2.hi, SourceMainFramesV1.Point0622.outputs.2.hi, SourceMainFramesV1.Point0623.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block77
