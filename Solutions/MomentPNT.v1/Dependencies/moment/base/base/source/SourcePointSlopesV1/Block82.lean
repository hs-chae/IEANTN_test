/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0656
import SourceMainFramesV1.Point0657
import SourceMainFramesV1.Point0658
import SourceMainFramesV1.Point0659
import SourceMainFramesV1.Point0660
import SourceMainFramesV1.Point0661
import SourceMainFramesV1.Point0662
import SourceMainFramesV1.Point0663
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block82
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0656.outputs.2.hi,
 SourceMainFramesV1.Point0657.outputs.2.hi,
 SourceMainFramesV1.Point0658.outputs.2.hi,
 SourceMainFramesV1.Point0659.outputs.2.hi,
 SourceMainFramesV1.Point0660.outputs.2.hi,
 SourceMainFramesV1.Point0661.outputs.2.hi,
 SourceMainFramesV1.Point0662.outputs.2.hi,
 SourceMainFramesV1.Point0663.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 656 ≤ i) (high : i < 664)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=656) domain
     SourceMainFramesV1.Point0656.input_defined SourceMainFramesV1.Point0656.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0656.outputs.2.hi (by
         change SourceMainFramesV1.Point0656.outputs.2.hi ∈ [SourceMainFramesV1.Point0656.outputs.2.hi, SourceMainFramesV1.Point0657.outputs.2.hi, SourceMainFramesV1.Point0658.outputs.2.hi, SourceMainFramesV1.Point0659.outputs.2.hi, SourceMainFramesV1.Point0660.outputs.2.hi, SourceMainFramesV1.Point0661.outputs.2.hi, SourceMainFramesV1.Point0662.outputs.2.hi, SourceMainFramesV1.Point0663.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=657) domain
     SourceMainFramesV1.Point0657.input_defined SourceMainFramesV1.Point0657.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0657.outputs.2.hi (by
         change SourceMainFramesV1.Point0657.outputs.2.hi ∈ [SourceMainFramesV1.Point0656.outputs.2.hi, SourceMainFramesV1.Point0657.outputs.2.hi, SourceMainFramesV1.Point0658.outputs.2.hi, SourceMainFramesV1.Point0659.outputs.2.hi, SourceMainFramesV1.Point0660.outputs.2.hi, SourceMainFramesV1.Point0661.outputs.2.hi, SourceMainFramesV1.Point0662.outputs.2.hi, SourceMainFramesV1.Point0663.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=658) domain
     SourceMainFramesV1.Point0658.input_defined SourceMainFramesV1.Point0658.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0658.outputs.2.hi (by
         change SourceMainFramesV1.Point0658.outputs.2.hi ∈ [SourceMainFramesV1.Point0656.outputs.2.hi, SourceMainFramesV1.Point0657.outputs.2.hi, SourceMainFramesV1.Point0658.outputs.2.hi, SourceMainFramesV1.Point0659.outputs.2.hi, SourceMainFramesV1.Point0660.outputs.2.hi, SourceMainFramesV1.Point0661.outputs.2.hi, SourceMainFramesV1.Point0662.outputs.2.hi, SourceMainFramesV1.Point0663.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=659) domain
     SourceMainFramesV1.Point0659.input_defined SourceMainFramesV1.Point0659.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0659.outputs.2.hi (by
         change SourceMainFramesV1.Point0659.outputs.2.hi ∈ [SourceMainFramesV1.Point0656.outputs.2.hi, SourceMainFramesV1.Point0657.outputs.2.hi, SourceMainFramesV1.Point0658.outputs.2.hi, SourceMainFramesV1.Point0659.outputs.2.hi, SourceMainFramesV1.Point0660.outputs.2.hi, SourceMainFramesV1.Point0661.outputs.2.hi, SourceMainFramesV1.Point0662.outputs.2.hi, SourceMainFramesV1.Point0663.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=660) domain
     SourceMainFramesV1.Point0660.input_defined SourceMainFramesV1.Point0660.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0660.outputs.2.hi (by
         change SourceMainFramesV1.Point0660.outputs.2.hi ∈ [SourceMainFramesV1.Point0656.outputs.2.hi, SourceMainFramesV1.Point0657.outputs.2.hi, SourceMainFramesV1.Point0658.outputs.2.hi, SourceMainFramesV1.Point0659.outputs.2.hi, SourceMainFramesV1.Point0660.outputs.2.hi, SourceMainFramesV1.Point0661.outputs.2.hi, SourceMainFramesV1.Point0662.outputs.2.hi, SourceMainFramesV1.Point0663.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=661) domain
     SourceMainFramesV1.Point0661.input_defined SourceMainFramesV1.Point0661.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0661.outputs.2.hi (by
         change SourceMainFramesV1.Point0661.outputs.2.hi ∈ [SourceMainFramesV1.Point0656.outputs.2.hi, SourceMainFramesV1.Point0657.outputs.2.hi, SourceMainFramesV1.Point0658.outputs.2.hi, SourceMainFramesV1.Point0659.outputs.2.hi, SourceMainFramesV1.Point0660.outputs.2.hi, SourceMainFramesV1.Point0661.outputs.2.hi, SourceMainFramesV1.Point0662.outputs.2.hi, SourceMainFramesV1.Point0663.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=662) domain
     SourceMainFramesV1.Point0662.input_defined SourceMainFramesV1.Point0662.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0662.outputs.2.hi (by
         change SourceMainFramesV1.Point0662.outputs.2.hi ∈ [SourceMainFramesV1.Point0656.outputs.2.hi, SourceMainFramesV1.Point0657.outputs.2.hi, SourceMainFramesV1.Point0658.outputs.2.hi, SourceMainFramesV1.Point0659.outputs.2.hi, SourceMainFramesV1.Point0660.outputs.2.hi, SourceMainFramesV1.Point0661.outputs.2.hi, SourceMainFramesV1.Point0662.outputs.2.hi, SourceMainFramesV1.Point0663.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=663) domain
     SourceMainFramesV1.Point0663.input_defined SourceMainFramesV1.Point0663.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0663.outputs.2.hi (by
         change SourceMainFramesV1.Point0663.outputs.2.hi ∈ [SourceMainFramesV1.Point0656.outputs.2.hi, SourceMainFramesV1.Point0657.outputs.2.hi, SourceMainFramesV1.Point0658.outputs.2.hi, SourceMainFramesV1.Point0659.outputs.2.hi, SourceMainFramesV1.Point0660.outputs.2.hi, SourceMainFramesV1.Point0661.outputs.2.hi, SourceMainFramesV1.Point0662.outputs.2.hi, SourceMainFramesV1.Point0663.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block82
