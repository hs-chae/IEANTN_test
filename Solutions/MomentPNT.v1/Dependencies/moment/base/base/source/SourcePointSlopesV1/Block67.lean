/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0536
import SourceMainFramesV1.Point0537
import SourceMainFramesV1.Point0538
import SourceMainFramesV1.Point0539
import SourceMainFramesV1.Point0540
import SourceMainFramesV1.Point0541
import SourceMainFramesV1.Point0542
import SourceMainFramesV1.Point0543
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block67
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0536.outputs.2.hi,
 SourceMainFramesV1.Point0537.outputs.2.hi,
 SourceMainFramesV1.Point0538.outputs.2.hi,
 SourceMainFramesV1.Point0539.outputs.2.hi,
 SourceMainFramesV1.Point0540.outputs.2.hi,
 SourceMainFramesV1.Point0541.outputs.2.hi,
 SourceMainFramesV1.Point0542.outputs.2.hi,
 SourceMainFramesV1.Point0543.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 536 ≤ i) (high : i < 544)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=536) domain
     SourceMainFramesV1.Point0536.input_defined SourceMainFramesV1.Point0536.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0536.outputs.2.hi (by
         change SourceMainFramesV1.Point0536.outputs.2.hi ∈ [SourceMainFramesV1.Point0536.outputs.2.hi, SourceMainFramesV1.Point0537.outputs.2.hi, SourceMainFramesV1.Point0538.outputs.2.hi, SourceMainFramesV1.Point0539.outputs.2.hi, SourceMainFramesV1.Point0540.outputs.2.hi, SourceMainFramesV1.Point0541.outputs.2.hi, SourceMainFramesV1.Point0542.outputs.2.hi, SourceMainFramesV1.Point0543.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=537) domain
     SourceMainFramesV1.Point0537.input_defined SourceMainFramesV1.Point0537.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0537.outputs.2.hi (by
         change SourceMainFramesV1.Point0537.outputs.2.hi ∈ [SourceMainFramesV1.Point0536.outputs.2.hi, SourceMainFramesV1.Point0537.outputs.2.hi, SourceMainFramesV1.Point0538.outputs.2.hi, SourceMainFramesV1.Point0539.outputs.2.hi, SourceMainFramesV1.Point0540.outputs.2.hi, SourceMainFramesV1.Point0541.outputs.2.hi, SourceMainFramesV1.Point0542.outputs.2.hi, SourceMainFramesV1.Point0543.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=538) domain
     SourceMainFramesV1.Point0538.input_defined SourceMainFramesV1.Point0538.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0538.outputs.2.hi (by
         change SourceMainFramesV1.Point0538.outputs.2.hi ∈ [SourceMainFramesV1.Point0536.outputs.2.hi, SourceMainFramesV1.Point0537.outputs.2.hi, SourceMainFramesV1.Point0538.outputs.2.hi, SourceMainFramesV1.Point0539.outputs.2.hi, SourceMainFramesV1.Point0540.outputs.2.hi, SourceMainFramesV1.Point0541.outputs.2.hi, SourceMainFramesV1.Point0542.outputs.2.hi, SourceMainFramesV1.Point0543.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=539) domain
     SourceMainFramesV1.Point0539.input_defined SourceMainFramesV1.Point0539.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0539.outputs.2.hi (by
         change SourceMainFramesV1.Point0539.outputs.2.hi ∈ [SourceMainFramesV1.Point0536.outputs.2.hi, SourceMainFramesV1.Point0537.outputs.2.hi, SourceMainFramesV1.Point0538.outputs.2.hi, SourceMainFramesV1.Point0539.outputs.2.hi, SourceMainFramesV1.Point0540.outputs.2.hi, SourceMainFramesV1.Point0541.outputs.2.hi, SourceMainFramesV1.Point0542.outputs.2.hi, SourceMainFramesV1.Point0543.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=540) domain
     SourceMainFramesV1.Point0540.input_defined SourceMainFramesV1.Point0540.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0540.outputs.2.hi (by
         change SourceMainFramesV1.Point0540.outputs.2.hi ∈ [SourceMainFramesV1.Point0536.outputs.2.hi, SourceMainFramesV1.Point0537.outputs.2.hi, SourceMainFramesV1.Point0538.outputs.2.hi, SourceMainFramesV1.Point0539.outputs.2.hi, SourceMainFramesV1.Point0540.outputs.2.hi, SourceMainFramesV1.Point0541.outputs.2.hi, SourceMainFramesV1.Point0542.outputs.2.hi, SourceMainFramesV1.Point0543.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=541) domain
     SourceMainFramesV1.Point0541.input_defined SourceMainFramesV1.Point0541.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0541.outputs.2.hi (by
         change SourceMainFramesV1.Point0541.outputs.2.hi ∈ [SourceMainFramesV1.Point0536.outputs.2.hi, SourceMainFramesV1.Point0537.outputs.2.hi, SourceMainFramesV1.Point0538.outputs.2.hi, SourceMainFramesV1.Point0539.outputs.2.hi, SourceMainFramesV1.Point0540.outputs.2.hi, SourceMainFramesV1.Point0541.outputs.2.hi, SourceMainFramesV1.Point0542.outputs.2.hi, SourceMainFramesV1.Point0543.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=542) domain
     SourceMainFramesV1.Point0542.input_defined SourceMainFramesV1.Point0542.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0542.outputs.2.hi (by
         change SourceMainFramesV1.Point0542.outputs.2.hi ∈ [SourceMainFramesV1.Point0536.outputs.2.hi, SourceMainFramesV1.Point0537.outputs.2.hi, SourceMainFramesV1.Point0538.outputs.2.hi, SourceMainFramesV1.Point0539.outputs.2.hi, SourceMainFramesV1.Point0540.outputs.2.hi, SourceMainFramesV1.Point0541.outputs.2.hi, SourceMainFramesV1.Point0542.outputs.2.hi, SourceMainFramesV1.Point0543.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=543) domain
     SourceMainFramesV1.Point0543.input_defined SourceMainFramesV1.Point0543.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0543.outputs.2.hi (by
         change SourceMainFramesV1.Point0543.outputs.2.hi ∈ [SourceMainFramesV1.Point0536.outputs.2.hi, SourceMainFramesV1.Point0537.outputs.2.hi, SourceMainFramesV1.Point0538.outputs.2.hi, SourceMainFramesV1.Point0539.outputs.2.hi, SourceMainFramesV1.Point0540.outputs.2.hi, SourceMainFramesV1.Point0541.outputs.2.hi, SourceMainFramesV1.Point0542.outputs.2.hi, SourceMainFramesV1.Point0543.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block67
