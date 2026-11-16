/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0512
import SourceMainFramesV1.Point0513
import SourceMainFramesV1.Point0514
import SourceMainFramesV1.Point0515
import SourceMainFramesV1.Point0516
import SourceMainFramesV1.Point0517
import SourceMainFramesV1.Point0518
import SourceMainFramesV1.Point0519
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block64
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0512.outputs.2.hi,
 SourceMainFramesV1.Point0513.outputs.2.hi,
 SourceMainFramesV1.Point0514.outputs.2.hi,
 SourceMainFramesV1.Point0515.outputs.2.hi,
 SourceMainFramesV1.Point0516.outputs.2.hi,
 SourceMainFramesV1.Point0517.outputs.2.hi,
 SourceMainFramesV1.Point0518.outputs.2.hi,
 SourceMainFramesV1.Point0519.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 512 ≤ i) (high : i < 520)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=512) domain
     SourceMainFramesV1.Point0512.input_defined SourceMainFramesV1.Point0512.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0512.outputs.2.hi (by
         change SourceMainFramesV1.Point0512.outputs.2.hi ∈ [SourceMainFramesV1.Point0512.outputs.2.hi, SourceMainFramesV1.Point0513.outputs.2.hi, SourceMainFramesV1.Point0514.outputs.2.hi, SourceMainFramesV1.Point0515.outputs.2.hi, SourceMainFramesV1.Point0516.outputs.2.hi, SourceMainFramesV1.Point0517.outputs.2.hi, SourceMainFramesV1.Point0518.outputs.2.hi, SourceMainFramesV1.Point0519.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=513) domain
     SourceMainFramesV1.Point0513.input_defined SourceMainFramesV1.Point0513.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0513.outputs.2.hi (by
         change SourceMainFramesV1.Point0513.outputs.2.hi ∈ [SourceMainFramesV1.Point0512.outputs.2.hi, SourceMainFramesV1.Point0513.outputs.2.hi, SourceMainFramesV1.Point0514.outputs.2.hi, SourceMainFramesV1.Point0515.outputs.2.hi, SourceMainFramesV1.Point0516.outputs.2.hi, SourceMainFramesV1.Point0517.outputs.2.hi, SourceMainFramesV1.Point0518.outputs.2.hi, SourceMainFramesV1.Point0519.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=514) domain
     SourceMainFramesV1.Point0514.input_defined SourceMainFramesV1.Point0514.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0514.outputs.2.hi (by
         change SourceMainFramesV1.Point0514.outputs.2.hi ∈ [SourceMainFramesV1.Point0512.outputs.2.hi, SourceMainFramesV1.Point0513.outputs.2.hi, SourceMainFramesV1.Point0514.outputs.2.hi, SourceMainFramesV1.Point0515.outputs.2.hi, SourceMainFramesV1.Point0516.outputs.2.hi, SourceMainFramesV1.Point0517.outputs.2.hi, SourceMainFramesV1.Point0518.outputs.2.hi, SourceMainFramesV1.Point0519.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=515) domain
     SourceMainFramesV1.Point0515.input_defined SourceMainFramesV1.Point0515.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0515.outputs.2.hi (by
         change SourceMainFramesV1.Point0515.outputs.2.hi ∈ [SourceMainFramesV1.Point0512.outputs.2.hi, SourceMainFramesV1.Point0513.outputs.2.hi, SourceMainFramesV1.Point0514.outputs.2.hi, SourceMainFramesV1.Point0515.outputs.2.hi, SourceMainFramesV1.Point0516.outputs.2.hi, SourceMainFramesV1.Point0517.outputs.2.hi, SourceMainFramesV1.Point0518.outputs.2.hi, SourceMainFramesV1.Point0519.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=516) domain
     SourceMainFramesV1.Point0516.input_defined SourceMainFramesV1.Point0516.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0516.outputs.2.hi (by
         change SourceMainFramesV1.Point0516.outputs.2.hi ∈ [SourceMainFramesV1.Point0512.outputs.2.hi, SourceMainFramesV1.Point0513.outputs.2.hi, SourceMainFramesV1.Point0514.outputs.2.hi, SourceMainFramesV1.Point0515.outputs.2.hi, SourceMainFramesV1.Point0516.outputs.2.hi, SourceMainFramesV1.Point0517.outputs.2.hi, SourceMainFramesV1.Point0518.outputs.2.hi, SourceMainFramesV1.Point0519.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=517) domain
     SourceMainFramesV1.Point0517.input_defined SourceMainFramesV1.Point0517.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0517.outputs.2.hi (by
         change SourceMainFramesV1.Point0517.outputs.2.hi ∈ [SourceMainFramesV1.Point0512.outputs.2.hi, SourceMainFramesV1.Point0513.outputs.2.hi, SourceMainFramesV1.Point0514.outputs.2.hi, SourceMainFramesV1.Point0515.outputs.2.hi, SourceMainFramesV1.Point0516.outputs.2.hi, SourceMainFramesV1.Point0517.outputs.2.hi, SourceMainFramesV1.Point0518.outputs.2.hi, SourceMainFramesV1.Point0519.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=518) domain
     SourceMainFramesV1.Point0518.input_defined SourceMainFramesV1.Point0518.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0518.outputs.2.hi (by
         change SourceMainFramesV1.Point0518.outputs.2.hi ∈ [SourceMainFramesV1.Point0512.outputs.2.hi, SourceMainFramesV1.Point0513.outputs.2.hi, SourceMainFramesV1.Point0514.outputs.2.hi, SourceMainFramesV1.Point0515.outputs.2.hi, SourceMainFramesV1.Point0516.outputs.2.hi, SourceMainFramesV1.Point0517.outputs.2.hi, SourceMainFramesV1.Point0518.outputs.2.hi, SourceMainFramesV1.Point0519.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=519) domain
     SourceMainFramesV1.Point0519.input_defined SourceMainFramesV1.Point0519.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0519.outputs.2.hi (by
         change SourceMainFramesV1.Point0519.outputs.2.hi ∈ [SourceMainFramesV1.Point0512.outputs.2.hi, SourceMainFramesV1.Point0513.outputs.2.hi, SourceMainFramesV1.Point0514.outputs.2.hi, SourceMainFramesV1.Point0515.outputs.2.hi, SourceMainFramesV1.Point0516.outputs.2.hi, SourceMainFramesV1.Point0517.outputs.2.hi, SourceMainFramesV1.Point0518.outputs.2.hi, SourceMainFramesV1.Point0519.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block64
