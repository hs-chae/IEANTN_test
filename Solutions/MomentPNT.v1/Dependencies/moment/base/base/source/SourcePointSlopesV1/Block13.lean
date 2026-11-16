/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0104
import SourceMainFramesV1.Point0105
import SourceMainFramesV1.Point0106
import SourceMainFramesV1.Point0107
import SourceMainFramesV1.Point0108
import SourceMainFramesV1.Point0109
import SourceMainFramesV1.Point0110
import SourceMainFramesV1.Point0111
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block13
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0104.outputs.2.hi,
 SourceMainFramesV1.Point0105.outputs.2.hi,
 SourceMainFramesV1.Point0106.outputs.2.hi,
 SourceMainFramesV1.Point0107.outputs.2.hi,
 SourceMainFramesV1.Point0108.outputs.2.hi,
 SourceMainFramesV1.Point0109.outputs.2.hi,
 SourceMainFramesV1.Point0110.outputs.2.hi,
 SourceMainFramesV1.Point0111.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 104 ≤ i) (high : i < 112)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=104) domain
     SourceMainFramesV1.Point0104.input_defined SourceMainFramesV1.Point0104.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0104.outputs.2.hi (by
         change SourceMainFramesV1.Point0104.outputs.2.hi ∈ [SourceMainFramesV1.Point0104.outputs.2.hi, SourceMainFramesV1.Point0105.outputs.2.hi, SourceMainFramesV1.Point0106.outputs.2.hi, SourceMainFramesV1.Point0107.outputs.2.hi, SourceMainFramesV1.Point0108.outputs.2.hi, SourceMainFramesV1.Point0109.outputs.2.hi, SourceMainFramesV1.Point0110.outputs.2.hi, SourceMainFramesV1.Point0111.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=105) domain
     SourceMainFramesV1.Point0105.input_defined SourceMainFramesV1.Point0105.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0105.outputs.2.hi (by
         change SourceMainFramesV1.Point0105.outputs.2.hi ∈ [SourceMainFramesV1.Point0104.outputs.2.hi, SourceMainFramesV1.Point0105.outputs.2.hi, SourceMainFramesV1.Point0106.outputs.2.hi, SourceMainFramesV1.Point0107.outputs.2.hi, SourceMainFramesV1.Point0108.outputs.2.hi, SourceMainFramesV1.Point0109.outputs.2.hi, SourceMainFramesV1.Point0110.outputs.2.hi, SourceMainFramesV1.Point0111.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=106) domain
     SourceMainFramesV1.Point0106.input_defined SourceMainFramesV1.Point0106.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0106.outputs.2.hi (by
         change SourceMainFramesV1.Point0106.outputs.2.hi ∈ [SourceMainFramesV1.Point0104.outputs.2.hi, SourceMainFramesV1.Point0105.outputs.2.hi, SourceMainFramesV1.Point0106.outputs.2.hi, SourceMainFramesV1.Point0107.outputs.2.hi, SourceMainFramesV1.Point0108.outputs.2.hi, SourceMainFramesV1.Point0109.outputs.2.hi, SourceMainFramesV1.Point0110.outputs.2.hi, SourceMainFramesV1.Point0111.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=107) domain
     SourceMainFramesV1.Point0107.input_defined SourceMainFramesV1.Point0107.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0107.outputs.2.hi (by
         change SourceMainFramesV1.Point0107.outputs.2.hi ∈ [SourceMainFramesV1.Point0104.outputs.2.hi, SourceMainFramesV1.Point0105.outputs.2.hi, SourceMainFramesV1.Point0106.outputs.2.hi, SourceMainFramesV1.Point0107.outputs.2.hi, SourceMainFramesV1.Point0108.outputs.2.hi, SourceMainFramesV1.Point0109.outputs.2.hi, SourceMainFramesV1.Point0110.outputs.2.hi, SourceMainFramesV1.Point0111.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=108) domain
     SourceMainFramesV1.Point0108.input_defined SourceMainFramesV1.Point0108.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0108.outputs.2.hi (by
         change SourceMainFramesV1.Point0108.outputs.2.hi ∈ [SourceMainFramesV1.Point0104.outputs.2.hi, SourceMainFramesV1.Point0105.outputs.2.hi, SourceMainFramesV1.Point0106.outputs.2.hi, SourceMainFramesV1.Point0107.outputs.2.hi, SourceMainFramesV1.Point0108.outputs.2.hi, SourceMainFramesV1.Point0109.outputs.2.hi, SourceMainFramesV1.Point0110.outputs.2.hi, SourceMainFramesV1.Point0111.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=109) domain
     SourceMainFramesV1.Point0109.input_defined SourceMainFramesV1.Point0109.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0109.outputs.2.hi (by
         change SourceMainFramesV1.Point0109.outputs.2.hi ∈ [SourceMainFramesV1.Point0104.outputs.2.hi, SourceMainFramesV1.Point0105.outputs.2.hi, SourceMainFramesV1.Point0106.outputs.2.hi, SourceMainFramesV1.Point0107.outputs.2.hi, SourceMainFramesV1.Point0108.outputs.2.hi, SourceMainFramesV1.Point0109.outputs.2.hi, SourceMainFramesV1.Point0110.outputs.2.hi, SourceMainFramesV1.Point0111.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=110) domain
     SourceMainFramesV1.Point0110.input_defined SourceMainFramesV1.Point0110.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0110.outputs.2.hi (by
         change SourceMainFramesV1.Point0110.outputs.2.hi ∈ [SourceMainFramesV1.Point0104.outputs.2.hi, SourceMainFramesV1.Point0105.outputs.2.hi, SourceMainFramesV1.Point0106.outputs.2.hi, SourceMainFramesV1.Point0107.outputs.2.hi, SourceMainFramesV1.Point0108.outputs.2.hi, SourceMainFramesV1.Point0109.outputs.2.hi, SourceMainFramesV1.Point0110.outputs.2.hi, SourceMainFramesV1.Point0111.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=111) domain
     SourceMainFramesV1.Point0111.input_defined SourceMainFramesV1.Point0111.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0111.outputs.2.hi (by
         change SourceMainFramesV1.Point0111.outputs.2.hi ∈ [SourceMainFramesV1.Point0104.outputs.2.hi, SourceMainFramesV1.Point0105.outputs.2.hi, SourceMainFramesV1.Point0106.outputs.2.hi, SourceMainFramesV1.Point0107.outputs.2.hi, SourceMainFramesV1.Point0108.outputs.2.hi, SourceMainFramesV1.Point0109.outputs.2.hi, SourceMainFramesV1.Point0110.outputs.2.hi, SourceMainFramesV1.Point0111.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block13
