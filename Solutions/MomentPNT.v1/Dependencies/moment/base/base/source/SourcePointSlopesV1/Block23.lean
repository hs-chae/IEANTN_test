/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0184
import SourceMainFramesV1.Point0185
import SourceMainFramesV1.Point0186
import SourceMainFramesV1.Point0187
import SourceMainFramesV1.Point0188
import SourceMainFramesV1.Point0189
import SourceMainFramesV1.Point0190
import SourceMainFramesV1.Point0191
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block23
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0184.outputs.2.hi,
 SourceMainFramesV1.Point0185.outputs.2.hi,
 SourceMainFramesV1.Point0186.outputs.2.hi,
 SourceMainFramesV1.Point0187.outputs.2.hi,
 SourceMainFramesV1.Point0188.outputs.2.hi,
 SourceMainFramesV1.Point0189.outputs.2.hi,
 SourceMainFramesV1.Point0190.outputs.2.hi,
 SourceMainFramesV1.Point0191.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 184 ≤ i) (high : i < 192)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=184) domain
     SourceMainFramesV1.Point0184.input_defined SourceMainFramesV1.Point0184.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0184.outputs.2.hi (by
         change SourceMainFramesV1.Point0184.outputs.2.hi ∈ [SourceMainFramesV1.Point0184.outputs.2.hi, SourceMainFramesV1.Point0185.outputs.2.hi, SourceMainFramesV1.Point0186.outputs.2.hi, SourceMainFramesV1.Point0187.outputs.2.hi, SourceMainFramesV1.Point0188.outputs.2.hi, SourceMainFramesV1.Point0189.outputs.2.hi, SourceMainFramesV1.Point0190.outputs.2.hi, SourceMainFramesV1.Point0191.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=185) domain
     SourceMainFramesV1.Point0185.input_defined SourceMainFramesV1.Point0185.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0185.outputs.2.hi (by
         change SourceMainFramesV1.Point0185.outputs.2.hi ∈ [SourceMainFramesV1.Point0184.outputs.2.hi, SourceMainFramesV1.Point0185.outputs.2.hi, SourceMainFramesV1.Point0186.outputs.2.hi, SourceMainFramesV1.Point0187.outputs.2.hi, SourceMainFramesV1.Point0188.outputs.2.hi, SourceMainFramesV1.Point0189.outputs.2.hi, SourceMainFramesV1.Point0190.outputs.2.hi, SourceMainFramesV1.Point0191.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=186) domain
     SourceMainFramesV1.Point0186.input_defined SourceMainFramesV1.Point0186.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0186.outputs.2.hi (by
         change SourceMainFramesV1.Point0186.outputs.2.hi ∈ [SourceMainFramesV1.Point0184.outputs.2.hi, SourceMainFramesV1.Point0185.outputs.2.hi, SourceMainFramesV1.Point0186.outputs.2.hi, SourceMainFramesV1.Point0187.outputs.2.hi, SourceMainFramesV1.Point0188.outputs.2.hi, SourceMainFramesV1.Point0189.outputs.2.hi, SourceMainFramesV1.Point0190.outputs.2.hi, SourceMainFramesV1.Point0191.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=187) domain
     SourceMainFramesV1.Point0187.input_defined SourceMainFramesV1.Point0187.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0187.outputs.2.hi (by
         change SourceMainFramesV1.Point0187.outputs.2.hi ∈ [SourceMainFramesV1.Point0184.outputs.2.hi, SourceMainFramesV1.Point0185.outputs.2.hi, SourceMainFramesV1.Point0186.outputs.2.hi, SourceMainFramesV1.Point0187.outputs.2.hi, SourceMainFramesV1.Point0188.outputs.2.hi, SourceMainFramesV1.Point0189.outputs.2.hi, SourceMainFramesV1.Point0190.outputs.2.hi, SourceMainFramesV1.Point0191.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=188) domain
     SourceMainFramesV1.Point0188.input_defined SourceMainFramesV1.Point0188.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0188.outputs.2.hi (by
         change SourceMainFramesV1.Point0188.outputs.2.hi ∈ [SourceMainFramesV1.Point0184.outputs.2.hi, SourceMainFramesV1.Point0185.outputs.2.hi, SourceMainFramesV1.Point0186.outputs.2.hi, SourceMainFramesV1.Point0187.outputs.2.hi, SourceMainFramesV1.Point0188.outputs.2.hi, SourceMainFramesV1.Point0189.outputs.2.hi, SourceMainFramesV1.Point0190.outputs.2.hi, SourceMainFramesV1.Point0191.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=189) domain
     SourceMainFramesV1.Point0189.input_defined SourceMainFramesV1.Point0189.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0189.outputs.2.hi (by
         change SourceMainFramesV1.Point0189.outputs.2.hi ∈ [SourceMainFramesV1.Point0184.outputs.2.hi, SourceMainFramesV1.Point0185.outputs.2.hi, SourceMainFramesV1.Point0186.outputs.2.hi, SourceMainFramesV1.Point0187.outputs.2.hi, SourceMainFramesV1.Point0188.outputs.2.hi, SourceMainFramesV1.Point0189.outputs.2.hi, SourceMainFramesV1.Point0190.outputs.2.hi, SourceMainFramesV1.Point0191.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=190) domain
     SourceMainFramesV1.Point0190.input_defined SourceMainFramesV1.Point0190.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0190.outputs.2.hi (by
         change SourceMainFramesV1.Point0190.outputs.2.hi ∈ [SourceMainFramesV1.Point0184.outputs.2.hi, SourceMainFramesV1.Point0185.outputs.2.hi, SourceMainFramesV1.Point0186.outputs.2.hi, SourceMainFramesV1.Point0187.outputs.2.hi, SourceMainFramesV1.Point0188.outputs.2.hi, SourceMainFramesV1.Point0189.outputs.2.hi, SourceMainFramesV1.Point0190.outputs.2.hi, SourceMainFramesV1.Point0191.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=191) domain
     SourceMainFramesV1.Point0191.input_defined SourceMainFramesV1.Point0191.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0191.outputs.2.hi (by
         change SourceMainFramesV1.Point0191.outputs.2.hi ∈ [SourceMainFramesV1.Point0184.outputs.2.hi, SourceMainFramesV1.Point0185.outputs.2.hi, SourceMainFramesV1.Point0186.outputs.2.hi, SourceMainFramesV1.Point0187.outputs.2.hi, SourceMainFramesV1.Point0188.outputs.2.hi, SourceMainFramesV1.Point0189.outputs.2.hi, SourceMainFramesV1.Point0190.outputs.2.hi, SourceMainFramesV1.Point0191.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block23
