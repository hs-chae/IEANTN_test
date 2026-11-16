/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0232
import SourceMainFramesV1.Point0233
import SourceMainFramesV1.Point0234
import SourceMainFramesV1.Point0235
import SourceMainFramesV1.Point0236
import SourceMainFramesV1.Point0237
import SourceMainFramesV1.Point0238
import SourceMainFramesV1.Point0239
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block29
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0232.outputs.2.hi,
 SourceMainFramesV1.Point0233.outputs.2.hi,
 SourceMainFramesV1.Point0234.outputs.2.hi,
 SourceMainFramesV1.Point0235.outputs.2.hi,
 SourceMainFramesV1.Point0236.outputs.2.hi,
 SourceMainFramesV1.Point0237.outputs.2.hi,
 SourceMainFramesV1.Point0238.outputs.2.hi,
 SourceMainFramesV1.Point0239.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 232 ≤ i) (high : i < 240)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=232) domain
     SourceMainFramesV1.Point0232.input_defined SourceMainFramesV1.Point0232.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0232.outputs.2.hi (by
         change SourceMainFramesV1.Point0232.outputs.2.hi ∈ [SourceMainFramesV1.Point0232.outputs.2.hi, SourceMainFramesV1.Point0233.outputs.2.hi, SourceMainFramesV1.Point0234.outputs.2.hi, SourceMainFramesV1.Point0235.outputs.2.hi, SourceMainFramesV1.Point0236.outputs.2.hi, SourceMainFramesV1.Point0237.outputs.2.hi, SourceMainFramesV1.Point0238.outputs.2.hi, SourceMainFramesV1.Point0239.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=233) domain
     SourceMainFramesV1.Point0233.input_defined SourceMainFramesV1.Point0233.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0233.outputs.2.hi (by
         change SourceMainFramesV1.Point0233.outputs.2.hi ∈ [SourceMainFramesV1.Point0232.outputs.2.hi, SourceMainFramesV1.Point0233.outputs.2.hi, SourceMainFramesV1.Point0234.outputs.2.hi, SourceMainFramesV1.Point0235.outputs.2.hi, SourceMainFramesV1.Point0236.outputs.2.hi, SourceMainFramesV1.Point0237.outputs.2.hi, SourceMainFramesV1.Point0238.outputs.2.hi, SourceMainFramesV1.Point0239.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=234) domain
     SourceMainFramesV1.Point0234.input_defined SourceMainFramesV1.Point0234.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0234.outputs.2.hi (by
         change SourceMainFramesV1.Point0234.outputs.2.hi ∈ [SourceMainFramesV1.Point0232.outputs.2.hi, SourceMainFramesV1.Point0233.outputs.2.hi, SourceMainFramesV1.Point0234.outputs.2.hi, SourceMainFramesV1.Point0235.outputs.2.hi, SourceMainFramesV1.Point0236.outputs.2.hi, SourceMainFramesV1.Point0237.outputs.2.hi, SourceMainFramesV1.Point0238.outputs.2.hi, SourceMainFramesV1.Point0239.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=235) domain
     SourceMainFramesV1.Point0235.input_defined SourceMainFramesV1.Point0235.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0235.outputs.2.hi (by
         change SourceMainFramesV1.Point0235.outputs.2.hi ∈ [SourceMainFramesV1.Point0232.outputs.2.hi, SourceMainFramesV1.Point0233.outputs.2.hi, SourceMainFramesV1.Point0234.outputs.2.hi, SourceMainFramesV1.Point0235.outputs.2.hi, SourceMainFramesV1.Point0236.outputs.2.hi, SourceMainFramesV1.Point0237.outputs.2.hi, SourceMainFramesV1.Point0238.outputs.2.hi, SourceMainFramesV1.Point0239.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=236) domain
     SourceMainFramesV1.Point0236.input_defined SourceMainFramesV1.Point0236.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0236.outputs.2.hi (by
         change SourceMainFramesV1.Point0236.outputs.2.hi ∈ [SourceMainFramesV1.Point0232.outputs.2.hi, SourceMainFramesV1.Point0233.outputs.2.hi, SourceMainFramesV1.Point0234.outputs.2.hi, SourceMainFramesV1.Point0235.outputs.2.hi, SourceMainFramesV1.Point0236.outputs.2.hi, SourceMainFramesV1.Point0237.outputs.2.hi, SourceMainFramesV1.Point0238.outputs.2.hi, SourceMainFramesV1.Point0239.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=237) domain
     SourceMainFramesV1.Point0237.input_defined SourceMainFramesV1.Point0237.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0237.outputs.2.hi (by
         change SourceMainFramesV1.Point0237.outputs.2.hi ∈ [SourceMainFramesV1.Point0232.outputs.2.hi, SourceMainFramesV1.Point0233.outputs.2.hi, SourceMainFramesV1.Point0234.outputs.2.hi, SourceMainFramesV1.Point0235.outputs.2.hi, SourceMainFramesV1.Point0236.outputs.2.hi, SourceMainFramesV1.Point0237.outputs.2.hi, SourceMainFramesV1.Point0238.outputs.2.hi, SourceMainFramesV1.Point0239.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=238) domain
     SourceMainFramesV1.Point0238.input_defined SourceMainFramesV1.Point0238.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0238.outputs.2.hi (by
         change SourceMainFramesV1.Point0238.outputs.2.hi ∈ [SourceMainFramesV1.Point0232.outputs.2.hi, SourceMainFramesV1.Point0233.outputs.2.hi, SourceMainFramesV1.Point0234.outputs.2.hi, SourceMainFramesV1.Point0235.outputs.2.hi, SourceMainFramesV1.Point0236.outputs.2.hi, SourceMainFramesV1.Point0237.outputs.2.hi, SourceMainFramesV1.Point0238.outputs.2.hi, SourceMainFramesV1.Point0239.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=239) domain
     SourceMainFramesV1.Point0239.input_defined SourceMainFramesV1.Point0239.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0239.outputs.2.hi (by
         change SourceMainFramesV1.Point0239.outputs.2.hi ∈ [SourceMainFramesV1.Point0232.outputs.2.hi, SourceMainFramesV1.Point0233.outputs.2.hi, SourceMainFramesV1.Point0234.outputs.2.hi, SourceMainFramesV1.Point0235.outputs.2.hi, SourceMainFramesV1.Point0236.outputs.2.hi, SourceMainFramesV1.Point0237.outputs.2.hi, SourceMainFramesV1.Point0238.outputs.2.hi, SourceMainFramesV1.Point0239.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block29
