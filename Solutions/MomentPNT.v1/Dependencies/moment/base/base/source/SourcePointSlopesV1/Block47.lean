/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0376
import SourceMainFramesV1.Point0377
import SourceMainFramesV1.Point0378
import SourceMainFramesV1.Point0379
import SourceMainFramesV1.Point0380
import SourceMainFramesV1.Point0381
import SourceMainFramesV1.Point0382
import SourceMainFramesV1.Point0383
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block47
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0376.outputs.2.hi,
 SourceMainFramesV1.Point0377.outputs.2.hi,
 SourceMainFramesV1.Point0378.outputs.2.hi,
 SourceMainFramesV1.Point0379.outputs.2.hi,
 SourceMainFramesV1.Point0380.outputs.2.hi,
 SourceMainFramesV1.Point0381.outputs.2.hi,
 SourceMainFramesV1.Point0382.outputs.2.hi,
 SourceMainFramesV1.Point0383.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 376 ≤ i) (high : i < 384)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=376) domain
     SourceMainFramesV1.Point0376.input_defined SourceMainFramesV1.Point0376.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0376.outputs.2.hi (by
         change SourceMainFramesV1.Point0376.outputs.2.hi ∈ [SourceMainFramesV1.Point0376.outputs.2.hi, SourceMainFramesV1.Point0377.outputs.2.hi, SourceMainFramesV1.Point0378.outputs.2.hi, SourceMainFramesV1.Point0379.outputs.2.hi, SourceMainFramesV1.Point0380.outputs.2.hi, SourceMainFramesV1.Point0381.outputs.2.hi, SourceMainFramesV1.Point0382.outputs.2.hi, SourceMainFramesV1.Point0383.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=377) domain
     SourceMainFramesV1.Point0377.input_defined SourceMainFramesV1.Point0377.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0377.outputs.2.hi (by
         change SourceMainFramesV1.Point0377.outputs.2.hi ∈ [SourceMainFramesV1.Point0376.outputs.2.hi, SourceMainFramesV1.Point0377.outputs.2.hi, SourceMainFramesV1.Point0378.outputs.2.hi, SourceMainFramesV1.Point0379.outputs.2.hi, SourceMainFramesV1.Point0380.outputs.2.hi, SourceMainFramesV1.Point0381.outputs.2.hi, SourceMainFramesV1.Point0382.outputs.2.hi, SourceMainFramesV1.Point0383.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=378) domain
     SourceMainFramesV1.Point0378.input_defined SourceMainFramesV1.Point0378.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0378.outputs.2.hi (by
         change SourceMainFramesV1.Point0378.outputs.2.hi ∈ [SourceMainFramesV1.Point0376.outputs.2.hi, SourceMainFramesV1.Point0377.outputs.2.hi, SourceMainFramesV1.Point0378.outputs.2.hi, SourceMainFramesV1.Point0379.outputs.2.hi, SourceMainFramesV1.Point0380.outputs.2.hi, SourceMainFramesV1.Point0381.outputs.2.hi, SourceMainFramesV1.Point0382.outputs.2.hi, SourceMainFramesV1.Point0383.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=379) domain
     SourceMainFramesV1.Point0379.input_defined SourceMainFramesV1.Point0379.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0379.outputs.2.hi (by
         change SourceMainFramesV1.Point0379.outputs.2.hi ∈ [SourceMainFramesV1.Point0376.outputs.2.hi, SourceMainFramesV1.Point0377.outputs.2.hi, SourceMainFramesV1.Point0378.outputs.2.hi, SourceMainFramesV1.Point0379.outputs.2.hi, SourceMainFramesV1.Point0380.outputs.2.hi, SourceMainFramesV1.Point0381.outputs.2.hi, SourceMainFramesV1.Point0382.outputs.2.hi, SourceMainFramesV1.Point0383.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=380) domain
     SourceMainFramesV1.Point0380.input_defined SourceMainFramesV1.Point0380.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0380.outputs.2.hi (by
         change SourceMainFramesV1.Point0380.outputs.2.hi ∈ [SourceMainFramesV1.Point0376.outputs.2.hi, SourceMainFramesV1.Point0377.outputs.2.hi, SourceMainFramesV1.Point0378.outputs.2.hi, SourceMainFramesV1.Point0379.outputs.2.hi, SourceMainFramesV1.Point0380.outputs.2.hi, SourceMainFramesV1.Point0381.outputs.2.hi, SourceMainFramesV1.Point0382.outputs.2.hi, SourceMainFramesV1.Point0383.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=381) domain
     SourceMainFramesV1.Point0381.input_defined SourceMainFramesV1.Point0381.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0381.outputs.2.hi (by
         change SourceMainFramesV1.Point0381.outputs.2.hi ∈ [SourceMainFramesV1.Point0376.outputs.2.hi, SourceMainFramesV1.Point0377.outputs.2.hi, SourceMainFramesV1.Point0378.outputs.2.hi, SourceMainFramesV1.Point0379.outputs.2.hi, SourceMainFramesV1.Point0380.outputs.2.hi, SourceMainFramesV1.Point0381.outputs.2.hi, SourceMainFramesV1.Point0382.outputs.2.hi, SourceMainFramesV1.Point0383.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=382) domain
     SourceMainFramesV1.Point0382.input_defined SourceMainFramesV1.Point0382.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0382.outputs.2.hi (by
         change SourceMainFramesV1.Point0382.outputs.2.hi ∈ [SourceMainFramesV1.Point0376.outputs.2.hi, SourceMainFramesV1.Point0377.outputs.2.hi, SourceMainFramesV1.Point0378.outputs.2.hi, SourceMainFramesV1.Point0379.outputs.2.hi, SourceMainFramesV1.Point0380.outputs.2.hi, SourceMainFramesV1.Point0381.outputs.2.hi, SourceMainFramesV1.Point0382.outputs.2.hi, SourceMainFramesV1.Point0383.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=383) domain
     SourceMainFramesV1.Point0383.input_defined SourceMainFramesV1.Point0383.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0383.outputs.2.hi (by
         change SourceMainFramesV1.Point0383.outputs.2.hi ∈ [SourceMainFramesV1.Point0376.outputs.2.hi, SourceMainFramesV1.Point0377.outputs.2.hi, SourceMainFramesV1.Point0378.outputs.2.hi, SourceMainFramesV1.Point0379.outputs.2.hi, SourceMainFramesV1.Point0380.outputs.2.hi, SourceMainFramesV1.Point0381.outputs.2.hi, SourceMainFramesV1.Point0382.outputs.2.hi, SourceMainFramesV1.Point0383.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block47
