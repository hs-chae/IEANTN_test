/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0224
import SourceMainFramesV1.Point0225
import SourceMainFramesV1.Point0226
import SourceMainFramesV1.Point0227
import SourceMainFramesV1.Point0228
import SourceMainFramesV1.Point0229
import SourceMainFramesV1.Point0230
import SourceMainFramesV1.Point0231
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block28
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0224.outputs.2.hi,
 SourceMainFramesV1.Point0225.outputs.2.hi,
 SourceMainFramesV1.Point0226.outputs.2.hi,
 SourceMainFramesV1.Point0227.outputs.2.hi,
 SourceMainFramesV1.Point0228.outputs.2.hi,
 SourceMainFramesV1.Point0229.outputs.2.hi,
 SourceMainFramesV1.Point0230.outputs.2.hi,
 SourceMainFramesV1.Point0231.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 224 ≤ i) (high : i < 232)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=224) domain
     SourceMainFramesV1.Point0224.input_defined SourceMainFramesV1.Point0224.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0224.outputs.2.hi (by
         change SourceMainFramesV1.Point0224.outputs.2.hi ∈ [SourceMainFramesV1.Point0224.outputs.2.hi, SourceMainFramesV1.Point0225.outputs.2.hi, SourceMainFramesV1.Point0226.outputs.2.hi, SourceMainFramesV1.Point0227.outputs.2.hi, SourceMainFramesV1.Point0228.outputs.2.hi, SourceMainFramesV1.Point0229.outputs.2.hi, SourceMainFramesV1.Point0230.outputs.2.hi, SourceMainFramesV1.Point0231.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=225) domain
     SourceMainFramesV1.Point0225.input_defined SourceMainFramesV1.Point0225.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0225.outputs.2.hi (by
         change SourceMainFramesV1.Point0225.outputs.2.hi ∈ [SourceMainFramesV1.Point0224.outputs.2.hi, SourceMainFramesV1.Point0225.outputs.2.hi, SourceMainFramesV1.Point0226.outputs.2.hi, SourceMainFramesV1.Point0227.outputs.2.hi, SourceMainFramesV1.Point0228.outputs.2.hi, SourceMainFramesV1.Point0229.outputs.2.hi, SourceMainFramesV1.Point0230.outputs.2.hi, SourceMainFramesV1.Point0231.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=226) domain
     SourceMainFramesV1.Point0226.input_defined SourceMainFramesV1.Point0226.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0226.outputs.2.hi (by
         change SourceMainFramesV1.Point0226.outputs.2.hi ∈ [SourceMainFramesV1.Point0224.outputs.2.hi, SourceMainFramesV1.Point0225.outputs.2.hi, SourceMainFramesV1.Point0226.outputs.2.hi, SourceMainFramesV1.Point0227.outputs.2.hi, SourceMainFramesV1.Point0228.outputs.2.hi, SourceMainFramesV1.Point0229.outputs.2.hi, SourceMainFramesV1.Point0230.outputs.2.hi, SourceMainFramesV1.Point0231.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=227) domain
     SourceMainFramesV1.Point0227.input_defined SourceMainFramesV1.Point0227.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0227.outputs.2.hi (by
         change SourceMainFramesV1.Point0227.outputs.2.hi ∈ [SourceMainFramesV1.Point0224.outputs.2.hi, SourceMainFramesV1.Point0225.outputs.2.hi, SourceMainFramesV1.Point0226.outputs.2.hi, SourceMainFramesV1.Point0227.outputs.2.hi, SourceMainFramesV1.Point0228.outputs.2.hi, SourceMainFramesV1.Point0229.outputs.2.hi, SourceMainFramesV1.Point0230.outputs.2.hi, SourceMainFramesV1.Point0231.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=228) domain
     SourceMainFramesV1.Point0228.input_defined SourceMainFramesV1.Point0228.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0228.outputs.2.hi (by
         change SourceMainFramesV1.Point0228.outputs.2.hi ∈ [SourceMainFramesV1.Point0224.outputs.2.hi, SourceMainFramesV1.Point0225.outputs.2.hi, SourceMainFramesV1.Point0226.outputs.2.hi, SourceMainFramesV1.Point0227.outputs.2.hi, SourceMainFramesV1.Point0228.outputs.2.hi, SourceMainFramesV1.Point0229.outputs.2.hi, SourceMainFramesV1.Point0230.outputs.2.hi, SourceMainFramesV1.Point0231.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=229) domain
     SourceMainFramesV1.Point0229.input_defined SourceMainFramesV1.Point0229.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0229.outputs.2.hi (by
         change SourceMainFramesV1.Point0229.outputs.2.hi ∈ [SourceMainFramesV1.Point0224.outputs.2.hi, SourceMainFramesV1.Point0225.outputs.2.hi, SourceMainFramesV1.Point0226.outputs.2.hi, SourceMainFramesV1.Point0227.outputs.2.hi, SourceMainFramesV1.Point0228.outputs.2.hi, SourceMainFramesV1.Point0229.outputs.2.hi, SourceMainFramesV1.Point0230.outputs.2.hi, SourceMainFramesV1.Point0231.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=230) domain
     SourceMainFramesV1.Point0230.input_defined SourceMainFramesV1.Point0230.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0230.outputs.2.hi (by
         change SourceMainFramesV1.Point0230.outputs.2.hi ∈ [SourceMainFramesV1.Point0224.outputs.2.hi, SourceMainFramesV1.Point0225.outputs.2.hi, SourceMainFramesV1.Point0226.outputs.2.hi, SourceMainFramesV1.Point0227.outputs.2.hi, SourceMainFramesV1.Point0228.outputs.2.hi, SourceMainFramesV1.Point0229.outputs.2.hi, SourceMainFramesV1.Point0230.outputs.2.hi, SourceMainFramesV1.Point0231.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=231) domain
     SourceMainFramesV1.Point0231.input_defined SourceMainFramesV1.Point0231.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0231.outputs.2.hi (by
         change SourceMainFramesV1.Point0231.outputs.2.hi ∈ [SourceMainFramesV1.Point0224.outputs.2.hi, SourceMainFramesV1.Point0225.outputs.2.hi, SourceMainFramesV1.Point0226.outputs.2.hi, SourceMainFramesV1.Point0227.outputs.2.hi, SourceMainFramesV1.Point0228.outputs.2.hi, SourceMainFramesV1.Point0229.outputs.2.hi, SourceMainFramesV1.Point0230.outputs.2.hi, SourceMainFramesV1.Point0231.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block28
