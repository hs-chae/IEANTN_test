/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0248
import SourceMainFramesV1.Point0249
import SourceMainFramesV1.Point0250
import SourceMainFramesV1.Point0251
import SourceMainFramesV1.Point0252
import SourceMainFramesV1.Point0253
import SourceMainFramesV1.Point0254
import SourceMainFramesV1.Point0255
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block31
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0248.outputs.2.hi,
 SourceMainFramesV1.Point0249.outputs.2.hi,
 SourceMainFramesV1.Point0250.outputs.2.hi,
 SourceMainFramesV1.Point0251.outputs.2.hi,
 SourceMainFramesV1.Point0252.outputs.2.hi,
 SourceMainFramesV1.Point0253.outputs.2.hi,
 SourceMainFramesV1.Point0254.outputs.2.hi,
 SourceMainFramesV1.Point0255.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 248 ≤ i) (high : i < 256)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=248) domain
     SourceMainFramesV1.Point0248.input_defined SourceMainFramesV1.Point0248.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0248.outputs.2.hi (by
         change SourceMainFramesV1.Point0248.outputs.2.hi ∈ [SourceMainFramesV1.Point0248.outputs.2.hi, SourceMainFramesV1.Point0249.outputs.2.hi, SourceMainFramesV1.Point0250.outputs.2.hi, SourceMainFramesV1.Point0251.outputs.2.hi, SourceMainFramesV1.Point0252.outputs.2.hi, SourceMainFramesV1.Point0253.outputs.2.hi, SourceMainFramesV1.Point0254.outputs.2.hi, SourceMainFramesV1.Point0255.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=249) domain
     SourceMainFramesV1.Point0249.input_defined SourceMainFramesV1.Point0249.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0249.outputs.2.hi (by
         change SourceMainFramesV1.Point0249.outputs.2.hi ∈ [SourceMainFramesV1.Point0248.outputs.2.hi, SourceMainFramesV1.Point0249.outputs.2.hi, SourceMainFramesV1.Point0250.outputs.2.hi, SourceMainFramesV1.Point0251.outputs.2.hi, SourceMainFramesV1.Point0252.outputs.2.hi, SourceMainFramesV1.Point0253.outputs.2.hi, SourceMainFramesV1.Point0254.outputs.2.hi, SourceMainFramesV1.Point0255.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=250) domain
     SourceMainFramesV1.Point0250.input_defined SourceMainFramesV1.Point0250.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0250.outputs.2.hi (by
         change SourceMainFramesV1.Point0250.outputs.2.hi ∈ [SourceMainFramesV1.Point0248.outputs.2.hi, SourceMainFramesV1.Point0249.outputs.2.hi, SourceMainFramesV1.Point0250.outputs.2.hi, SourceMainFramesV1.Point0251.outputs.2.hi, SourceMainFramesV1.Point0252.outputs.2.hi, SourceMainFramesV1.Point0253.outputs.2.hi, SourceMainFramesV1.Point0254.outputs.2.hi, SourceMainFramesV1.Point0255.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=251) domain
     SourceMainFramesV1.Point0251.input_defined SourceMainFramesV1.Point0251.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0251.outputs.2.hi (by
         change SourceMainFramesV1.Point0251.outputs.2.hi ∈ [SourceMainFramesV1.Point0248.outputs.2.hi, SourceMainFramesV1.Point0249.outputs.2.hi, SourceMainFramesV1.Point0250.outputs.2.hi, SourceMainFramesV1.Point0251.outputs.2.hi, SourceMainFramesV1.Point0252.outputs.2.hi, SourceMainFramesV1.Point0253.outputs.2.hi, SourceMainFramesV1.Point0254.outputs.2.hi, SourceMainFramesV1.Point0255.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=252) domain
     SourceMainFramesV1.Point0252.input_defined SourceMainFramesV1.Point0252.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0252.outputs.2.hi (by
         change SourceMainFramesV1.Point0252.outputs.2.hi ∈ [SourceMainFramesV1.Point0248.outputs.2.hi, SourceMainFramesV1.Point0249.outputs.2.hi, SourceMainFramesV1.Point0250.outputs.2.hi, SourceMainFramesV1.Point0251.outputs.2.hi, SourceMainFramesV1.Point0252.outputs.2.hi, SourceMainFramesV1.Point0253.outputs.2.hi, SourceMainFramesV1.Point0254.outputs.2.hi, SourceMainFramesV1.Point0255.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=253) domain
     SourceMainFramesV1.Point0253.input_defined SourceMainFramesV1.Point0253.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0253.outputs.2.hi (by
         change SourceMainFramesV1.Point0253.outputs.2.hi ∈ [SourceMainFramesV1.Point0248.outputs.2.hi, SourceMainFramesV1.Point0249.outputs.2.hi, SourceMainFramesV1.Point0250.outputs.2.hi, SourceMainFramesV1.Point0251.outputs.2.hi, SourceMainFramesV1.Point0252.outputs.2.hi, SourceMainFramesV1.Point0253.outputs.2.hi, SourceMainFramesV1.Point0254.outputs.2.hi, SourceMainFramesV1.Point0255.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=254) domain
     SourceMainFramesV1.Point0254.input_defined SourceMainFramesV1.Point0254.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0254.outputs.2.hi (by
         change SourceMainFramesV1.Point0254.outputs.2.hi ∈ [SourceMainFramesV1.Point0248.outputs.2.hi, SourceMainFramesV1.Point0249.outputs.2.hi, SourceMainFramesV1.Point0250.outputs.2.hi, SourceMainFramesV1.Point0251.outputs.2.hi, SourceMainFramesV1.Point0252.outputs.2.hi, SourceMainFramesV1.Point0253.outputs.2.hi, SourceMainFramesV1.Point0254.outputs.2.hi, SourceMainFramesV1.Point0255.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=255) domain
     SourceMainFramesV1.Point0255.input_defined SourceMainFramesV1.Point0255.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0255.outputs.2.hi (by
         change SourceMainFramesV1.Point0255.outputs.2.hi ∈ [SourceMainFramesV1.Point0248.outputs.2.hi, SourceMainFramesV1.Point0249.outputs.2.hi, SourceMainFramesV1.Point0250.outputs.2.hi, SourceMainFramesV1.Point0251.outputs.2.hi, SourceMainFramesV1.Point0252.outputs.2.hi, SourceMainFramesV1.Point0253.outputs.2.hi, SourceMainFramesV1.Point0254.outputs.2.hi, SourceMainFramesV1.Point0255.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block31
