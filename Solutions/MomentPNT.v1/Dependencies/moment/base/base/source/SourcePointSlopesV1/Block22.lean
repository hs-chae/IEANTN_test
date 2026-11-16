/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0176
import SourceMainFramesV1.Point0177
import SourceMainFramesV1.Point0178
import SourceMainFramesV1.Point0179
import SourceMainFramesV1.Point0180
import SourceMainFramesV1.Point0181
import SourceMainFramesV1.Point0182
import SourceMainFramesV1.Point0183
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block22
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0176.outputs.2.hi,
 SourceMainFramesV1.Point0177.outputs.2.hi,
 SourceMainFramesV1.Point0178.outputs.2.hi,
 SourceMainFramesV1.Point0179.outputs.2.hi,
 SourceMainFramesV1.Point0180.outputs.2.hi,
 SourceMainFramesV1.Point0181.outputs.2.hi,
 SourceMainFramesV1.Point0182.outputs.2.hi,
 SourceMainFramesV1.Point0183.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 176 ≤ i) (high : i < 184)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=176) domain
     SourceMainFramesV1.Point0176.input_defined SourceMainFramesV1.Point0176.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0176.outputs.2.hi (by
         change SourceMainFramesV1.Point0176.outputs.2.hi ∈ [SourceMainFramesV1.Point0176.outputs.2.hi, SourceMainFramesV1.Point0177.outputs.2.hi, SourceMainFramesV1.Point0178.outputs.2.hi, SourceMainFramesV1.Point0179.outputs.2.hi, SourceMainFramesV1.Point0180.outputs.2.hi, SourceMainFramesV1.Point0181.outputs.2.hi, SourceMainFramesV1.Point0182.outputs.2.hi, SourceMainFramesV1.Point0183.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=177) domain
     SourceMainFramesV1.Point0177.input_defined SourceMainFramesV1.Point0177.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0177.outputs.2.hi (by
         change SourceMainFramesV1.Point0177.outputs.2.hi ∈ [SourceMainFramesV1.Point0176.outputs.2.hi, SourceMainFramesV1.Point0177.outputs.2.hi, SourceMainFramesV1.Point0178.outputs.2.hi, SourceMainFramesV1.Point0179.outputs.2.hi, SourceMainFramesV1.Point0180.outputs.2.hi, SourceMainFramesV1.Point0181.outputs.2.hi, SourceMainFramesV1.Point0182.outputs.2.hi, SourceMainFramesV1.Point0183.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=178) domain
     SourceMainFramesV1.Point0178.input_defined SourceMainFramesV1.Point0178.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0178.outputs.2.hi (by
         change SourceMainFramesV1.Point0178.outputs.2.hi ∈ [SourceMainFramesV1.Point0176.outputs.2.hi, SourceMainFramesV1.Point0177.outputs.2.hi, SourceMainFramesV1.Point0178.outputs.2.hi, SourceMainFramesV1.Point0179.outputs.2.hi, SourceMainFramesV1.Point0180.outputs.2.hi, SourceMainFramesV1.Point0181.outputs.2.hi, SourceMainFramesV1.Point0182.outputs.2.hi, SourceMainFramesV1.Point0183.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=179) domain
     SourceMainFramesV1.Point0179.input_defined SourceMainFramesV1.Point0179.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0179.outputs.2.hi (by
         change SourceMainFramesV1.Point0179.outputs.2.hi ∈ [SourceMainFramesV1.Point0176.outputs.2.hi, SourceMainFramesV1.Point0177.outputs.2.hi, SourceMainFramesV1.Point0178.outputs.2.hi, SourceMainFramesV1.Point0179.outputs.2.hi, SourceMainFramesV1.Point0180.outputs.2.hi, SourceMainFramesV1.Point0181.outputs.2.hi, SourceMainFramesV1.Point0182.outputs.2.hi, SourceMainFramesV1.Point0183.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=180) domain
     SourceMainFramesV1.Point0180.input_defined SourceMainFramesV1.Point0180.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0180.outputs.2.hi (by
         change SourceMainFramesV1.Point0180.outputs.2.hi ∈ [SourceMainFramesV1.Point0176.outputs.2.hi, SourceMainFramesV1.Point0177.outputs.2.hi, SourceMainFramesV1.Point0178.outputs.2.hi, SourceMainFramesV1.Point0179.outputs.2.hi, SourceMainFramesV1.Point0180.outputs.2.hi, SourceMainFramesV1.Point0181.outputs.2.hi, SourceMainFramesV1.Point0182.outputs.2.hi, SourceMainFramesV1.Point0183.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=181) domain
     SourceMainFramesV1.Point0181.input_defined SourceMainFramesV1.Point0181.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0181.outputs.2.hi (by
         change SourceMainFramesV1.Point0181.outputs.2.hi ∈ [SourceMainFramesV1.Point0176.outputs.2.hi, SourceMainFramesV1.Point0177.outputs.2.hi, SourceMainFramesV1.Point0178.outputs.2.hi, SourceMainFramesV1.Point0179.outputs.2.hi, SourceMainFramesV1.Point0180.outputs.2.hi, SourceMainFramesV1.Point0181.outputs.2.hi, SourceMainFramesV1.Point0182.outputs.2.hi, SourceMainFramesV1.Point0183.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=182) domain
     SourceMainFramesV1.Point0182.input_defined SourceMainFramesV1.Point0182.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0182.outputs.2.hi (by
         change SourceMainFramesV1.Point0182.outputs.2.hi ∈ [SourceMainFramesV1.Point0176.outputs.2.hi, SourceMainFramesV1.Point0177.outputs.2.hi, SourceMainFramesV1.Point0178.outputs.2.hi, SourceMainFramesV1.Point0179.outputs.2.hi, SourceMainFramesV1.Point0180.outputs.2.hi, SourceMainFramesV1.Point0181.outputs.2.hi, SourceMainFramesV1.Point0182.outputs.2.hi, SourceMainFramesV1.Point0183.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=183) domain
     SourceMainFramesV1.Point0183.input_defined SourceMainFramesV1.Point0183.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0183.outputs.2.hi (by
         change SourceMainFramesV1.Point0183.outputs.2.hi ∈ [SourceMainFramesV1.Point0176.outputs.2.hi, SourceMainFramesV1.Point0177.outputs.2.hi, SourceMainFramesV1.Point0178.outputs.2.hi, SourceMainFramesV1.Point0179.outputs.2.hi, SourceMainFramesV1.Point0180.outputs.2.hi, SourceMainFramesV1.Point0181.outputs.2.hi, SourceMainFramesV1.Point0182.outputs.2.hi, SourceMainFramesV1.Point0183.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block22
