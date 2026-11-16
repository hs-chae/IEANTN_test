/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0272
import SourceMainFramesV1.Point0273
import SourceMainFramesV1.Point0274
import SourceMainFramesV1.Point0275
import SourceMainFramesV1.Point0276
import SourceMainFramesV1.Point0277
import SourceMainFramesV1.Point0278
import SourceMainFramesV1.Point0279
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block34
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0272.outputs.2.hi,
 SourceMainFramesV1.Point0273.outputs.2.hi,
 SourceMainFramesV1.Point0274.outputs.2.hi,
 SourceMainFramesV1.Point0275.outputs.2.hi,
 SourceMainFramesV1.Point0276.outputs.2.hi,
 SourceMainFramesV1.Point0277.outputs.2.hi,
 SourceMainFramesV1.Point0278.outputs.2.hi,
 SourceMainFramesV1.Point0279.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 272 ≤ i) (high : i < 280)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=272) domain
     SourceMainFramesV1.Point0272.input_defined SourceMainFramesV1.Point0272.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0272.outputs.2.hi (by
         change SourceMainFramesV1.Point0272.outputs.2.hi ∈ [SourceMainFramesV1.Point0272.outputs.2.hi, SourceMainFramesV1.Point0273.outputs.2.hi, SourceMainFramesV1.Point0274.outputs.2.hi, SourceMainFramesV1.Point0275.outputs.2.hi, SourceMainFramesV1.Point0276.outputs.2.hi, SourceMainFramesV1.Point0277.outputs.2.hi, SourceMainFramesV1.Point0278.outputs.2.hi, SourceMainFramesV1.Point0279.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=273) domain
     SourceMainFramesV1.Point0273.input_defined SourceMainFramesV1.Point0273.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0273.outputs.2.hi (by
         change SourceMainFramesV1.Point0273.outputs.2.hi ∈ [SourceMainFramesV1.Point0272.outputs.2.hi, SourceMainFramesV1.Point0273.outputs.2.hi, SourceMainFramesV1.Point0274.outputs.2.hi, SourceMainFramesV1.Point0275.outputs.2.hi, SourceMainFramesV1.Point0276.outputs.2.hi, SourceMainFramesV1.Point0277.outputs.2.hi, SourceMainFramesV1.Point0278.outputs.2.hi, SourceMainFramesV1.Point0279.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=274) domain
     SourceMainFramesV1.Point0274.input_defined SourceMainFramesV1.Point0274.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0274.outputs.2.hi (by
         change SourceMainFramesV1.Point0274.outputs.2.hi ∈ [SourceMainFramesV1.Point0272.outputs.2.hi, SourceMainFramesV1.Point0273.outputs.2.hi, SourceMainFramesV1.Point0274.outputs.2.hi, SourceMainFramesV1.Point0275.outputs.2.hi, SourceMainFramesV1.Point0276.outputs.2.hi, SourceMainFramesV1.Point0277.outputs.2.hi, SourceMainFramesV1.Point0278.outputs.2.hi, SourceMainFramesV1.Point0279.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=275) domain
     SourceMainFramesV1.Point0275.input_defined SourceMainFramesV1.Point0275.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0275.outputs.2.hi (by
         change SourceMainFramesV1.Point0275.outputs.2.hi ∈ [SourceMainFramesV1.Point0272.outputs.2.hi, SourceMainFramesV1.Point0273.outputs.2.hi, SourceMainFramesV1.Point0274.outputs.2.hi, SourceMainFramesV1.Point0275.outputs.2.hi, SourceMainFramesV1.Point0276.outputs.2.hi, SourceMainFramesV1.Point0277.outputs.2.hi, SourceMainFramesV1.Point0278.outputs.2.hi, SourceMainFramesV1.Point0279.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=276) domain
     SourceMainFramesV1.Point0276.input_defined SourceMainFramesV1.Point0276.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0276.outputs.2.hi (by
         change SourceMainFramesV1.Point0276.outputs.2.hi ∈ [SourceMainFramesV1.Point0272.outputs.2.hi, SourceMainFramesV1.Point0273.outputs.2.hi, SourceMainFramesV1.Point0274.outputs.2.hi, SourceMainFramesV1.Point0275.outputs.2.hi, SourceMainFramesV1.Point0276.outputs.2.hi, SourceMainFramesV1.Point0277.outputs.2.hi, SourceMainFramesV1.Point0278.outputs.2.hi, SourceMainFramesV1.Point0279.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=277) domain
     SourceMainFramesV1.Point0277.input_defined SourceMainFramesV1.Point0277.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0277.outputs.2.hi (by
         change SourceMainFramesV1.Point0277.outputs.2.hi ∈ [SourceMainFramesV1.Point0272.outputs.2.hi, SourceMainFramesV1.Point0273.outputs.2.hi, SourceMainFramesV1.Point0274.outputs.2.hi, SourceMainFramesV1.Point0275.outputs.2.hi, SourceMainFramesV1.Point0276.outputs.2.hi, SourceMainFramesV1.Point0277.outputs.2.hi, SourceMainFramesV1.Point0278.outputs.2.hi, SourceMainFramesV1.Point0279.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=278) domain
     SourceMainFramesV1.Point0278.input_defined SourceMainFramesV1.Point0278.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0278.outputs.2.hi (by
         change SourceMainFramesV1.Point0278.outputs.2.hi ∈ [SourceMainFramesV1.Point0272.outputs.2.hi, SourceMainFramesV1.Point0273.outputs.2.hi, SourceMainFramesV1.Point0274.outputs.2.hi, SourceMainFramesV1.Point0275.outputs.2.hi, SourceMainFramesV1.Point0276.outputs.2.hi, SourceMainFramesV1.Point0277.outputs.2.hi, SourceMainFramesV1.Point0278.outputs.2.hi, SourceMainFramesV1.Point0279.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=279) domain
     SourceMainFramesV1.Point0279.input_defined SourceMainFramesV1.Point0279.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0279.outputs.2.hi (by
         change SourceMainFramesV1.Point0279.outputs.2.hi ∈ [SourceMainFramesV1.Point0272.outputs.2.hi, SourceMainFramesV1.Point0273.outputs.2.hi, SourceMainFramesV1.Point0274.outputs.2.hi, SourceMainFramesV1.Point0275.outputs.2.hi, SourceMainFramesV1.Point0276.outputs.2.hi, SourceMainFramesV1.Point0277.outputs.2.hi, SourceMainFramesV1.Point0278.outputs.2.hi, SourceMainFramesV1.Point0279.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block34
