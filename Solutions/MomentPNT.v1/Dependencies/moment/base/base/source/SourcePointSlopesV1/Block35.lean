/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0280
import SourceMainFramesV1.Point0281
import SourceMainFramesV1.Point0282
import SourceMainFramesV1.Point0283
import SourceMainFramesV1.Point0284
import SourceMainFramesV1.Point0285
import SourceMainFramesV1.Point0286
import SourceMainFramesV1.Point0287
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block35
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0280.outputs.2.hi,
 SourceMainFramesV1.Point0281.outputs.2.hi,
 SourceMainFramesV1.Point0282.outputs.2.hi,
 SourceMainFramesV1.Point0283.outputs.2.hi,
 SourceMainFramesV1.Point0284.outputs.2.hi,
 SourceMainFramesV1.Point0285.outputs.2.hi,
 SourceMainFramesV1.Point0286.outputs.2.hi,
 SourceMainFramesV1.Point0287.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 280 ≤ i) (high : i < 288)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=280) domain
     SourceMainFramesV1.Point0280.input_defined SourceMainFramesV1.Point0280.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0280.outputs.2.hi (by
         change SourceMainFramesV1.Point0280.outputs.2.hi ∈ [SourceMainFramesV1.Point0280.outputs.2.hi, SourceMainFramesV1.Point0281.outputs.2.hi, SourceMainFramesV1.Point0282.outputs.2.hi, SourceMainFramesV1.Point0283.outputs.2.hi, SourceMainFramesV1.Point0284.outputs.2.hi, SourceMainFramesV1.Point0285.outputs.2.hi, SourceMainFramesV1.Point0286.outputs.2.hi, SourceMainFramesV1.Point0287.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=281) domain
     SourceMainFramesV1.Point0281.input_defined SourceMainFramesV1.Point0281.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0281.outputs.2.hi (by
         change SourceMainFramesV1.Point0281.outputs.2.hi ∈ [SourceMainFramesV1.Point0280.outputs.2.hi, SourceMainFramesV1.Point0281.outputs.2.hi, SourceMainFramesV1.Point0282.outputs.2.hi, SourceMainFramesV1.Point0283.outputs.2.hi, SourceMainFramesV1.Point0284.outputs.2.hi, SourceMainFramesV1.Point0285.outputs.2.hi, SourceMainFramesV1.Point0286.outputs.2.hi, SourceMainFramesV1.Point0287.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=282) domain
     SourceMainFramesV1.Point0282.input_defined SourceMainFramesV1.Point0282.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0282.outputs.2.hi (by
         change SourceMainFramesV1.Point0282.outputs.2.hi ∈ [SourceMainFramesV1.Point0280.outputs.2.hi, SourceMainFramesV1.Point0281.outputs.2.hi, SourceMainFramesV1.Point0282.outputs.2.hi, SourceMainFramesV1.Point0283.outputs.2.hi, SourceMainFramesV1.Point0284.outputs.2.hi, SourceMainFramesV1.Point0285.outputs.2.hi, SourceMainFramesV1.Point0286.outputs.2.hi, SourceMainFramesV1.Point0287.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=283) domain
     SourceMainFramesV1.Point0283.input_defined SourceMainFramesV1.Point0283.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0283.outputs.2.hi (by
         change SourceMainFramesV1.Point0283.outputs.2.hi ∈ [SourceMainFramesV1.Point0280.outputs.2.hi, SourceMainFramesV1.Point0281.outputs.2.hi, SourceMainFramesV1.Point0282.outputs.2.hi, SourceMainFramesV1.Point0283.outputs.2.hi, SourceMainFramesV1.Point0284.outputs.2.hi, SourceMainFramesV1.Point0285.outputs.2.hi, SourceMainFramesV1.Point0286.outputs.2.hi, SourceMainFramesV1.Point0287.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=284) domain
     SourceMainFramesV1.Point0284.input_defined SourceMainFramesV1.Point0284.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0284.outputs.2.hi (by
         change SourceMainFramesV1.Point0284.outputs.2.hi ∈ [SourceMainFramesV1.Point0280.outputs.2.hi, SourceMainFramesV1.Point0281.outputs.2.hi, SourceMainFramesV1.Point0282.outputs.2.hi, SourceMainFramesV1.Point0283.outputs.2.hi, SourceMainFramesV1.Point0284.outputs.2.hi, SourceMainFramesV1.Point0285.outputs.2.hi, SourceMainFramesV1.Point0286.outputs.2.hi, SourceMainFramesV1.Point0287.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=285) domain
     SourceMainFramesV1.Point0285.input_defined SourceMainFramesV1.Point0285.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0285.outputs.2.hi (by
         change SourceMainFramesV1.Point0285.outputs.2.hi ∈ [SourceMainFramesV1.Point0280.outputs.2.hi, SourceMainFramesV1.Point0281.outputs.2.hi, SourceMainFramesV1.Point0282.outputs.2.hi, SourceMainFramesV1.Point0283.outputs.2.hi, SourceMainFramesV1.Point0284.outputs.2.hi, SourceMainFramesV1.Point0285.outputs.2.hi, SourceMainFramesV1.Point0286.outputs.2.hi, SourceMainFramesV1.Point0287.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=286) domain
     SourceMainFramesV1.Point0286.input_defined SourceMainFramesV1.Point0286.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0286.outputs.2.hi (by
         change SourceMainFramesV1.Point0286.outputs.2.hi ∈ [SourceMainFramesV1.Point0280.outputs.2.hi, SourceMainFramesV1.Point0281.outputs.2.hi, SourceMainFramesV1.Point0282.outputs.2.hi, SourceMainFramesV1.Point0283.outputs.2.hi, SourceMainFramesV1.Point0284.outputs.2.hi, SourceMainFramesV1.Point0285.outputs.2.hi, SourceMainFramesV1.Point0286.outputs.2.hi, SourceMainFramesV1.Point0287.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=287) domain
     SourceMainFramesV1.Point0287.input_defined SourceMainFramesV1.Point0287.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0287.outputs.2.hi (by
         change SourceMainFramesV1.Point0287.outputs.2.hi ∈ [SourceMainFramesV1.Point0280.outputs.2.hi, SourceMainFramesV1.Point0281.outputs.2.hi, SourceMainFramesV1.Point0282.outputs.2.hi, SourceMainFramesV1.Point0283.outputs.2.hi, SourceMainFramesV1.Point0284.outputs.2.hi, SourceMainFramesV1.Point0285.outputs.2.hi, SourceMainFramesV1.Point0286.outputs.2.hi, SourceMainFramesV1.Point0287.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block35
