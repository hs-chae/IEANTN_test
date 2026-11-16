/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0040
import SourceMainFramesV1.Point0041
import SourceMainFramesV1.Point0042
import SourceMainFramesV1.Point0043
import SourceMainFramesV1.Point0044
import SourceMainFramesV1.Point0045
import SourceMainFramesV1.Point0046
import SourceMainFramesV1.Point0047
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block05
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0040.outputs.2.hi,
 SourceMainFramesV1.Point0041.outputs.2.hi,
 SourceMainFramesV1.Point0042.outputs.2.hi,
 SourceMainFramesV1.Point0043.outputs.2.hi,
 SourceMainFramesV1.Point0044.outputs.2.hi,
 SourceMainFramesV1.Point0045.outputs.2.hi,
 SourceMainFramesV1.Point0046.outputs.2.hi,
 SourceMainFramesV1.Point0047.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 40 ≤ i) (high : i < 48)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=40) domain
     SourceMainFramesV1.Point0040.input_defined SourceMainFramesV1.Point0040.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0040.outputs.2.hi (by
         change SourceMainFramesV1.Point0040.outputs.2.hi ∈ [SourceMainFramesV1.Point0040.outputs.2.hi, SourceMainFramesV1.Point0041.outputs.2.hi, SourceMainFramesV1.Point0042.outputs.2.hi, SourceMainFramesV1.Point0043.outputs.2.hi, SourceMainFramesV1.Point0044.outputs.2.hi, SourceMainFramesV1.Point0045.outputs.2.hi, SourceMainFramesV1.Point0046.outputs.2.hi, SourceMainFramesV1.Point0047.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=41) domain
     SourceMainFramesV1.Point0041.input_defined SourceMainFramesV1.Point0041.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0041.outputs.2.hi (by
         change SourceMainFramesV1.Point0041.outputs.2.hi ∈ [SourceMainFramesV1.Point0040.outputs.2.hi, SourceMainFramesV1.Point0041.outputs.2.hi, SourceMainFramesV1.Point0042.outputs.2.hi, SourceMainFramesV1.Point0043.outputs.2.hi, SourceMainFramesV1.Point0044.outputs.2.hi, SourceMainFramesV1.Point0045.outputs.2.hi, SourceMainFramesV1.Point0046.outputs.2.hi, SourceMainFramesV1.Point0047.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=42) domain
     SourceMainFramesV1.Point0042.input_defined SourceMainFramesV1.Point0042.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0042.outputs.2.hi (by
         change SourceMainFramesV1.Point0042.outputs.2.hi ∈ [SourceMainFramesV1.Point0040.outputs.2.hi, SourceMainFramesV1.Point0041.outputs.2.hi, SourceMainFramesV1.Point0042.outputs.2.hi, SourceMainFramesV1.Point0043.outputs.2.hi, SourceMainFramesV1.Point0044.outputs.2.hi, SourceMainFramesV1.Point0045.outputs.2.hi, SourceMainFramesV1.Point0046.outputs.2.hi, SourceMainFramesV1.Point0047.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=43) domain
     SourceMainFramesV1.Point0043.input_defined SourceMainFramesV1.Point0043.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0043.outputs.2.hi (by
         change SourceMainFramesV1.Point0043.outputs.2.hi ∈ [SourceMainFramesV1.Point0040.outputs.2.hi, SourceMainFramesV1.Point0041.outputs.2.hi, SourceMainFramesV1.Point0042.outputs.2.hi, SourceMainFramesV1.Point0043.outputs.2.hi, SourceMainFramesV1.Point0044.outputs.2.hi, SourceMainFramesV1.Point0045.outputs.2.hi, SourceMainFramesV1.Point0046.outputs.2.hi, SourceMainFramesV1.Point0047.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=44) domain
     SourceMainFramesV1.Point0044.input_defined SourceMainFramesV1.Point0044.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0044.outputs.2.hi (by
         change SourceMainFramesV1.Point0044.outputs.2.hi ∈ [SourceMainFramesV1.Point0040.outputs.2.hi, SourceMainFramesV1.Point0041.outputs.2.hi, SourceMainFramesV1.Point0042.outputs.2.hi, SourceMainFramesV1.Point0043.outputs.2.hi, SourceMainFramesV1.Point0044.outputs.2.hi, SourceMainFramesV1.Point0045.outputs.2.hi, SourceMainFramesV1.Point0046.outputs.2.hi, SourceMainFramesV1.Point0047.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=45) domain
     SourceMainFramesV1.Point0045.input_defined SourceMainFramesV1.Point0045.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0045.outputs.2.hi (by
         change SourceMainFramesV1.Point0045.outputs.2.hi ∈ [SourceMainFramesV1.Point0040.outputs.2.hi, SourceMainFramesV1.Point0041.outputs.2.hi, SourceMainFramesV1.Point0042.outputs.2.hi, SourceMainFramesV1.Point0043.outputs.2.hi, SourceMainFramesV1.Point0044.outputs.2.hi, SourceMainFramesV1.Point0045.outputs.2.hi, SourceMainFramesV1.Point0046.outputs.2.hi, SourceMainFramesV1.Point0047.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=46) domain
     SourceMainFramesV1.Point0046.input_defined SourceMainFramesV1.Point0046.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0046.outputs.2.hi (by
         change SourceMainFramesV1.Point0046.outputs.2.hi ∈ [SourceMainFramesV1.Point0040.outputs.2.hi, SourceMainFramesV1.Point0041.outputs.2.hi, SourceMainFramesV1.Point0042.outputs.2.hi, SourceMainFramesV1.Point0043.outputs.2.hi, SourceMainFramesV1.Point0044.outputs.2.hi, SourceMainFramesV1.Point0045.outputs.2.hi, SourceMainFramesV1.Point0046.outputs.2.hi, SourceMainFramesV1.Point0047.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=47) domain
     SourceMainFramesV1.Point0047.input_defined SourceMainFramesV1.Point0047.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0047.outputs.2.hi (by
         change SourceMainFramesV1.Point0047.outputs.2.hi ∈ [SourceMainFramesV1.Point0040.outputs.2.hi, SourceMainFramesV1.Point0041.outputs.2.hi, SourceMainFramesV1.Point0042.outputs.2.hi, SourceMainFramesV1.Point0043.outputs.2.hi, SourceMainFramesV1.Point0044.outputs.2.hi, SourceMainFramesV1.Point0045.outputs.2.hi, SourceMainFramesV1.Point0046.outputs.2.hi, SourceMainFramesV1.Point0047.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block05
