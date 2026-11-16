/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0256
import SourceMainFramesV1.Point0257
import SourceMainFramesV1.Point0258
import SourceMainFramesV1.Point0259
import SourceMainFramesV1.Point0260
import SourceMainFramesV1.Point0261
import SourceMainFramesV1.Point0262
import SourceMainFramesV1.Point0263
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block32
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0256.outputs.2.hi,
 SourceMainFramesV1.Point0257.outputs.2.hi,
 SourceMainFramesV1.Point0258.outputs.2.hi,
 SourceMainFramesV1.Point0259.outputs.2.hi,
 SourceMainFramesV1.Point0260.outputs.2.hi,
 SourceMainFramesV1.Point0261.outputs.2.hi,
 SourceMainFramesV1.Point0262.outputs.2.hi,
 SourceMainFramesV1.Point0263.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 256 ≤ i) (high : i < 264)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=256) domain
     SourceMainFramesV1.Point0256.input_defined SourceMainFramesV1.Point0256.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0256.outputs.2.hi (by
         change SourceMainFramesV1.Point0256.outputs.2.hi ∈ [SourceMainFramesV1.Point0256.outputs.2.hi, SourceMainFramesV1.Point0257.outputs.2.hi, SourceMainFramesV1.Point0258.outputs.2.hi, SourceMainFramesV1.Point0259.outputs.2.hi, SourceMainFramesV1.Point0260.outputs.2.hi, SourceMainFramesV1.Point0261.outputs.2.hi, SourceMainFramesV1.Point0262.outputs.2.hi, SourceMainFramesV1.Point0263.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=257) domain
     SourceMainFramesV1.Point0257.input_defined SourceMainFramesV1.Point0257.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0257.outputs.2.hi (by
         change SourceMainFramesV1.Point0257.outputs.2.hi ∈ [SourceMainFramesV1.Point0256.outputs.2.hi, SourceMainFramesV1.Point0257.outputs.2.hi, SourceMainFramesV1.Point0258.outputs.2.hi, SourceMainFramesV1.Point0259.outputs.2.hi, SourceMainFramesV1.Point0260.outputs.2.hi, SourceMainFramesV1.Point0261.outputs.2.hi, SourceMainFramesV1.Point0262.outputs.2.hi, SourceMainFramesV1.Point0263.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=258) domain
     SourceMainFramesV1.Point0258.input_defined SourceMainFramesV1.Point0258.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0258.outputs.2.hi (by
         change SourceMainFramesV1.Point0258.outputs.2.hi ∈ [SourceMainFramesV1.Point0256.outputs.2.hi, SourceMainFramesV1.Point0257.outputs.2.hi, SourceMainFramesV1.Point0258.outputs.2.hi, SourceMainFramesV1.Point0259.outputs.2.hi, SourceMainFramesV1.Point0260.outputs.2.hi, SourceMainFramesV1.Point0261.outputs.2.hi, SourceMainFramesV1.Point0262.outputs.2.hi, SourceMainFramesV1.Point0263.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=259) domain
     SourceMainFramesV1.Point0259.input_defined SourceMainFramesV1.Point0259.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0259.outputs.2.hi (by
         change SourceMainFramesV1.Point0259.outputs.2.hi ∈ [SourceMainFramesV1.Point0256.outputs.2.hi, SourceMainFramesV1.Point0257.outputs.2.hi, SourceMainFramesV1.Point0258.outputs.2.hi, SourceMainFramesV1.Point0259.outputs.2.hi, SourceMainFramesV1.Point0260.outputs.2.hi, SourceMainFramesV1.Point0261.outputs.2.hi, SourceMainFramesV1.Point0262.outputs.2.hi, SourceMainFramesV1.Point0263.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=260) domain
     SourceMainFramesV1.Point0260.input_defined SourceMainFramesV1.Point0260.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0260.outputs.2.hi (by
         change SourceMainFramesV1.Point0260.outputs.2.hi ∈ [SourceMainFramesV1.Point0256.outputs.2.hi, SourceMainFramesV1.Point0257.outputs.2.hi, SourceMainFramesV1.Point0258.outputs.2.hi, SourceMainFramesV1.Point0259.outputs.2.hi, SourceMainFramesV1.Point0260.outputs.2.hi, SourceMainFramesV1.Point0261.outputs.2.hi, SourceMainFramesV1.Point0262.outputs.2.hi, SourceMainFramesV1.Point0263.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=261) domain
     SourceMainFramesV1.Point0261.input_defined SourceMainFramesV1.Point0261.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0261.outputs.2.hi (by
         change SourceMainFramesV1.Point0261.outputs.2.hi ∈ [SourceMainFramesV1.Point0256.outputs.2.hi, SourceMainFramesV1.Point0257.outputs.2.hi, SourceMainFramesV1.Point0258.outputs.2.hi, SourceMainFramesV1.Point0259.outputs.2.hi, SourceMainFramesV1.Point0260.outputs.2.hi, SourceMainFramesV1.Point0261.outputs.2.hi, SourceMainFramesV1.Point0262.outputs.2.hi, SourceMainFramesV1.Point0263.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=262) domain
     SourceMainFramesV1.Point0262.input_defined SourceMainFramesV1.Point0262.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0262.outputs.2.hi (by
         change SourceMainFramesV1.Point0262.outputs.2.hi ∈ [SourceMainFramesV1.Point0256.outputs.2.hi, SourceMainFramesV1.Point0257.outputs.2.hi, SourceMainFramesV1.Point0258.outputs.2.hi, SourceMainFramesV1.Point0259.outputs.2.hi, SourceMainFramesV1.Point0260.outputs.2.hi, SourceMainFramesV1.Point0261.outputs.2.hi, SourceMainFramesV1.Point0262.outputs.2.hi, SourceMainFramesV1.Point0263.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=263) domain
     SourceMainFramesV1.Point0263.input_defined SourceMainFramesV1.Point0263.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0263.outputs.2.hi (by
         change SourceMainFramesV1.Point0263.outputs.2.hi ∈ [SourceMainFramesV1.Point0256.outputs.2.hi, SourceMainFramesV1.Point0257.outputs.2.hi, SourceMainFramesV1.Point0258.outputs.2.hi, SourceMainFramesV1.Point0259.outputs.2.hi, SourceMainFramesV1.Point0260.outputs.2.hi, SourceMainFramesV1.Point0261.outputs.2.hi, SourceMainFramesV1.Point0262.outputs.2.hi, SourceMainFramesV1.Point0263.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block32
