/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0712
import SourceMainFramesV1.Point0713
import SourceMainFramesV1.Point0714
import SourceMainFramesV1.Point0715
import SourceMainFramesV1.Point0716
import SourceMainFramesV1.Point0717
import SourceMainFramesV1.Point0718
import SourceMainFramesV1.Point0719
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block89
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0712.outputs.2.hi,
 SourceMainFramesV1.Point0713.outputs.2.hi,
 SourceMainFramesV1.Point0714.outputs.2.hi,
 SourceMainFramesV1.Point0715.outputs.2.hi,
 SourceMainFramesV1.Point0716.outputs.2.hi,
 SourceMainFramesV1.Point0717.outputs.2.hi,
 SourceMainFramesV1.Point0718.outputs.2.hi,
 SourceMainFramesV1.Point0719.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 712 ≤ i) (high : i < 720)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=712) domain
     SourceMainFramesV1.Point0712.input_defined SourceMainFramesV1.Point0712.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0712.outputs.2.hi (by
         change SourceMainFramesV1.Point0712.outputs.2.hi ∈ [SourceMainFramesV1.Point0712.outputs.2.hi, SourceMainFramesV1.Point0713.outputs.2.hi, SourceMainFramesV1.Point0714.outputs.2.hi, SourceMainFramesV1.Point0715.outputs.2.hi, SourceMainFramesV1.Point0716.outputs.2.hi, SourceMainFramesV1.Point0717.outputs.2.hi, SourceMainFramesV1.Point0718.outputs.2.hi, SourceMainFramesV1.Point0719.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=713) domain
     SourceMainFramesV1.Point0713.input_defined SourceMainFramesV1.Point0713.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0713.outputs.2.hi (by
         change SourceMainFramesV1.Point0713.outputs.2.hi ∈ [SourceMainFramesV1.Point0712.outputs.2.hi, SourceMainFramesV1.Point0713.outputs.2.hi, SourceMainFramesV1.Point0714.outputs.2.hi, SourceMainFramesV1.Point0715.outputs.2.hi, SourceMainFramesV1.Point0716.outputs.2.hi, SourceMainFramesV1.Point0717.outputs.2.hi, SourceMainFramesV1.Point0718.outputs.2.hi, SourceMainFramesV1.Point0719.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=714) domain
     SourceMainFramesV1.Point0714.input_defined SourceMainFramesV1.Point0714.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0714.outputs.2.hi (by
         change SourceMainFramesV1.Point0714.outputs.2.hi ∈ [SourceMainFramesV1.Point0712.outputs.2.hi, SourceMainFramesV1.Point0713.outputs.2.hi, SourceMainFramesV1.Point0714.outputs.2.hi, SourceMainFramesV1.Point0715.outputs.2.hi, SourceMainFramesV1.Point0716.outputs.2.hi, SourceMainFramesV1.Point0717.outputs.2.hi, SourceMainFramesV1.Point0718.outputs.2.hi, SourceMainFramesV1.Point0719.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=715) domain
     SourceMainFramesV1.Point0715.input_defined SourceMainFramesV1.Point0715.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0715.outputs.2.hi (by
         change SourceMainFramesV1.Point0715.outputs.2.hi ∈ [SourceMainFramesV1.Point0712.outputs.2.hi, SourceMainFramesV1.Point0713.outputs.2.hi, SourceMainFramesV1.Point0714.outputs.2.hi, SourceMainFramesV1.Point0715.outputs.2.hi, SourceMainFramesV1.Point0716.outputs.2.hi, SourceMainFramesV1.Point0717.outputs.2.hi, SourceMainFramesV1.Point0718.outputs.2.hi, SourceMainFramesV1.Point0719.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=716) domain
     SourceMainFramesV1.Point0716.input_defined SourceMainFramesV1.Point0716.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0716.outputs.2.hi (by
         change SourceMainFramesV1.Point0716.outputs.2.hi ∈ [SourceMainFramesV1.Point0712.outputs.2.hi, SourceMainFramesV1.Point0713.outputs.2.hi, SourceMainFramesV1.Point0714.outputs.2.hi, SourceMainFramesV1.Point0715.outputs.2.hi, SourceMainFramesV1.Point0716.outputs.2.hi, SourceMainFramesV1.Point0717.outputs.2.hi, SourceMainFramesV1.Point0718.outputs.2.hi, SourceMainFramesV1.Point0719.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=717) domain
     SourceMainFramesV1.Point0717.input_defined SourceMainFramesV1.Point0717.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0717.outputs.2.hi (by
         change SourceMainFramesV1.Point0717.outputs.2.hi ∈ [SourceMainFramesV1.Point0712.outputs.2.hi, SourceMainFramesV1.Point0713.outputs.2.hi, SourceMainFramesV1.Point0714.outputs.2.hi, SourceMainFramesV1.Point0715.outputs.2.hi, SourceMainFramesV1.Point0716.outputs.2.hi, SourceMainFramesV1.Point0717.outputs.2.hi, SourceMainFramesV1.Point0718.outputs.2.hi, SourceMainFramesV1.Point0719.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=718) domain
     SourceMainFramesV1.Point0718.input_defined SourceMainFramesV1.Point0718.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0718.outputs.2.hi (by
         change SourceMainFramesV1.Point0718.outputs.2.hi ∈ [SourceMainFramesV1.Point0712.outputs.2.hi, SourceMainFramesV1.Point0713.outputs.2.hi, SourceMainFramesV1.Point0714.outputs.2.hi, SourceMainFramesV1.Point0715.outputs.2.hi, SourceMainFramesV1.Point0716.outputs.2.hi, SourceMainFramesV1.Point0717.outputs.2.hi, SourceMainFramesV1.Point0718.outputs.2.hi, SourceMainFramesV1.Point0719.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=719) domain
     SourceMainFramesV1.Point0719.input_defined SourceMainFramesV1.Point0719.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0719.outputs.2.hi (by
         change SourceMainFramesV1.Point0719.outputs.2.hi ∈ [SourceMainFramesV1.Point0712.outputs.2.hi, SourceMainFramesV1.Point0713.outputs.2.hi, SourceMainFramesV1.Point0714.outputs.2.hi, SourceMainFramesV1.Point0715.outputs.2.hi, SourceMainFramesV1.Point0716.outputs.2.hi, SourceMainFramesV1.Point0717.outputs.2.hi, SourceMainFramesV1.Point0718.outputs.2.hi, SourceMainFramesV1.Point0719.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block89
