/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0032
import SourceMainFramesV1.Point0033
import SourceMainFramesV1.Point0034
import SourceMainFramesV1.Point0035
import SourceMainFramesV1.Point0036
import SourceMainFramesV1.Point0037
import SourceMainFramesV1.Point0038
import SourceMainFramesV1.Point0039
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block04
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0032.outputs.2.hi,
 SourceMainFramesV1.Point0033.outputs.2.hi,
 SourceMainFramesV1.Point0034.outputs.2.hi,
 SourceMainFramesV1.Point0035.outputs.2.hi,
 SourceMainFramesV1.Point0036.outputs.2.hi,
 SourceMainFramesV1.Point0037.outputs.2.hi,
 SourceMainFramesV1.Point0038.outputs.2.hi,
 SourceMainFramesV1.Point0039.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 32 ≤ i) (high : i < 40)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=32) domain
     SourceMainFramesV1.Point0032.input_defined SourceMainFramesV1.Point0032.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0032.outputs.2.hi (by
         change SourceMainFramesV1.Point0032.outputs.2.hi ∈ [SourceMainFramesV1.Point0032.outputs.2.hi, SourceMainFramesV1.Point0033.outputs.2.hi, SourceMainFramesV1.Point0034.outputs.2.hi, SourceMainFramesV1.Point0035.outputs.2.hi, SourceMainFramesV1.Point0036.outputs.2.hi, SourceMainFramesV1.Point0037.outputs.2.hi, SourceMainFramesV1.Point0038.outputs.2.hi, SourceMainFramesV1.Point0039.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=33) domain
     SourceMainFramesV1.Point0033.input_defined SourceMainFramesV1.Point0033.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0033.outputs.2.hi (by
         change SourceMainFramesV1.Point0033.outputs.2.hi ∈ [SourceMainFramesV1.Point0032.outputs.2.hi, SourceMainFramesV1.Point0033.outputs.2.hi, SourceMainFramesV1.Point0034.outputs.2.hi, SourceMainFramesV1.Point0035.outputs.2.hi, SourceMainFramesV1.Point0036.outputs.2.hi, SourceMainFramesV1.Point0037.outputs.2.hi, SourceMainFramesV1.Point0038.outputs.2.hi, SourceMainFramesV1.Point0039.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=34) domain
     SourceMainFramesV1.Point0034.input_defined SourceMainFramesV1.Point0034.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0034.outputs.2.hi (by
         change SourceMainFramesV1.Point0034.outputs.2.hi ∈ [SourceMainFramesV1.Point0032.outputs.2.hi, SourceMainFramesV1.Point0033.outputs.2.hi, SourceMainFramesV1.Point0034.outputs.2.hi, SourceMainFramesV1.Point0035.outputs.2.hi, SourceMainFramesV1.Point0036.outputs.2.hi, SourceMainFramesV1.Point0037.outputs.2.hi, SourceMainFramesV1.Point0038.outputs.2.hi, SourceMainFramesV1.Point0039.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=35) domain
     SourceMainFramesV1.Point0035.input_defined SourceMainFramesV1.Point0035.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0035.outputs.2.hi (by
         change SourceMainFramesV1.Point0035.outputs.2.hi ∈ [SourceMainFramesV1.Point0032.outputs.2.hi, SourceMainFramesV1.Point0033.outputs.2.hi, SourceMainFramesV1.Point0034.outputs.2.hi, SourceMainFramesV1.Point0035.outputs.2.hi, SourceMainFramesV1.Point0036.outputs.2.hi, SourceMainFramesV1.Point0037.outputs.2.hi, SourceMainFramesV1.Point0038.outputs.2.hi, SourceMainFramesV1.Point0039.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=36) domain
     SourceMainFramesV1.Point0036.input_defined SourceMainFramesV1.Point0036.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0036.outputs.2.hi (by
         change SourceMainFramesV1.Point0036.outputs.2.hi ∈ [SourceMainFramesV1.Point0032.outputs.2.hi, SourceMainFramesV1.Point0033.outputs.2.hi, SourceMainFramesV1.Point0034.outputs.2.hi, SourceMainFramesV1.Point0035.outputs.2.hi, SourceMainFramesV1.Point0036.outputs.2.hi, SourceMainFramesV1.Point0037.outputs.2.hi, SourceMainFramesV1.Point0038.outputs.2.hi, SourceMainFramesV1.Point0039.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=37) domain
     SourceMainFramesV1.Point0037.input_defined SourceMainFramesV1.Point0037.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0037.outputs.2.hi (by
         change SourceMainFramesV1.Point0037.outputs.2.hi ∈ [SourceMainFramesV1.Point0032.outputs.2.hi, SourceMainFramesV1.Point0033.outputs.2.hi, SourceMainFramesV1.Point0034.outputs.2.hi, SourceMainFramesV1.Point0035.outputs.2.hi, SourceMainFramesV1.Point0036.outputs.2.hi, SourceMainFramesV1.Point0037.outputs.2.hi, SourceMainFramesV1.Point0038.outputs.2.hi, SourceMainFramesV1.Point0039.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=38) domain
     SourceMainFramesV1.Point0038.input_defined SourceMainFramesV1.Point0038.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0038.outputs.2.hi (by
         change SourceMainFramesV1.Point0038.outputs.2.hi ∈ [SourceMainFramesV1.Point0032.outputs.2.hi, SourceMainFramesV1.Point0033.outputs.2.hi, SourceMainFramesV1.Point0034.outputs.2.hi, SourceMainFramesV1.Point0035.outputs.2.hi, SourceMainFramesV1.Point0036.outputs.2.hi, SourceMainFramesV1.Point0037.outputs.2.hi, SourceMainFramesV1.Point0038.outputs.2.hi, SourceMainFramesV1.Point0039.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=39) domain
     SourceMainFramesV1.Point0039.input_defined SourceMainFramesV1.Point0039.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0039.outputs.2.hi (by
         change SourceMainFramesV1.Point0039.outputs.2.hi ∈ [SourceMainFramesV1.Point0032.outputs.2.hi, SourceMainFramesV1.Point0033.outputs.2.hi, SourceMainFramesV1.Point0034.outputs.2.hi, SourceMainFramesV1.Point0035.outputs.2.hi, SourceMainFramesV1.Point0036.outputs.2.hi, SourceMainFramesV1.Point0037.outputs.2.hi, SourceMainFramesV1.Point0038.outputs.2.hi, SourceMainFramesV1.Point0039.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block04
