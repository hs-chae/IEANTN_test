/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0024
import SourceMainFramesV1.Point0025
import SourceMainFramesV1.Point0026
import SourceMainFramesV1.Point0027
import SourceMainFramesV1.Point0028
import SourceMainFramesV1.Point0029
import SourceMainFramesV1.Point0030
import SourceMainFramesV1.Point0031
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block03
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0024.outputs.2.hi,
 SourceMainFramesV1.Point0025.outputs.2.hi,
 SourceMainFramesV1.Point0026.outputs.2.hi,
 SourceMainFramesV1.Point0027.outputs.2.hi,
 SourceMainFramesV1.Point0028.outputs.2.hi,
 SourceMainFramesV1.Point0029.outputs.2.hi,
 SourceMainFramesV1.Point0030.outputs.2.hi,
 SourceMainFramesV1.Point0031.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 24 ≤ i) (high : i < 32)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=24) domain
     SourceMainFramesV1.Point0024.input_defined SourceMainFramesV1.Point0024.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0024.outputs.2.hi (by
         change SourceMainFramesV1.Point0024.outputs.2.hi ∈ [SourceMainFramesV1.Point0024.outputs.2.hi, SourceMainFramesV1.Point0025.outputs.2.hi, SourceMainFramesV1.Point0026.outputs.2.hi, SourceMainFramesV1.Point0027.outputs.2.hi, SourceMainFramesV1.Point0028.outputs.2.hi, SourceMainFramesV1.Point0029.outputs.2.hi, SourceMainFramesV1.Point0030.outputs.2.hi, SourceMainFramesV1.Point0031.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=25) domain
     SourceMainFramesV1.Point0025.input_defined SourceMainFramesV1.Point0025.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0025.outputs.2.hi (by
         change SourceMainFramesV1.Point0025.outputs.2.hi ∈ [SourceMainFramesV1.Point0024.outputs.2.hi, SourceMainFramesV1.Point0025.outputs.2.hi, SourceMainFramesV1.Point0026.outputs.2.hi, SourceMainFramesV1.Point0027.outputs.2.hi, SourceMainFramesV1.Point0028.outputs.2.hi, SourceMainFramesV1.Point0029.outputs.2.hi, SourceMainFramesV1.Point0030.outputs.2.hi, SourceMainFramesV1.Point0031.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=26) domain
     SourceMainFramesV1.Point0026.input_defined SourceMainFramesV1.Point0026.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0026.outputs.2.hi (by
         change SourceMainFramesV1.Point0026.outputs.2.hi ∈ [SourceMainFramesV1.Point0024.outputs.2.hi, SourceMainFramesV1.Point0025.outputs.2.hi, SourceMainFramesV1.Point0026.outputs.2.hi, SourceMainFramesV1.Point0027.outputs.2.hi, SourceMainFramesV1.Point0028.outputs.2.hi, SourceMainFramesV1.Point0029.outputs.2.hi, SourceMainFramesV1.Point0030.outputs.2.hi, SourceMainFramesV1.Point0031.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=27) domain
     SourceMainFramesV1.Point0027.input_defined SourceMainFramesV1.Point0027.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0027.outputs.2.hi (by
         change SourceMainFramesV1.Point0027.outputs.2.hi ∈ [SourceMainFramesV1.Point0024.outputs.2.hi, SourceMainFramesV1.Point0025.outputs.2.hi, SourceMainFramesV1.Point0026.outputs.2.hi, SourceMainFramesV1.Point0027.outputs.2.hi, SourceMainFramesV1.Point0028.outputs.2.hi, SourceMainFramesV1.Point0029.outputs.2.hi, SourceMainFramesV1.Point0030.outputs.2.hi, SourceMainFramesV1.Point0031.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=28) domain
     SourceMainFramesV1.Point0028.input_defined SourceMainFramesV1.Point0028.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0028.outputs.2.hi (by
         change SourceMainFramesV1.Point0028.outputs.2.hi ∈ [SourceMainFramesV1.Point0024.outputs.2.hi, SourceMainFramesV1.Point0025.outputs.2.hi, SourceMainFramesV1.Point0026.outputs.2.hi, SourceMainFramesV1.Point0027.outputs.2.hi, SourceMainFramesV1.Point0028.outputs.2.hi, SourceMainFramesV1.Point0029.outputs.2.hi, SourceMainFramesV1.Point0030.outputs.2.hi, SourceMainFramesV1.Point0031.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=29) domain
     SourceMainFramesV1.Point0029.input_defined SourceMainFramesV1.Point0029.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0029.outputs.2.hi (by
         change SourceMainFramesV1.Point0029.outputs.2.hi ∈ [SourceMainFramesV1.Point0024.outputs.2.hi, SourceMainFramesV1.Point0025.outputs.2.hi, SourceMainFramesV1.Point0026.outputs.2.hi, SourceMainFramesV1.Point0027.outputs.2.hi, SourceMainFramesV1.Point0028.outputs.2.hi, SourceMainFramesV1.Point0029.outputs.2.hi, SourceMainFramesV1.Point0030.outputs.2.hi, SourceMainFramesV1.Point0031.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=30) domain
     SourceMainFramesV1.Point0030.input_defined SourceMainFramesV1.Point0030.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0030.outputs.2.hi (by
         change SourceMainFramesV1.Point0030.outputs.2.hi ∈ [SourceMainFramesV1.Point0024.outputs.2.hi, SourceMainFramesV1.Point0025.outputs.2.hi, SourceMainFramesV1.Point0026.outputs.2.hi, SourceMainFramesV1.Point0027.outputs.2.hi, SourceMainFramesV1.Point0028.outputs.2.hi, SourceMainFramesV1.Point0029.outputs.2.hi, SourceMainFramesV1.Point0030.outputs.2.hi, SourceMainFramesV1.Point0031.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=31) domain
     SourceMainFramesV1.Point0031.input_defined SourceMainFramesV1.Point0031.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0031.outputs.2.hi (by
         change SourceMainFramesV1.Point0031.outputs.2.hi ∈ [SourceMainFramesV1.Point0024.outputs.2.hi, SourceMainFramesV1.Point0025.outputs.2.hi, SourceMainFramesV1.Point0026.outputs.2.hi, SourceMainFramesV1.Point0027.outputs.2.hi, SourceMainFramesV1.Point0028.outputs.2.hi, SourceMainFramesV1.Point0029.outputs.2.hi, SourceMainFramesV1.Point0030.outputs.2.hi, SourceMainFramesV1.Point0031.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block03
