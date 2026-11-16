/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0016
import SourceMainFramesV1.Point0017
import SourceMainFramesV1.Point0018
import SourceMainFramesV1.Point0019
import SourceMainFramesV1.Point0020
import SourceMainFramesV1.Point0021
import SourceMainFramesV1.Point0022
import SourceMainFramesV1.Point0023
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block02
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0016.outputs.2.hi,
 SourceMainFramesV1.Point0017.outputs.2.hi,
 SourceMainFramesV1.Point0018.outputs.2.hi,
 SourceMainFramesV1.Point0019.outputs.2.hi,
 SourceMainFramesV1.Point0020.outputs.2.hi,
 SourceMainFramesV1.Point0021.outputs.2.hi,
 SourceMainFramesV1.Point0022.outputs.2.hi,
 SourceMainFramesV1.Point0023.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 16 ≤ i) (high : i < 24)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=16) domain
     SourceMainFramesV1.Point0016.input_defined SourceMainFramesV1.Point0016.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0016.outputs.2.hi (by
         change SourceMainFramesV1.Point0016.outputs.2.hi ∈ [SourceMainFramesV1.Point0016.outputs.2.hi, SourceMainFramesV1.Point0017.outputs.2.hi, SourceMainFramesV1.Point0018.outputs.2.hi, SourceMainFramesV1.Point0019.outputs.2.hi, SourceMainFramesV1.Point0020.outputs.2.hi, SourceMainFramesV1.Point0021.outputs.2.hi, SourceMainFramesV1.Point0022.outputs.2.hi, SourceMainFramesV1.Point0023.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=17) domain
     SourceMainFramesV1.Point0017.input_defined SourceMainFramesV1.Point0017.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0017.outputs.2.hi (by
         change SourceMainFramesV1.Point0017.outputs.2.hi ∈ [SourceMainFramesV1.Point0016.outputs.2.hi, SourceMainFramesV1.Point0017.outputs.2.hi, SourceMainFramesV1.Point0018.outputs.2.hi, SourceMainFramesV1.Point0019.outputs.2.hi, SourceMainFramesV1.Point0020.outputs.2.hi, SourceMainFramesV1.Point0021.outputs.2.hi, SourceMainFramesV1.Point0022.outputs.2.hi, SourceMainFramesV1.Point0023.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=18) domain
     SourceMainFramesV1.Point0018.input_defined SourceMainFramesV1.Point0018.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0018.outputs.2.hi (by
         change SourceMainFramesV1.Point0018.outputs.2.hi ∈ [SourceMainFramesV1.Point0016.outputs.2.hi, SourceMainFramesV1.Point0017.outputs.2.hi, SourceMainFramesV1.Point0018.outputs.2.hi, SourceMainFramesV1.Point0019.outputs.2.hi, SourceMainFramesV1.Point0020.outputs.2.hi, SourceMainFramesV1.Point0021.outputs.2.hi, SourceMainFramesV1.Point0022.outputs.2.hi, SourceMainFramesV1.Point0023.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=19) domain
     SourceMainFramesV1.Point0019.input_defined SourceMainFramesV1.Point0019.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0019.outputs.2.hi (by
         change SourceMainFramesV1.Point0019.outputs.2.hi ∈ [SourceMainFramesV1.Point0016.outputs.2.hi, SourceMainFramesV1.Point0017.outputs.2.hi, SourceMainFramesV1.Point0018.outputs.2.hi, SourceMainFramesV1.Point0019.outputs.2.hi, SourceMainFramesV1.Point0020.outputs.2.hi, SourceMainFramesV1.Point0021.outputs.2.hi, SourceMainFramesV1.Point0022.outputs.2.hi, SourceMainFramesV1.Point0023.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=20) domain
     SourceMainFramesV1.Point0020.input_defined SourceMainFramesV1.Point0020.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0020.outputs.2.hi (by
         change SourceMainFramesV1.Point0020.outputs.2.hi ∈ [SourceMainFramesV1.Point0016.outputs.2.hi, SourceMainFramesV1.Point0017.outputs.2.hi, SourceMainFramesV1.Point0018.outputs.2.hi, SourceMainFramesV1.Point0019.outputs.2.hi, SourceMainFramesV1.Point0020.outputs.2.hi, SourceMainFramesV1.Point0021.outputs.2.hi, SourceMainFramesV1.Point0022.outputs.2.hi, SourceMainFramesV1.Point0023.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=21) domain
     SourceMainFramesV1.Point0021.input_defined SourceMainFramesV1.Point0021.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0021.outputs.2.hi (by
         change SourceMainFramesV1.Point0021.outputs.2.hi ∈ [SourceMainFramesV1.Point0016.outputs.2.hi, SourceMainFramesV1.Point0017.outputs.2.hi, SourceMainFramesV1.Point0018.outputs.2.hi, SourceMainFramesV1.Point0019.outputs.2.hi, SourceMainFramesV1.Point0020.outputs.2.hi, SourceMainFramesV1.Point0021.outputs.2.hi, SourceMainFramesV1.Point0022.outputs.2.hi, SourceMainFramesV1.Point0023.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=22) domain
     SourceMainFramesV1.Point0022.input_defined SourceMainFramesV1.Point0022.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0022.outputs.2.hi (by
         change SourceMainFramesV1.Point0022.outputs.2.hi ∈ [SourceMainFramesV1.Point0016.outputs.2.hi, SourceMainFramesV1.Point0017.outputs.2.hi, SourceMainFramesV1.Point0018.outputs.2.hi, SourceMainFramesV1.Point0019.outputs.2.hi, SourceMainFramesV1.Point0020.outputs.2.hi, SourceMainFramesV1.Point0021.outputs.2.hi, SourceMainFramesV1.Point0022.outputs.2.hi, SourceMainFramesV1.Point0023.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=23) domain
     SourceMainFramesV1.Point0023.input_defined SourceMainFramesV1.Point0023.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0023.outputs.2.hi (by
         change SourceMainFramesV1.Point0023.outputs.2.hi ∈ [SourceMainFramesV1.Point0016.outputs.2.hi, SourceMainFramesV1.Point0017.outputs.2.hi, SourceMainFramesV1.Point0018.outputs.2.hi, SourceMainFramesV1.Point0019.outputs.2.hi, SourceMainFramesV1.Point0020.outputs.2.hi, SourceMainFramesV1.Point0021.outputs.2.hi, SourceMainFramesV1.Point0022.outputs.2.hi, SourceMainFramesV1.Point0023.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block02
