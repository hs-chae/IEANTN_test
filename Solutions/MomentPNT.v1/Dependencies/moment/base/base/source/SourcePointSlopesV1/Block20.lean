/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0160
import SourceMainFramesV1.Point0161
import SourceMainFramesV1.Point0162
import SourceMainFramesV1.Point0163
import SourceMainFramesV1.Point0164
import SourceMainFramesV1.Point0165
import SourceMainFramesV1.Point0166
import SourceMainFramesV1.Point0167
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block20
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0160.outputs.2.hi,
 SourceMainFramesV1.Point0161.outputs.2.hi,
 SourceMainFramesV1.Point0162.outputs.2.hi,
 SourceMainFramesV1.Point0163.outputs.2.hi,
 SourceMainFramesV1.Point0164.outputs.2.hi,
 SourceMainFramesV1.Point0165.outputs.2.hi,
 SourceMainFramesV1.Point0166.outputs.2.hi,
 SourceMainFramesV1.Point0167.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 160 ≤ i) (high : i < 168)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=160) domain
     SourceMainFramesV1.Point0160.input_defined SourceMainFramesV1.Point0160.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0160.outputs.2.hi (by
         change SourceMainFramesV1.Point0160.outputs.2.hi ∈ [SourceMainFramesV1.Point0160.outputs.2.hi, SourceMainFramesV1.Point0161.outputs.2.hi, SourceMainFramesV1.Point0162.outputs.2.hi, SourceMainFramesV1.Point0163.outputs.2.hi, SourceMainFramesV1.Point0164.outputs.2.hi, SourceMainFramesV1.Point0165.outputs.2.hi, SourceMainFramesV1.Point0166.outputs.2.hi, SourceMainFramesV1.Point0167.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=161) domain
     SourceMainFramesV1.Point0161.input_defined SourceMainFramesV1.Point0161.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0161.outputs.2.hi (by
         change SourceMainFramesV1.Point0161.outputs.2.hi ∈ [SourceMainFramesV1.Point0160.outputs.2.hi, SourceMainFramesV1.Point0161.outputs.2.hi, SourceMainFramesV1.Point0162.outputs.2.hi, SourceMainFramesV1.Point0163.outputs.2.hi, SourceMainFramesV1.Point0164.outputs.2.hi, SourceMainFramesV1.Point0165.outputs.2.hi, SourceMainFramesV1.Point0166.outputs.2.hi, SourceMainFramesV1.Point0167.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=162) domain
     SourceMainFramesV1.Point0162.input_defined SourceMainFramesV1.Point0162.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0162.outputs.2.hi (by
         change SourceMainFramesV1.Point0162.outputs.2.hi ∈ [SourceMainFramesV1.Point0160.outputs.2.hi, SourceMainFramesV1.Point0161.outputs.2.hi, SourceMainFramesV1.Point0162.outputs.2.hi, SourceMainFramesV1.Point0163.outputs.2.hi, SourceMainFramesV1.Point0164.outputs.2.hi, SourceMainFramesV1.Point0165.outputs.2.hi, SourceMainFramesV1.Point0166.outputs.2.hi, SourceMainFramesV1.Point0167.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=163) domain
     SourceMainFramesV1.Point0163.input_defined SourceMainFramesV1.Point0163.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0163.outputs.2.hi (by
         change SourceMainFramesV1.Point0163.outputs.2.hi ∈ [SourceMainFramesV1.Point0160.outputs.2.hi, SourceMainFramesV1.Point0161.outputs.2.hi, SourceMainFramesV1.Point0162.outputs.2.hi, SourceMainFramesV1.Point0163.outputs.2.hi, SourceMainFramesV1.Point0164.outputs.2.hi, SourceMainFramesV1.Point0165.outputs.2.hi, SourceMainFramesV1.Point0166.outputs.2.hi, SourceMainFramesV1.Point0167.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=164) domain
     SourceMainFramesV1.Point0164.input_defined SourceMainFramesV1.Point0164.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0164.outputs.2.hi (by
         change SourceMainFramesV1.Point0164.outputs.2.hi ∈ [SourceMainFramesV1.Point0160.outputs.2.hi, SourceMainFramesV1.Point0161.outputs.2.hi, SourceMainFramesV1.Point0162.outputs.2.hi, SourceMainFramesV1.Point0163.outputs.2.hi, SourceMainFramesV1.Point0164.outputs.2.hi, SourceMainFramesV1.Point0165.outputs.2.hi, SourceMainFramesV1.Point0166.outputs.2.hi, SourceMainFramesV1.Point0167.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=165) domain
     SourceMainFramesV1.Point0165.input_defined SourceMainFramesV1.Point0165.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0165.outputs.2.hi (by
         change SourceMainFramesV1.Point0165.outputs.2.hi ∈ [SourceMainFramesV1.Point0160.outputs.2.hi, SourceMainFramesV1.Point0161.outputs.2.hi, SourceMainFramesV1.Point0162.outputs.2.hi, SourceMainFramesV1.Point0163.outputs.2.hi, SourceMainFramesV1.Point0164.outputs.2.hi, SourceMainFramesV1.Point0165.outputs.2.hi, SourceMainFramesV1.Point0166.outputs.2.hi, SourceMainFramesV1.Point0167.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=166) domain
     SourceMainFramesV1.Point0166.input_defined SourceMainFramesV1.Point0166.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0166.outputs.2.hi (by
         change SourceMainFramesV1.Point0166.outputs.2.hi ∈ [SourceMainFramesV1.Point0160.outputs.2.hi, SourceMainFramesV1.Point0161.outputs.2.hi, SourceMainFramesV1.Point0162.outputs.2.hi, SourceMainFramesV1.Point0163.outputs.2.hi, SourceMainFramesV1.Point0164.outputs.2.hi, SourceMainFramesV1.Point0165.outputs.2.hi, SourceMainFramesV1.Point0166.outputs.2.hi, SourceMainFramesV1.Point0167.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=167) domain
     SourceMainFramesV1.Point0167.input_defined SourceMainFramesV1.Point0167.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0167.outputs.2.hi (by
         change SourceMainFramesV1.Point0167.outputs.2.hi ∈ [SourceMainFramesV1.Point0160.outputs.2.hi, SourceMainFramesV1.Point0161.outputs.2.hi, SourceMainFramesV1.Point0162.outputs.2.hi, SourceMainFramesV1.Point0163.outputs.2.hi, SourceMainFramesV1.Point0164.outputs.2.hi, SourceMainFramesV1.Point0165.outputs.2.hi, SourceMainFramesV1.Point0166.outputs.2.hi, SourceMainFramesV1.Point0167.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block20
