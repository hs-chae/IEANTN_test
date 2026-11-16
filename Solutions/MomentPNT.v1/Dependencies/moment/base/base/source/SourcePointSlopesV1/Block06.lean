/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0048
import SourceMainFramesV1.Point0049
import SourceMainFramesV1.Point0050
import SourceMainFramesV1.Point0051
import SourceMainFramesV1.Point0052
import SourceMainFramesV1.Point0053
import SourceMainFramesV1.Point0054
import SourceMainFramesV1.Point0055
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block06
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0048.outputs.2.hi,
 SourceMainFramesV1.Point0049.outputs.2.hi,
 SourceMainFramesV1.Point0050.outputs.2.hi,
 SourceMainFramesV1.Point0051.outputs.2.hi,
 SourceMainFramesV1.Point0052.outputs.2.hi,
 SourceMainFramesV1.Point0053.outputs.2.hi,
 SourceMainFramesV1.Point0054.outputs.2.hi,
 SourceMainFramesV1.Point0055.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 48 ≤ i) (high : i < 56)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=48) domain
     SourceMainFramesV1.Point0048.input_defined SourceMainFramesV1.Point0048.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0048.outputs.2.hi (by
         change SourceMainFramesV1.Point0048.outputs.2.hi ∈ [SourceMainFramesV1.Point0048.outputs.2.hi, SourceMainFramesV1.Point0049.outputs.2.hi, SourceMainFramesV1.Point0050.outputs.2.hi, SourceMainFramesV1.Point0051.outputs.2.hi, SourceMainFramesV1.Point0052.outputs.2.hi, SourceMainFramesV1.Point0053.outputs.2.hi, SourceMainFramesV1.Point0054.outputs.2.hi, SourceMainFramesV1.Point0055.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=49) domain
     SourceMainFramesV1.Point0049.input_defined SourceMainFramesV1.Point0049.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0049.outputs.2.hi (by
         change SourceMainFramesV1.Point0049.outputs.2.hi ∈ [SourceMainFramesV1.Point0048.outputs.2.hi, SourceMainFramesV1.Point0049.outputs.2.hi, SourceMainFramesV1.Point0050.outputs.2.hi, SourceMainFramesV1.Point0051.outputs.2.hi, SourceMainFramesV1.Point0052.outputs.2.hi, SourceMainFramesV1.Point0053.outputs.2.hi, SourceMainFramesV1.Point0054.outputs.2.hi, SourceMainFramesV1.Point0055.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=50) domain
     SourceMainFramesV1.Point0050.input_defined SourceMainFramesV1.Point0050.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0050.outputs.2.hi (by
         change SourceMainFramesV1.Point0050.outputs.2.hi ∈ [SourceMainFramesV1.Point0048.outputs.2.hi, SourceMainFramesV1.Point0049.outputs.2.hi, SourceMainFramesV1.Point0050.outputs.2.hi, SourceMainFramesV1.Point0051.outputs.2.hi, SourceMainFramesV1.Point0052.outputs.2.hi, SourceMainFramesV1.Point0053.outputs.2.hi, SourceMainFramesV1.Point0054.outputs.2.hi, SourceMainFramesV1.Point0055.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=51) domain
     SourceMainFramesV1.Point0051.input_defined SourceMainFramesV1.Point0051.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0051.outputs.2.hi (by
         change SourceMainFramesV1.Point0051.outputs.2.hi ∈ [SourceMainFramesV1.Point0048.outputs.2.hi, SourceMainFramesV1.Point0049.outputs.2.hi, SourceMainFramesV1.Point0050.outputs.2.hi, SourceMainFramesV1.Point0051.outputs.2.hi, SourceMainFramesV1.Point0052.outputs.2.hi, SourceMainFramesV1.Point0053.outputs.2.hi, SourceMainFramesV1.Point0054.outputs.2.hi, SourceMainFramesV1.Point0055.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=52) domain
     SourceMainFramesV1.Point0052.input_defined SourceMainFramesV1.Point0052.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0052.outputs.2.hi (by
         change SourceMainFramesV1.Point0052.outputs.2.hi ∈ [SourceMainFramesV1.Point0048.outputs.2.hi, SourceMainFramesV1.Point0049.outputs.2.hi, SourceMainFramesV1.Point0050.outputs.2.hi, SourceMainFramesV1.Point0051.outputs.2.hi, SourceMainFramesV1.Point0052.outputs.2.hi, SourceMainFramesV1.Point0053.outputs.2.hi, SourceMainFramesV1.Point0054.outputs.2.hi, SourceMainFramesV1.Point0055.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=53) domain
     SourceMainFramesV1.Point0053.input_defined SourceMainFramesV1.Point0053.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0053.outputs.2.hi (by
         change SourceMainFramesV1.Point0053.outputs.2.hi ∈ [SourceMainFramesV1.Point0048.outputs.2.hi, SourceMainFramesV1.Point0049.outputs.2.hi, SourceMainFramesV1.Point0050.outputs.2.hi, SourceMainFramesV1.Point0051.outputs.2.hi, SourceMainFramesV1.Point0052.outputs.2.hi, SourceMainFramesV1.Point0053.outputs.2.hi, SourceMainFramesV1.Point0054.outputs.2.hi, SourceMainFramesV1.Point0055.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=54) domain
     SourceMainFramesV1.Point0054.input_defined SourceMainFramesV1.Point0054.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0054.outputs.2.hi (by
         change SourceMainFramesV1.Point0054.outputs.2.hi ∈ [SourceMainFramesV1.Point0048.outputs.2.hi, SourceMainFramesV1.Point0049.outputs.2.hi, SourceMainFramesV1.Point0050.outputs.2.hi, SourceMainFramesV1.Point0051.outputs.2.hi, SourceMainFramesV1.Point0052.outputs.2.hi, SourceMainFramesV1.Point0053.outputs.2.hi, SourceMainFramesV1.Point0054.outputs.2.hi, SourceMainFramesV1.Point0055.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=55) domain
     SourceMainFramesV1.Point0055.input_defined SourceMainFramesV1.Point0055.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0055.outputs.2.hi (by
         change SourceMainFramesV1.Point0055.outputs.2.hi ∈ [SourceMainFramesV1.Point0048.outputs.2.hi, SourceMainFramesV1.Point0049.outputs.2.hi, SourceMainFramesV1.Point0050.outputs.2.hi, SourceMainFramesV1.Point0051.outputs.2.hi, SourceMainFramesV1.Point0052.outputs.2.hi, SourceMainFramesV1.Point0053.outputs.2.hi, SourceMainFramesV1.Point0054.outputs.2.hi, SourceMainFramesV1.Point0055.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block06
