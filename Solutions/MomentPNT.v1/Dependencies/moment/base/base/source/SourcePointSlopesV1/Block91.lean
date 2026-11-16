/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0728
import SourceMainFramesV1.Point0729
import SourceMainFramesV1.Point0730
import SourceMainFramesV1.Point0731
import SourceMainFramesV1.Point0732
import SourceMainFramesV1.Point0733
import SourceMainFramesV1.Point0734
import SourceMainFramesV1.Point0735
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block91
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0728.outputs.2.hi,
 SourceMainFramesV1.Point0729.outputs.2.hi,
 SourceMainFramesV1.Point0730.outputs.2.hi,
 SourceMainFramesV1.Point0731.outputs.2.hi,
 SourceMainFramesV1.Point0732.outputs.2.hi,
 SourceMainFramesV1.Point0733.outputs.2.hi,
 SourceMainFramesV1.Point0734.outputs.2.hi,
 SourceMainFramesV1.Point0735.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 728 ≤ i) (high : i < 736)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=728) domain
     SourceMainFramesV1.Point0728.input_defined SourceMainFramesV1.Point0728.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0728.outputs.2.hi (by
         change SourceMainFramesV1.Point0728.outputs.2.hi ∈ [SourceMainFramesV1.Point0728.outputs.2.hi, SourceMainFramesV1.Point0729.outputs.2.hi, SourceMainFramesV1.Point0730.outputs.2.hi, SourceMainFramesV1.Point0731.outputs.2.hi, SourceMainFramesV1.Point0732.outputs.2.hi, SourceMainFramesV1.Point0733.outputs.2.hi, SourceMainFramesV1.Point0734.outputs.2.hi, SourceMainFramesV1.Point0735.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=729) domain
     SourceMainFramesV1.Point0729.input_defined SourceMainFramesV1.Point0729.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0729.outputs.2.hi (by
         change SourceMainFramesV1.Point0729.outputs.2.hi ∈ [SourceMainFramesV1.Point0728.outputs.2.hi, SourceMainFramesV1.Point0729.outputs.2.hi, SourceMainFramesV1.Point0730.outputs.2.hi, SourceMainFramesV1.Point0731.outputs.2.hi, SourceMainFramesV1.Point0732.outputs.2.hi, SourceMainFramesV1.Point0733.outputs.2.hi, SourceMainFramesV1.Point0734.outputs.2.hi, SourceMainFramesV1.Point0735.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=730) domain
     SourceMainFramesV1.Point0730.input_defined SourceMainFramesV1.Point0730.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0730.outputs.2.hi (by
         change SourceMainFramesV1.Point0730.outputs.2.hi ∈ [SourceMainFramesV1.Point0728.outputs.2.hi, SourceMainFramesV1.Point0729.outputs.2.hi, SourceMainFramesV1.Point0730.outputs.2.hi, SourceMainFramesV1.Point0731.outputs.2.hi, SourceMainFramesV1.Point0732.outputs.2.hi, SourceMainFramesV1.Point0733.outputs.2.hi, SourceMainFramesV1.Point0734.outputs.2.hi, SourceMainFramesV1.Point0735.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=731) domain
     SourceMainFramesV1.Point0731.input_defined SourceMainFramesV1.Point0731.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0731.outputs.2.hi (by
         change SourceMainFramesV1.Point0731.outputs.2.hi ∈ [SourceMainFramesV1.Point0728.outputs.2.hi, SourceMainFramesV1.Point0729.outputs.2.hi, SourceMainFramesV1.Point0730.outputs.2.hi, SourceMainFramesV1.Point0731.outputs.2.hi, SourceMainFramesV1.Point0732.outputs.2.hi, SourceMainFramesV1.Point0733.outputs.2.hi, SourceMainFramesV1.Point0734.outputs.2.hi, SourceMainFramesV1.Point0735.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=732) domain
     SourceMainFramesV1.Point0732.input_defined SourceMainFramesV1.Point0732.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0732.outputs.2.hi (by
         change SourceMainFramesV1.Point0732.outputs.2.hi ∈ [SourceMainFramesV1.Point0728.outputs.2.hi, SourceMainFramesV1.Point0729.outputs.2.hi, SourceMainFramesV1.Point0730.outputs.2.hi, SourceMainFramesV1.Point0731.outputs.2.hi, SourceMainFramesV1.Point0732.outputs.2.hi, SourceMainFramesV1.Point0733.outputs.2.hi, SourceMainFramesV1.Point0734.outputs.2.hi, SourceMainFramesV1.Point0735.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=733) domain
     SourceMainFramesV1.Point0733.input_defined SourceMainFramesV1.Point0733.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0733.outputs.2.hi (by
         change SourceMainFramesV1.Point0733.outputs.2.hi ∈ [SourceMainFramesV1.Point0728.outputs.2.hi, SourceMainFramesV1.Point0729.outputs.2.hi, SourceMainFramesV1.Point0730.outputs.2.hi, SourceMainFramesV1.Point0731.outputs.2.hi, SourceMainFramesV1.Point0732.outputs.2.hi, SourceMainFramesV1.Point0733.outputs.2.hi, SourceMainFramesV1.Point0734.outputs.2.hi, SourceMainFramesV1.Point0735.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=734) domain
     SourceMainFramesV1.Point0734.input_defined SourceMainFramesV1.Point0734.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0734.outputs.2.hi (by
         change SourceMainFramesV1.Point0734.outputs.2.hi ∈ [SourceMainFramesV1.Point0728.outputs.2.hi, SourceMainFramesV1.Point0729.outputs.2.hi, SourceMainFramesV1.Point0730.outputs.2.hi, SourceMainFramesV1.Point0731.outputs.2.hi, SourceMainFramesV1.Point0732.outputs.2.hi, SourceMainFramesV1.Point0733.outputs.2.hi, SourceMainFramesV1.Point0734.outputs.2.hi, SourceMainFramesV1.Point0735.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=735) domain
     SourceMainFramesV1.Point0735.input_defined SourceMainFramesV1.Point0735.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0735.outputs.2.hi (by
         change SourceMainFramesV1.Point0735.outputs.2.hi ∈ [SourceMainFramesV1.Point0728.outputs.2.hi, SourceMainFramesV1.Point0729.outputs.2.hi, SourceMainFramesV1.Point0730.outputs.2.hi, SourceMainFramesV1.Point0731.outputs.2.hi, SourceMainFramesV1.Point0732.outputs.2.hi, SourceMainFramesV1.Point0733.outputs.2.hi, SourceMainFramesV1.Point0734.outputs.2.hi, SourceMainFramesV1.Point0735.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block91
