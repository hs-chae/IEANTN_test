/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0664
import SourceMainFramesV1.Point0665
import SourceMainFramesV1.Point0666
import SourceMainFramesV1.Point0667
import SourceMainFramesV1.Point0668
import SourceMainFramesV1.Point0669
import SourceMainFramesV1.Point0670
import SourceMainFramesV1.Point0671
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block83
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0664.outputs.2.hi,
 SourceMainFramesV1.Point0665.outputs.2.hi,
 SourceMainFramesV1.Point0666.outputs.2.hi,
 SourceMainFramesV1.Point0667.outputs.2.hi,
 SourceMainFramesV1.Point0668.outputs.2.hi,
 SourceMainFramesV1.Point0669.outputs.2.hi,
 SourceMainFramesV1.Point0670.outputs.2.hi,
 SourceMainFramesV1.Point0671.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 664 ≤ i) (high : i < 672)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=664) domain
     SourceMainFramesV1.Point0664.input_defined SourceMainFramesV1.Point0664.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0664.outputs.2.hi (by
         change SourceMainFramesV1.Point0664.outputs.2.hi ∈ [SourceMainFramesV1.Point0664.outputs.2.hi, SourceMainFramesV1.Point0665.outputs.2.hi, SourceMainFramesV1.Point0666.outputs.2.hi, SourceMainFramesV1.Point0667.outputs.2.hi, SourceMainFramesV1.Point0668.outputs.2.hi, SourceMainFramesV1.Point0669.outputs.2.hi, SourceMainFramesV1.Point0670.outputs.2.hi, SourceMainFramesV1.Point0671.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=665) domain
     SourceMainFramesV1.Point0665.input_defined SourceMainFramesV1.Point0665.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0665.outputs.2.hi (by
         change SourceMainFramesV1.Point0665.outputs.2.hi ∈ [SourceMainFramesV1.Point0664.outputs.2.hi, SourceMainFramesV1.Point0665.outputs.2.hi, SourceMainFramesV1.Point0666.outputs.2.hi, SourceMainFramesV1.Point0667.outputs.2.hi, SourceMainFramesV1.Point0668.outputs.2.hi, SourceMainFramesV1.Point0669.outputs.2.hi, SourceMainFramesV1.Point0670.outputs.2.hi, SourceMainFramesV1.Point0671.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=666) domain
     SourceMainFramesV1.Point0666.input_defined SourceMainFramesV1.Point0666.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0666.outputs.2.hi (by
         change SourceMainFramesV1.Point0666.outputs.2.hi ∈ [SourceMainFramesV1.Point0664.outputs.2.hi, SourceMainFramesV1.Point0665.outputs.2.hi, SourceMainFramesV1.Point0666.outputs.2.hi, SourceMainFramesV1.Point0667.outputs.2.hi, SourceMainFramesV1.Point0668.outputs.2.hi, SourceMainFramesV1.Point0669.outputs.2.hi, SourceMainFramesV1.Point0670.outputs.2.hi, SourceMainFramesV1.Point0671.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=667) domain
     SourceMainFramesV1.Point0667.input_defined SourceMainFramesV1.Point0667.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0667.outputs.2.hi (by
         change SourceMainFramesV1.Point0667.outputs.2.hi ∈ [SourceMainFramesV1.Point0664.outputs.2.hi, SourceMainFramesV1.Point0665.outputs.2.hi, SourceMainFramesV1.Point0666.outputs.2.hi, SourceMainFramesV1.Point0667.outputs.2.hi, SourceMainFramesV1.Point0668.outputs.2.hi, SourceMainFramesV1.Point0669.outputs.2.hi, SourceMainFramesV1.Point0670.outputs.2.hi, SourceMainFramesV1.Point0671.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=668) domain
     SourceMainFramesV1.Point0668.input_defined SourceMainFramesV1.Point0668.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0668.outputs.2.hi (by
         change SourceMainFramesV1.Point0668.outputs.2.hi ∈ [SourceMainFramesV1.Point0664.outputs.2.hi, SourceMainFramesV1.Point0665.outputs.2.hi, SourceMainFramesV1.Point0666.outputs.2.hi, SourceMainFramesV1.Point0667.outputs.2.hi, SourceMainFramesV1.Point0668.outputs.2.hi, SourceMainFramesV1.Point0669.outputs.2.hi, SourceMainFramesV1.Point0670.outputs.2.hi, SourceMainFramesV1.Point0671.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=669) domain
     SourceMainFramesV1.Point0669.input_defined SourceMainFramesV1.Point0669.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0669.outputs.2.hi (by
         change SourceMainFramesV1.Point0669.outputs.2.hi ∈ [SourceMainFramesV1.Point0664.outputs.2.hi, SourceMainFramesV1.Point0665.outputs.2.hi, SourceMainFramesV1.Point0666.outputs.2.hi, SourceMainFramesV1.Point0667.outputs.2.hi, SourceMainFramesV1.Point0668.outputs.2.hi, SourceMainFramesV1.Point0669.outputs.2.hi, SourceMainFramesV1.Point0670.outputs.2.hi, SourceMainFramesV1.Point0671.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=670) domain
     SourceMainFramesV1.Point0670.input_defined SourceMainFramesV1.Point0670.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0670.outputs.2.hi (by
         change SourceMainFramesV1.Point0670.outputs.2.hi ∈ [SourceMainFramesV1.Point0664.outputs.2.hi, SourceMainFramesV1.Point0665.outputs.2.hi, SourceMainFramesV1.Point0666.outputs.2.hi, SourceMainFramesV1.Point0667.outputs.2.hi, SourceMainFramesV1.Point0668.outputs.2.hi, SourceMainFramesV1.Point0669.outputs.2.hi, SourceMainFramesV1.Point0670.outputs.2.hi, SourceMainFramesV1.Point0671.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=671) domain
     SourceMainFramesV1.Point0671.input_defined SourceMainFramesV1.Point0671.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0671.outputs.2.hi (by
         change SourceMainFramesV1.Point0671.outputs.2.hi ∈ [SourceMainFramesV1.Point0664.outputs.2.hi, SourceMainFramesV1.Point0665.outputs.2.hi, SourceMainFramesV1.Point0666.outputs.2.hi, SourceMainFramesV1.Point0667.outputs.2.hi, SourceMainFramesV1.Point0668.outputs.2.hi, SourceMainFramesV1.Point0669.outputs.2.hi, SourceMainFramesV1.Point0670.outputs.2.hi, SourceMainFramesV1.Point0671.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block83
