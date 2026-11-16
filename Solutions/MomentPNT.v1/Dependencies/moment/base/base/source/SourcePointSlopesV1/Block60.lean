/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0480
import SourceMainFramesV1.Point0481
import SourceMainFramesV1.Point0482
import SourceMainFramesV1.Point0483
import SourceMainFramesV1.Point0484
import SourceMainFramesV1.Point0485
import SourceMainFramesV1.Point0486
import SourceMainFramesV1.Point0487
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block60
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0480.outputs.2.hi,
 SourceMainFramesV1.Point0481.outputs.2.hi,
 SourceMainFramesV1.Point0482.outputs.2.hi,
 SourceMainFramesV1.Point0483.outputs.2.hi,
 SourceMainFramesV1.Point0484.outputs.2.hi,
 SourceMainFramesV1.Point0485.outputs.2.hi,
 SourceMainFramesV1.Point0486.outputs.2.hi,
 SourceMainFramesV1.Point0487.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 480 ≤ i) (high : i < 488)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=480) domain
     SourceMainFramesV1.Point0480.input_defined SourceMainFramesV1.Point0480.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0480.outputs.2.hi (by
         change SourceMainFramesV1.Point0480.outputs.2.hi ∈ [SourceMainFramesV1.Point0480.outputs.2.hi, SourceMainFramesV1.Point0481.outputs.2.hi, SourceMainFramesV1.Point0482.outputs.2.hi, SourceMainFramesV1.Point0483.outputs.2.hi, SourceMainFramesV1.Point0484.outputs.2.hi, SourceMainFramesV1.Point0485.outputs.2.hi, SourceMainFramesV1.Point0486.outputs.2.hi, SourceMainFramesV1.Point0487.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=481) domain
     SourceMainFramesV1.Point0481.input_defined SourceMainFramesV1.Point0481.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0481.outputs.2.hi (by
         change SourceMainFramesV1.Point0481.outputs.2.hi ∈ [SourceMainFramesV1.Point0480.outputs.2.hi, SourceMainFramesV1.Point0481.outputs.2.hi, SourceMainFramesV1.Point0482.outputs.2.hi, SourceMainFramesV1.Point0483.outputs.2.hi, SourceMainFramesV1.Point0484.outputs.2.hi, SourceMainFramesV1.Point0485.outputs.2.hi, SourceMainFramesV1.Point0486.outputs.2.hi, SourceMainFramesV1.Point0487.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=482) domain
     SourceMainFramesV1.Point0482.input_defined SourceMainFramesV1.Point0482.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0482.outputs.2.hi (by
         change SourceMainFramesV1.Point0482.outputs.2.hi ∈ [SourceMainFramesV1.Point0480.outputs.2.hi, SourceMainFramesV1.Point0481.outputs.2.hi, SourceMainFramesV1.Point0482.outputs.2.hi, SourceMainFramesV1.Point0483.outputs.2.hi, SourceMainFramesV1.Point0484.outputs.2.hi, SourceMainFramesV1.Point0485.outputs.2.hi, SourceMainFramesV1.Point0486.outputs.2.hi, SourceMainFramesV1.Point0487.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=483) domain
     SourceMainFramesV1.Point0483.input_defined SourceMainFramesV1.Point0483.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0483.outputs.2.hi (by
         change SourceMainFramesV1.Point0483.outputs.2.hi ∈ [SourceMainFramesV1.Point0480.outputs.2.hi, SourceMainFramesV1.Point0481.outputs.2.hi, SourceMainFramesV1.Point0482.outputs.2.hi, SourceMainFramesV1.Point0483.outputs.2.hi, SourceMainFramesV1.Point0484.outputs.2.hi, SourceMainFramesV1.Point0485.outputs.2.hi, SourceMainFramesV1.Point0486.outputs.2.hi, SourceMainFramesV1.Point0487.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=484) domain
     SourceMainFramesV1.Point0484.input_defined SourceMainFramesV1.Point0484.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0484.outputs.2.hi (by
         change SourceMainFramesV1.Point0484.outputs.2.hi ∈ [SourceMainFramesV1.Point0480.outputs.2.hi, SourceMainFramesV1.Point0481.outputs.2.hi, SourceMainFramesV1.Point0482.outputs.2.hi, SourceMainFramesV1.Point0483.outputs.2.hi, SourceMainFramesV1.Point0484.outputs.2.hi, SourceMainFramesV1.Point0485.outputs.2.hi, SourceMainFramesV1.Point0486.outputs.2.hi, SourceMainFramesV1.Point0487.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=485) domain
     SourceMainFramesV1.Point0485.input_defined SourceMainFramesV1.Point0485.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0485.outputs.2.hi (by
         change SourceMainFramesV1.Point0485.outputs.2.hi ∈ [SourceMainFramesV1.Point0480.outputs.2.hi, SourceMainFramesV1.Point0481.outputs.2.hi, SourceMainFramesV1.Point0482.outputs.2.hi, SourceMainFramesV1.Point0483.outputs.2.hi, SourceMainFramesV1.Point0484.outputs.2.hi, SourceMainFramesV1.Point0485.outputs.2.hi, SourceMainFramesV1.Point0486.outputs.2.hi, SourceMainFramesV1.Point0487.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=486) domain
     SourceMainFramesV1.Point0486.input_defined SourceMainFramesV1.Point0486.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0486.outputs.2.hi (by
         change SourceMainFramesV1.Point0486.outputs.2.hi ∈ [SourceMainFramesV1.Point0480.outputs.2.hi, SourceMainFramesV1.Point0481.outputs.2.hi, SourceMainFramesV1.Point0482.outputs.2.hi, SourceMainFramesV1.Point0483.outputs.2.hi, SourceMainFramesV1.Point0484.outputs.2.hi, SourceMainFramesV1.Point0485.outputs.2.hi, SourceMainFramesV1.Point0486.outputs.2.hi, SourceMainFramesV1.Point0487.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=487) domain
     SourceMainFramesV1.Point0487.input_defined SourceMainFramesV1.Point0487.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0487.outputs.2.hi (by
         change SourceMainFramesV1.Point0487.outputs.2.hi ∈ [SourceMainFramesV1.Point0480.outputs.2.hi, SourceMainFramesV1.Point0481.outputs.2.hi, SourceMainFramesV1.Point0482.outputs.2.hi, SourceMainFramesV1.Point0483.outputs.2.hi, SourceMainFramesV1.Point0484.outputs.2.hi, SourceMainFramesV1.Point0485.outputs.2.hi, SourceMainFramesV1.Point0486.outputs.2.hi, SourceMainFramesV1.Point0487.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block60
