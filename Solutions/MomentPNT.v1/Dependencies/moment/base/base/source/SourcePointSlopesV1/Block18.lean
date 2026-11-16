/- Exact bounds on unchanged source-linked C model outputs; no native evaluation. -/
import SourceMainFramesV1.Point0144
import SourceMainFramesV1.Point0145
import SourceMainFramesV1.Point0146
import SourceMainFramesV1.Point0147
import SourceMainFramesV1.Point0148
import SourceMainFramesV1.Point0149
import SourceMainFramesV1.Point0150
import SourceMainFramesV1.Point0151
import SynergyHeightC.MainSlopeRangeAPI
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.Block18
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slopes : List Int := [
 SourceMainFramesV1.Point0144.outputs.2.hi,
 SourceMainFramesV1.Point0145.outputs.2.hi,
 SourceMainFramesV1.Point0146.outputs.2.hi,
 SourceMainFramesV1.Point0147.outputs.2.hi,
 SourceMainFramesV1.Point0148.outputs.2.hi,
 SourceMainFramesV1.Point0149.outputs.2.hi,
 SourceMainFramesV1.Point0150.outputs.2.hi,
 SourceMainFramesV1.Point0151.outputs.2.hi]
theorem checked : slopes.all (fun z=>decide
 (77*ProofBox.scale 128 ≤ z ∧ z ≤ 163*ProofBox.scale 128))=true := by
 decide +kernel
theorem bounds (i : Nat) (low : 144 ≤ i) (high : i < 152)
 (domain : cellDomain i=true) : 77 ≤ pointD i ∧ pointD i ≤ 163 := by
 interval_cases i
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=144) domain
     SourceMainFramesV1.Point0144.input_defined SourceMainFramesV1.Point0144.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0144.outputs.2.hi (by
         change SourceMainFramesV1.Point0144.outputs.2.hi ∈ [SourceMainFramesV1.Point0144.outputs.2.hi, SourceMainFramesV1.Point0145.outputs.2.hi, SourceMainFramesV1.Point0146.outputs.2.hi, SourceMainFramesV1.Point0147.outputs.2.hi, SourceMainFramesV1.Point0148.outputs.2.hi, SourceMainFramesV1.Point0149.outputs.2.hi, SourceMainFramesV1.Point0150.outputs.2.hi, SourceMainFramesV1.Point0151.outputs.2.hi]
         exact List.Mem.head _))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=145) domain
     SourceMainFramesV1.Point0145.input_defined SourceMainFramesV1.Point0145.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0145.outputs.2.hi (by
         change SourceMainFramesV1.Point0145.outputs.2.hi ∈ [SourceMainFramesV1.Point0144.outputs.2.hi, SourceMainFramesV1.Point0145.outputs.2.hi, SourceMainFramesV1.Point0146.outputs.2.hi, SourceMainFramesV1.Point0147.outputs.2.hi, SourceMainFramesV1.Point0148.outputs.2.hi, SourceMainFramesV1.Point0149.outputs.2.hi, SourceMainFramesV1.Point0150.outputs.2.hi, SourceMainFramesV1.Point0151.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.head _)))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=146) domain
     SourceMainFramesV1.Point0146.input_defined SourceMainFramesV1.Point0146.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0146.outputs.2.hi (by
         change SourceMainFramesV1.Point0146.outputs.2.hi ∈ [SourceMainFramesV1.Point0144.outputs.2.hi, SourceMainFramesV1.Point0145.outputs.2.hi, SourceMainFramesV1.Point0146.outputs.2.hi, SourceMainFramesV1.Point0147.outputs.2.hi, SourceMainFramesV1.Point0148.outputs.2.hi, SourceMainFramesV1.Point0149.outputs.2.hi, SourceMainFramesV1.Point0150.outputs.2.hi, SourceMainFramesV1.Point0151.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=147) domain
     SourceMainFramesV1.Point0147.input_defined SourceMainFramesV1.Point0147.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0147.outputs.2.hi (by
         change SourceMainFramesV1.Point0147.outputs.2.hi ∈ [SourceMainFramesV1.Point0144.outputs.2.hi, SourceMainFramesV1.Point0145.outputs.2.hi, SourceMainFramesV1.Point0146.outputs.2.hi, SourceMainFramesV1.Point0147.outputs.2.hi, SourceMainFramesV1.Point0148.outputs.2.hi, SourceMainFramesV1.Point0149.outputs.2.hi, SourceMainFramesV1.Point0150.outputs.2.hi, SourceMainFramesV1.Point0151.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=148) domain
     SourceMainFramesV1.Point0148.input_defined SourceMainFramesV1.Point0148.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0148.outputs.2.hi (by
         change SourceMainFramesV1.Point0148.outputs.2.hi ∈ [SourceMainFramesV1.Point0144.outputs.2.hi, SourceMainFramesV1.Point0145.outputs.2.hi, SourceMainFramesV1.Point0146.outputs.2.hi, SourceMainFramesV1.Point0147.outputs.2.hi, SourceMainFramesV1.Point0148.outputs.2.hi, SourceMainFramesV1.Point0149.outputs.2.hi, SourceMainFramesV1.Point0150.outputs.2.hi, SourceMainFramesV1.Point0151.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=149) domain
     SourceMainFramesV1.Point0149.input_defined SourceMainFramesV1.Point0149.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0149.outputs.2.hi (by
         change SourceMainFramesV1.Point0149.outputs.2.hi ∈ [SourceMainFramesV1.Point0144.outputs.2.hi, SourceMainFramesV1.Point0145.outputs.2.hi, SourceMainFramesV1.Point0146.outputs.2.hi, SourceMainFramesV1.Point0147.outputs.2.hi, SourceMainFramesV1.Point0148.outputs.2.hi, SourceMainFramesV1.Point0149.outputs.2.hi, SourceMainFramesV1.Point0150.outputs.2.hi, SourceMainFramesV1.Point0151.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=150) domain
     SourceMainFramesV1.Point0150.input_defined SourceMainFramesV1.Point0150.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0150.outputs.2.hi (by
         change SourceMainFramesV1.Point0150.outputs.2.hi ∈ [SourceMainFramesV1.Point0144.outputs.2.hi, SourceMainFramesV1.Point0145.outputs.2.hi, SourceMainFramesV1.Point0146.outputs.2.hi, SourceMainFramesV1.Point0147.outputs.2.hi, SourceMainFramesV1.Point0148.outputs.2.hi, SourceMainFramesV1.Point0149.outputs.2.hi, SourceMainFramesV1.Point0150.outputs.2.hi, SourceMainFramesV1.Point0151.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
 · exact SynergyHeightC.MainSlopeRangeAPI.from_outputs (i:=151) domain
     SourceMainFramesV1.Point0151.input_defined SourceMainFramesV1.Point0151.outputs_defined
     (SynergyHeightC.MainSlopeRangeAPI.from_all slopes checked
       SourceMainFramesV1.Point0151.outputs.2.hi (by
         change SourceMainFramesV1.Point0151.outputs.2.hi ∈ [SourceMainFramesV1.Point0144.outputs.2.hi, SourceMainFramesV1.Point0145.outputs.2.hi, SourceMainFramesV1.Point0146.outputs.2.hi, SourceMainFramesV1.Point0147.outputs.2.hi, SourceMainFramesV1.Point0148.outputs.2.hi, SourceMainFramesV1.Point0149.outputs.2.hi, SourceMainFramesV1.Point0150.outputs.2.hi, SourceMainFramesV1.Point0151.outputs.2.hi]
         exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

#print axioms checked
#print axioms bounds
end SourcePointSlopesV1.Block18
