import SourceMainFramesV1.Point0672
import SourceMainFramesV1.Point0673
import SourceMainFramesV1.Point0674
import SourceMainFramesV1.Point0675
import SourceMainFramesV1.Point0676
import SourceMainFramesV1.Point0677
import SourceMainFramesV1.Point0678
import SourceMainFramesV1.Point0679
import SourceMainFramesV1.Point0680
import SourceMainFramesV1.Point0681
import SourceMainFramesV1.Point0682
import SourceMainFramesV1.Point0683
import SourceMainFramesV1.Point0684
import SourceMainFramesV1.Point0685
import SourceMainFramesV1.Point0686
import SourceMainFramesV1.Point0687
import SourceMainFramesV1.Point0688
import SourceMainFramesV1.Point0689
import SourceMainFramesV1.Point0690
import SourceMainFramesV1.Point0691
import SourceMainFramesV1.Point0692
import SourceMainFramesV1.Point0693
import SourceMainFramesV1.Point0694
import SourceMainFramesV1.Point0695
import SourceMainFramesV1.Point0696
import SourceMainFramesV1.Point0697
import SourceMainFramesV1.Point0698
import SourceMainFramesV1.Point0699
import SourceMainFramesV1.Point0700
import SourceMainFramesV1.Point0701
import SourceMainFramesV1.Point0702
import SourceMainFramesV1.Point0703
import SourceMainFramesV1.PackOutput
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Block21
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (total : ProofBox) (i : ℕ) (lower : 672 ≤ i) (upper : i < 704) :
 ∃ base input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs base input c d := by
 interval_cases i
 · exact SourceMainFramesV1.pack_output (i:=672) (base:=SynergyHeightC.FullMainFrame.base total 672) (input:=SourceMainFramesV1.Point0672.input) (pair:=SourceMainFramesV1.Point0672.outputs) SourceMainFramesV1.Point0672.input_defined SourceMainFramesV1.Point0672.outputs_defined (SourceMainFramesV1.Point0672.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=673) (base:=SynergyHeightC.FullMainFrame.base total 673) (input:=SourceMainFramesV1.Point0673.input) (pair:=SourceMainFramesV1.Point0673.outputs) SourceMainFramesV1.Point0673.input_defined SourceMainFramesV1.Point0673.outputs_defined (SourceMainFramesV1.Point0673.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=674) (base:=SynergyHeightC.FullMainFrame.base total 674) (input:=SourceMainFramesV1.Point0674.input) (pair:=SourceMainFramesV1.Point0674.outputs) SourceMainFramesV1.Point0674.input_defined SourceMainFramesV1.Point0674.outputs_defined (SourceMainFramesV1.Point0674.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=675) (base:=SynergyHeightC.FullMainFrame.base total 675) (input:=SourceMainFramesV1.Point0675.input) (pair:=SourceMainFramesV1.Point0675.outputs) SourceMainFramesV1.Point0675.input_defined SourceMainFramesV1.Point0675.outputs_defined (SourceMainFramesV1.Point0675.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=676) (base:=SynergyHeightC.FullMainFrame.base total 676) (input:=SourceMainFramesV1.Point0676.input) (pair:=SourceMainFramesV1.Point0676.outputs) SourceMainFramesV1.Point0676.input_defined SourceMainFramesV1.Point0676.outputs_defined (SourceMainFramesV1.Point0676.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=677) (base:=SynergyHeightC.FullMainFrame.base total 677) (input:=SourceMainFramesV1.Point0677.input) (pair:=SourceMainFramesV1.Point0677.outputs) SourceMainFramesV1.Point0677.input_defined SourceMainFramesV1.Point0677.outputs_defined (SourceMainFramesV1.Point0677.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=678) (base:=SynergyHeightC.FullMainFrame.base total 678) (input:=SourceMainFramesV1.Point0678.input) (pair:=SourceMainFramesV1.Point0678.outputs) SourceMainFramesV1.Point0678.input_defined SourceMainFramesV1.Point0678.outputs_defined (SourceMainFramesV1.Point0678.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=679) (base:=SynergyHeightC.FullMainFrame.base total 679) (input:=SourceMainFramesV1.Point0679.input) (pair:=SourceMainFramesV1.Point0679.outputs) SourceMainFramesV1.Point0679.input_defined SourceMainFramesV1.Point0679.outputs_defined (SourceMainFramesV1.Point0679.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=680) (base:=SynergyHeightC.FullMainFrame.base total 680) (input:=SourceMainFramesV1.Point0680.input) (pair:=SourceMainFramesV1.Point0680.outputs) SourceMainFramesV1.Point0680.input_defined SourceMainFramesV1.Point0680.outputs_defined (SourceMainFramesV1.Point0680.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=681) (base:=SynergyHeightC.FullMainFrame.base total 681) (input:=SourceMainFramesV1.Point0681.input) (pair:=SourceMainFramesV1.Point0681.outputs) SourceMainFramesV1.Point0681.input_defined SourceMainFramesV1.Point0681.outputs_defined (SourceMainFramesV1.Point0681.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=682) (base:=SynergyHeightC.FullMainFrame.base total 682) (input:=SourceMainFramesV1.Point0682.input) (pair:=SourceMainFramesV1.Point0682.outputs) SourceMainFramesV1.Point0682.input_defined SourceMainFramesV1.Point0682.outputs_defined (SourceMainFramesV1.Point0682.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=683) (base:=SynergyHeightC.FullMainFrame.base total 683) (input:=SourceMainFramesV1.Point0683.input) (pair:=SourceMainFramesV1.Point0683.outputs) SourceMainFramesV1.Point0683.input_defined SourceMainFramesV1.Point0683.outputs_defined (SourceMainFramesV1.Point0683.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=684) (base:=SynergyHeightC.FullMainFrame.base total 684) (input:=SourceMainFramesV1.Point0684.input) (pair:=SourceMainFramesV1.Point0684.outputs) SourceMainFramesV1.Point0684.input_defined SourceMainFramesV1.Point0684.outputs_defined (SourceMainFramesV1.Point0684.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=685) (base:=SynergyHeightC.FullMainFrame.base total 685) (input:=SourceMainFramesV1.Point0685.input) (pair:=SourceMainFramesV1.Point0685.outputs) SourceMainFramesV1.Point0685.input_defined SourceMainFramesV1.Point0685.outputs_defined (SourceMainFramesV1.Point0685.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=686) (base:=SynergyHeightC.FullMainFrame.base total 686) (input:=SourceMainFramesV1.Point0686.input) (pair:=SourceMainFramesV1.Point0686.outputs) SourceMainFramesV1.Point0686.input_defined SourceMainFramesV1.Point0686.outputs_defined (SourceMainFramesV1.Point0686.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=687) (base:=SynergyHeightC.FullMainFrame.base total 687) (input:=SourceMainFramesV1.Point0687.input) (pair:=SourceMainFramesV1.Point0687.outputs) SourceMainFramesV1.Point0687.input_defined SourceMainFramesV1.Point0687.outputs_defined (SourceMainFramesV1.Point0687.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=688) (base:=SynergyHeightC.FullMainFrame.base total 688) (input:=SourceMainFramesV1.Point0688.input) (pair:=SourceMainFramesV1.Point0688.outputs) SourceMainFramesV1.Point0688.input_defined SourceMainFramesV1.Point0688.outputs_defined (SourceMainFramesV1.Point0688.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=689) (base:=SynergyHeightC.FullMainFrame.base total 689) (input:=SourceMainFramesV1.Point0689.input) (pair:=SourceMainFramesV1.Point0689.outputs) SourceMainFramesV1.Point0689.input_defined SourceMainFramesV1.Point0689.outputs_defined (SourceMainFramesV1.Point0689.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=690) (base:=SynergyHeightC.FullMainFrame.base total 690) (input:=SourceMainFramesV1.Point0690.input) (pair:=SourceMainFramesV1.Point0690.outputs) SourceMainFramesV1.Point0690.input_defined SourceMainFramesV1.Point0690.outputs_defined (SourceMainFramesV1.Point0690.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=691) (base:=SynergyHeightC.FullMainFrame.base total 691) (input:=SourceMainFramesV1.Point0691.input) (pair:=SourceMainFramesV1.Point0691.outputs) SourceMainFramesV1.Point0691.input_defined SourceMainFramesV1.Point0691.outputs_defined (SourceMainFramesV1.Point0691.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=692) (base:=SynergyHeightC.FullMainFrame.base total 692) (input:=SourceMainFramesV1.Point0692.input) (pair:=SourceMainFramesV1.Point0692.outputs) SourceMainFramesV1.Point0692.input_defined SourceMainFramesV1.Point0692.outputs_defined (SourceMainFramesV1.Point0692.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=693) (base:=SynergyHeightC.FullMainFrame.base total 693) (input:=SourceMainFramesV1.Point0693.input) (pair:=SourceMainFramesV1.Point0693.outputs) SourceMainFramesV1.Point0693.input_defined SourceMainFramesV1.Point0693.outputs_defined (SourceMainFramesV1.Point0693.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=694) (base:=SynergyHeightC.FullMainFrame.base total 694) (input:=SourceMainFramesV1.Point0694.input) (pair:=SourceMainFramesV1.Point0694.outputs) SourceMainFramesV1.Point0694.input_defined SourceMainFramesV1.Point0694.outputs_defined (SourceMainFramesV1.Point0694.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=695) (base:=SynergyHeightC.FullMainFrame.base total 695) (input:=SourceMainFramesV1.Point0695.input) (pair:=SourceMainFramesV1.Point0695.outputs) SourceMainFramesV1.Point0695.input_defined SourceMainFramesV1.Point0695.outputs_defined (SourceMainFramesV1.Point0695.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=696) (base:=SynergyHeightC.FullMainFrame.base total 696) (input:=SourceMainFramesV1.Point0696.input) (pair:=SourceMainFramesV1.Point0696.outputs) SourceMainFramesV1.Point0696.input_defined SourceMainFramesV1.Point0696.outputs_defined (SourceMainFramesV1.Point0696.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=697) (base:=SynergyHeightC.FullMainFrame.base total 697) (input:=SourceMainFramesV1.Point0697.input) (pair:=SourceMainFramesV1.Point0697.outputs) SourceMainFramesV1.Point0697.input_defined SourceMainFramesV1.Point0697.outputs_defined (SourceMainFramesV1.Point0697.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=698) (base:=SynergyHeightC.FullMainFrame.base total 698) (input:=SourceMainFramesV1.Point0698.input) (pair:=SourceMainFramesV1.Point0698.outputs) SourceMainFramesV1.Point0698.input_defined SourceMainFramesV1.Point0698.outputs_defined (SourceMainFramesV1.Point0698.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=699) (base:=SynergyHeightC.FullMainFrame.base total 699) (input:=SourceMainFramesV1.Point0699.input) (pair:=SourceMainFramesV1.Point0699.outputs) SourceMainFramesV1.Point0699.input_defined SourceMainFramesV1.Point0699.outputs_defined (SourceMainFramesV1.Point0699.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=700) (base:=SynergyHeightC.FullMainFrame.base total 700) (input:=SourceMainFramesV1.Point0700.input) (pair:=SourceMainFramesV1.Point0700.outputs) SourceMainFramesV1.Point0700.input_defined SourceMainFramesV1.Point0700.outputs_defined (SourceMainFramesV1.Point0700.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=701) (base:=SynergyHeightC.FullMainFrame.base total 701) (input:=SourceMainFramesV1.Point0701.input) (pair:=SourceMainFramesV1.Point0701.outputs) SourceMainFramesV1.Point0701.input_defined SourceMainFramesV1.Point0701.outputs_defined (SourceMainFramesV1.Point0701.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=702) (base:=SynergyHeightC.FullMainFrame.base total 702) (input:=SourceMainFramesV1.Point0702.input) (pair:=SourceMainFramesV1.Point0702.outputs) SourceMainFramesV1.Point0702.input_defined SourceMainFramesV1.Point0702.outputs_defined (SourceMainFramesV1.Point0702.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=703) (base:=SynergyHeightC.FullMainFrame.base total 703) (input:=SourceMainFramesV1.Point0703.input) (pair:=SourceMainFramesV1.Point0703.outputs) SourceMainFramesV1.Point0703.input_defined SourceMainFramesV1.Point0703.outputs_defined (SourceMainFramesV1.Point0703.source_outputs total)
end SourceMainFramesV1.Block21
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Block21.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
