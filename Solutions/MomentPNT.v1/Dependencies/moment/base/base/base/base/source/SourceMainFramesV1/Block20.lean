import SourceMainFramesV1.Point0640
import SourceMainFramesV1.Point0641
import SourceMainFramesV1.Point0642
import SourceMainFramesV1.Point0643
import SourceMainFramesV1.Point0644
import SourceMainFramesV1.Point0645
import SourceMainFramesV1.Point0646
import SourceMainFramesV1.Point0647
import SourceMainFramesV1.Point0648
import SourceMainFramesV1.Point0649
import SourceMainFramesV1.Point0650
import SourceMainFramesV1.Point0651
import SourceMainFramesV1.Point0652
import SourceMainFramesV1.Point0653
import SourceMainFramesV1.Point0654
import SourceMainFramesV1.Point0655
import SourceMainFramesV1.Point0656
import SourceMainFramesV1.Point0657
import SourceMainFramesV1.Point0658
import SourceMainFramesV1.Point0659
import SourceMainFramesV1.Point0660
import SourceMainFramesV1.Point0661
import SourceMainFramesV1.Point0662
import SourceMainFramesV1.Point0663
import SourceMainFramesV1.Point0664
import SourceMainFramesV1.Point0665
import SourceMainFramesV1.Point0666
import SourceMainFramesV1.Point0667
import SourceMainFramesV1.Point0668
import SourceMainFramesV1.Point0669
import SourceMainFramesV1.Point0670
import SourceMainFramesV1.Point0671
import SourceMainFramesV1.PackOutput
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Block20
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (total : ProofBox) (i : ℕ) (lower : 640 ≤ i) (upper : i < 672) :
 ∃ base input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs base input c d := by
 interval_cases i
 · exact SourceMainFramesV1.pack_output (i:=640) (base:=SynergyHeightC.FullMainFrame.base total 640) (input:=SourceMainFramesV1.Point0640.input) (pair:=SourceMainFramesV1.Point0640.outputs) SourceMainFramesV1.Point0640.input_defined SourceMainFramesV1.Point0640.outputs_defined (SourceMainFramesV1.Point0640.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=641) (base:=SynergyHeightC.FullMainFrame.base total 641) (input:=SourceMainFramesV1.Point0641.input) (pair:=SourceMainFramesV1.Point0641.outputs) SourceMainFramesV1.Point0641.input_defined SourceMainFramesV1.Point0641.outputs_defined (SourceMainFramesV1.Point0641.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=642) (base:=SynergyHeightC.FullMainFrame.base total 642) (input:=SourceMainFramesV1.Point0642.input) (pair:=SourceMainFramesV1.Point0642.outputs) SourceMainFramesV1.Point0642.input_defined SourceMainFramesV1.Point0642.outputs_defined (SourceMainFramesV1.Point0642.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=643) (base:=SynergyHeightC.FullMainFrame.base total 643) (input:=SourceMainFramesV1.Point0643.input) (pair:=SourceMainFramesV1.Point0643.outputs) SourceMainFramesV1.Point0643.input_defined SourceMainFramesV1.Point0643.outputs_defined (SourceMainFramesV1.Point0643.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=644) (base:=SynergyHeightC.FullMainFrame.base total 644) (input:=SourceMainFramesV1.Point0644.input) (pair:=SourceMainFramesV1.Point0644.outputs) SourceMainFramesV1.Point0644.input_defined SourceMainFramesV1.Point0644.outputs_defined (SourceMainFramesV1.Point0644.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=645) (base:=SynergyHeightC.FullMainFrame.base total 645) (input:=SourceMainFramesV1.Point0645.input) (pair:=SourceMainFramesV1.Point0645.outputs) SourceMainFramesV1.Point0645.input_defined SourceMainFramesV1.Point0645.outputs_defined (SourceMainFramesV1.Point0645.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=646) (base:=SynergyHeightC.FullMainFrame.base total 646) (input:=SourceMainFramesV1.Point0646.input) (pair:=SourceMainFramesV1.Point0646.outputs) SourceMainFramesV1.Point0646.input_defined SourceMainFramesV1.Point0646.outputs_defined (SourceMainFramesV1.Point0646.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=647) (base:=SynergyHeightC.FullMainFrame.base total 647) (input:=SourceMainFramesV1.Point0647.input) (pair:=SourceMainFramesV1.Point0647.outputs) SourceMainFramesV1.Point0647.input_defined SourceMainFramesV1.Point0647.outputs_defined (SourceMainFramesV1.Point0647.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=648) (base:=SynergyHeightC.FullMainFrame.base total 648) (input:=SourceMainFramesV1.Point0648.input) (pair:=SourceMainFramesV1.Point0648.outputs) SourceMainFramesV1.Point0648.input_defined SourceMainFramesV1.Point0648.outputs_defined (SourceMainFramesV1.Point0648.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=649) (base:=SynergyHeightC.FullMainFrame.base total 649) (input:=SourceMainFramesV1.Point0649.input) (pair:=SourceMainFramesV1.Point0649.outputs) SourceMainFramesV1.Point0649.input_defined SourceMainFramesV1.Point0649.outputs_defined (SourceMainFramesV1.Point0649.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=650) (base:=SynergyHeightC.FullMainFrame.base total 650) (input:=SourceMainFramesV1.Point0650.input) (pair:=SourceMainFramesV1.Point0650.outputs) SourceMainFramesV1.Point0650.input_defined SourceMainFramesV1.Point0650.outputs_defined (SourceMainFramesV1.Point0650.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=651) (base:=SynergyHeightC.FullMainFrame.base total 651) (input:=SourceMainFramesV1.Point0651.input) (pair:=SourceMainFramesV1.Point0651.outputs) SourceMainFramesV1.Point0651.input_defined SourceMainFramesV1.Point0651.outputs_defined (SourceMainFramesV1.Point0651.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=652) (base:=SynergyHeightC.FullMainFrame.base total 652) (input:=SourceMainFramesV1.Point0652.input) (pair:=SourceMainFramesV1.Point0652.outputs) SourceMainFramesV1.Point0652.input_defined SourceMainFramesV1.Point0652.outputs_defined (SourceMainFramesV1.Point0652.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=653) (base:=SynergyHeightC.FullMainFrame.base total 653) (input:=SourceMainFramesV1.Point0653.input) (pair:=SourceMainFramesV1.Point0653.outputs) SourceMainFramesV1.Point0653.input_defined SourceMainFramesV1.Point0653.outputs_defined (SourceMainFramesV1.Point0653.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=654) (base:=SynergyHeightC.FullMainFrame.base total 654) (input:=SourceMainFramesV1.Point0654.input) (pair:=SourceMainFramesV1.Point0654.outputs) SourceMainFramesV1.Point0654.input_defined SourceMainFramesV1.Point0654.outputs_defined (SourceMainFramesV1.Point0654.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=655) (base:=SynergyHeightC.FullMainFrame.base total 655) (input:=SourceMainFramesV1.Point0655.input) (pair:=SourceMainFramesV1.Point0655.outputs) SourceMainFramesV1.Point0655.input_defined SourceMainFramesV1.Point0655.outputs_defined (SourceMainFramesV1.Point0655.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=656) (base:=SynergyHeightC.FullMainFrame.base total 656) (input:=SourceMainFramesV1.Point0656.input) (pair:=SourceMainFramesV1.Point0656.outputs) SourceMainFramesV1.Point0656.input_defined SourceMainFramesV1.Point0656.outputs_defined (SourceMainFramesV1.Point0656.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=657) (base:=SynergyHeightC.FullMainFrame.base total 657) (input:=SourceMainFramesV1.Point0657.input) (pair:=SourceMainFramesV1.Point0657.outputs) SourceMainFramesV1.Point0657.input_defined SourceMainFramesV1.Point0657.outputs_defined (SourceMainFramesV1.Point0657.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=658) (base:=SynergyHeightC.FullMainFrame.base total 658) (input:=SourceMainFramesV1.Point0658.input) (pair:=SourceMainFramesV1.Point0658.outputs) SourceMainFramesV1.Point0658.input_defined SourceMainFramesV1.Point0658.outputs_defined (SourceMainFramesV1.Point0658.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=659) (base:=SynergyHeightC.FullMainFrame.base total 659) (input:=SourceMainFramesV1.Point0659.input) (pair:=SourceMainFramesV1.Point0659.outputs) SourceMainFramesV1.Point0659.input_defined SourceMainFramesV1.Point0659.outputs_defined (SourceMainFramesV1.Point0659.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=660) (base:=SynergyHeightC.FullMainFrame.base total 660) (input:=SourceMainFramesV1.Point0660.input) (pair:=SourceMainFramesV1.Point0660.outputs) SourceMainFramesV1.Point0660.input_defined SourceMainFramesV1.Point0660.outputs_defined (SourceMainFramesV1.Point0660.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=661) (base:=SynergyHeightC.FullMainFrame.base total 661) (input:=SourceMainFramesV1.Point0661.input) (pair:=SourceMainFramesV1.Point0661.outputs) SourceMainFramesV1.Point0661.input_defined SourceMainFramesV1.Point0661.outputs_defined (SourceMainFramesV1.Point0661.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=662) (base:=SynergyHeightC.FullMainFrame.base total 662) (input:=SourceMainFramesV1.Point0662.input) (pair:=SourceMainFramesV1.Point0662.outputs) SourceMainFramesV1.Point0662.input_defined SourceMainFramesV1.Point0662.outputs_defined (SourceMainFramesV1.Point0662.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=663) (base:=SynergyHeightC.FullMainFrame.base total 663) (input:=SourceMainFramesV1.Point0663.input) (pair:=SourceMainFramesV1.Point0663.outputs) SourceMainFramesV1.Point0663.input_defined SourceMainFramesV1.Point0663.outputs_defined (SourceMainFramesV1.Point0663.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=664) (base:=SynergyHeightC.FullMainFrame.base total 664) (input:=SourceMainFramesV1.Point0664.input) (pair:=SourceMainFramesV1.Point0664.outputs) SourceMainFramesV1.Point0664.input_defined SourceMainFramesV1.Point0664.outputs_defined (SourceMainFramesV1.Point0664.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=665) (base:=SynergyHeightC.FullMainFrame.base total 665) (input:=SourceMainFramesV1.Point0665.input) (pair:=SourceMainFramesV1.Point0665.outputs) SourceMainFramesV1.Point0665.input_defined SourceMainFramesV1.Point0665.outputs_defined (SourceMainFramesV1.Point0665.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=666) (base:=SynergyHeightC.FullMainFrame.base total 666) (input:=SourceMainFramesV1.Point0666.input) (pair:=SourceMainFramesV1.Point0666.outputs) SourceMainFramesV1.Point0666.input_defined SourceMainFramesV1.Point0666.outputs_defined (SourceMainFramesV1.Point0666.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=667) (base:=SynergyHeightC.FullMainFrame.base total 667) (input:=SourceMainFramesV1.Point0667.input) (pair:=SourceMainFramesV1.Point0667.outputs) SourceMainFramesV1.Point0667.input_defined SourceMainFramesV1.Point0667.outputs_defined (SourceMainFramesV1.Point0667.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=668) (base:=SynergyHeightC.FullMainFrame.base total 668) (input:=SourceMainFramesV1.Point0668.input) (pair:=SourceMainFramesV1.Point0668.outputs) SourceMainFramesV1.Point0668.input_defined SourceMainFramesV1.Point0668.outputs_defined (SourceMainFramesV1.Point0668.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=669) (base:=SynergyHeightC.FullMainFrame.base total 669) (input:=SourceMainFramesV1.Point0669.input) (pair:=SourceMainFramesV1.Point0669.outputs) SourceMainFramesV1.Point0669.input_defined SourceMainFramesV1.Point0669.outputs_defined (SourceMainFramesV1.Point0669.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=670) (base:=SynergyHeightC.FullMainFrame.base total 670) (input:=SourceMainFramesV1.Point0670.input) (pair:=SourceMainFramesV1.Point0670.outputs) SourceMainFramesV1.Point0670.input_defined SourceMainFramesV1.Point0670.outputs_defined (SourceMainFramesV1.Point0670.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=671) (base:=SynergyHeightC.FullMainFrame.base total 671) (input:=SourceMainFramesV1.Point0671.input) (pair:=SourceMainFramesV1.Point0671.outputs) SourceMainFramesV1.Point0671.input_defined SourceMainFramesV1.Point0671.outputs_defined (SourceMainFramesV1.Point0671.source_outputs total)
end SourceMainFramesV1.Block20
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Block20.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
