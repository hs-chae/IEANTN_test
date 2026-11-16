import SourceMainFramesV1.Point0576
import SourceMainFramesV1.Point0577
import SourceMainFramesV1.Point0578
import SourceMainFramesV1.Point0579
import SourceMainFramesV1.Point0580
import SourceMainFramesV1.Point0581
import SourceMainFramesV1.Point0582
import SourceMainFramesV1.Point0583
import SourceMainFramesV1.Point0584
import SourceMainFramesV1.Point0585
import SourceMainFramesV1.Point0586
import SourceMainFramesV1.Point0587
import SourceMainFramesV1.Point0588
import SourceMainFramesV1.Point0589
import SourceMainFramesV1.Point0590
import SourceMainFramesV1.Point0591
import SourceMainFramesV1.Point0592
import SourceMainFramesV1.Point0593
import SourceMainFramesV1.Point0594
import SourceMainFramesV1.Point0595
import SourceMainFramesV1.Point0596
import SourceMainFramesV1.Point0597
import SourceMainFramesV1.Point0598
import SourceMainFramesV1.Point0599
import SourceMainFramesV1.Point0600
import SourceMainFramesV1.Point0601
import SourceMainFramesV1.Point0602
import SourceMainFramesV1.Point0603
import SourceMainFramesV1.Point0604
import SourceMainFramesV1.Point0605
import SourceMainFramesV1.Point0606
import SourceMainFramesV1.Point0607
import SourceMainFramesV1.PackOutput
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Block18
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (total : ProofBox) (i : ℕ) (lower : 576 ≤ i) (upper : i < 608) :
 ∃ base input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs base input c d := by
 interval_cases i
 · exact SourceMainFramesV1.pack_output (i:=576) (base:=SynergyHeightC.FullMainFrame.base total 576) (input:=SourceMainFramesV1.Point0576.input) (pair:=SourceMainFramesV1.Point0576.outputs) SourceMainFramesV1.Point0576.input_defined SourceMainFramesV1.Point0576.outputs_defined (SourceMainFramesV1.Point0576.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=577) (base:=SynergyHeightC.FullMainFrame.base total 577) (input:=SourceMainFramesV1.Point0577.input) (pair:=SourceMainFramesV1.Point0577.outputs) SourceMainFramesV1.Point0577.input_defined SourceMainFramesV1.Point0577.outputs_defined (SourceMainFramesV1.Point0577.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=578) (base:=SynergyHeightC.FullMainFrame.base total 578) (input:=SourceMainFramesV1.Point0578.input) (pair:=SourceMainFramesV1.Point0578.outputs) SourceMainFramesV1.Point0578.input_defined SourceMainFramesV1.Point0578.outputs_defined (SourceMainFramesV1.Point0578.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=579) (base:=SynergyHeightC.FullMainFrame.base total 579) (input:=SourceMainFramesV1.Point0579.input) (pair:=SourceMainFramesV1.Point0579.outputs) SourceMainFramesV1.Point0579.input_defined SourceMainFramesV1.Point0579.outputs_defined (SourceMainFramesV1.Point0579.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=580) (base:=SynergyHeightC.FullMainFrame.base total 580) (input:=SourceMainFramesV1.Point0580.input) (pair:=SourceMainFramesV1.Point0580.outputs) SourceMainFramesV1.Point0580.input_defined SourceMainFramesV1.Point0580.outputs_defined (SourceMainFramesV1.Point0580.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=581) (base:=SynergyHeightC.FullMainFrame.base total 581) (input:=SourceMainFramesV1.Point0581.input) (pair:=SourceMainFramesV1.Point0581.outputs) SourceMainFramesV1.Point0581.input_defined SourceMainFramesV1.Point0581.outputs_defined (SourceMainFramesV1.Point0581.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=582) (base:=SynergyHeightC.FullMainFrame.base total 582) (input:=SourceMainFramesV1.Point0582.input) (pair:=SourceMainFramesV1.Point0582.outputs) SourceMainFramesV1.Point0582.input_defined SourceMainFramesV1.Point0582.outputs_defined (SourceMainFramesV1.Point0582.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=583) (base:=SynergyHeightC.FullMainFrame.base total 583) (input:=SourceMainFramesV1.Point0583.input) (pair:=SourceMainFramesV1.Point0583.outputs) SourceMainFramesV1.Point0583.input_defined SourceMainFramesV1.Point0583.outputs_defined (SourceMainFramesV1.Point0583.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=584) (base:=SynergyHeightC.FullMainFrame.base total 584) (input:=SourceMainFramesV1.Point0584.input) (pair:=SourceMainFramesV1.Point0584.outputs) SourceMainFramesV1.Point0584.input_defined SourceMainFramesV1.Point0584.outputs_defined (SourceMainFramesV1.Point0584.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=585) (base:=SynergyHeightC.FullMainFrame.base total 585) (input:=SourceMainFramesV1.Point0585.input) (pair:=SourceMainFramesV1.Point0585.outputs) SourceMainFramesV1.Point0585.input_defined SourceMainFramesV1.Point0585.outputs_defined (SourceMainFramesV1.Point0585.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=586) (base:=SynergyHeightC.FullMainFrame.base total 586) (input:=SourceMainFramesV1.Point0586.input) (pair:=SourceMainFramesV1.Point0586.outputs) SourceMainFramesV1.Point0586.input_defined SourceMainFramesV1.Point0586.outputs_defined (SourceMainFramesV1.Point0586.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=587) (base:=SynergyHeightC.FullMainFrame.base total 587) (input:=SourceMainFramesV1.Point0587.input) (pair:=SourceMainFramesV1.Point0587.outputs) SourceMainFramesV1.Point0587.input_defined SourceMainFramesV1.Point0587.outputs_defined (SourceMainFramesV1.Point0587.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=588) (base:=SynergyHeightC.FullMainFrame.base total 588) (input:=SourceMainFramesV1.Point0588.input) (pair:=SourceMainFramesV1.Point0588.outputs) SourceMainFramesV1.Point0588.input_defined SourceMainFramesV1.Point0588.outputs_defined (SourceMainFramesV1.Point0588.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=589) (base:=SynergyHeightC.FullMainFrame.base total 589) (input:=SourceMainFramesV1.Point0589.input) (pair:=SourceMainFramesV1.Point0589.outputs) SourceMainFramesV1.Point0589.input_defined SourceMainFramesV1.Point0589.outputs_defined (SourceMainFramesV1.Point0589.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=590) (base:=SynergyHeightC.FullMainFrame.base total 590) (input:=SourceMainFramesV1.Point0590.input) (pair:=SourceMainFramesV1.Point0590.outputs) SourceMainFramesV1.Point0590.input_defined SourceMainFramesV1.Point0590.outputs_defined (SourceMainFramesV1.Point0590.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=591) (base:=SynergyHeightC.FullMainFrame.base total 591) (input:=SourceMainFramesV1.Point0591.input) (pair:=SourceMainFramesV1.Point0591.outputs) SourceMainFramesV1.Point0591.input_defined SourceMainFramesV1.Point0591.outputs_defined (SourceMainFramesV1.Point0591.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=592) (base:=SynergyHeightC.FullMainFrame.base total 592) (input:=SourceMainFramesV1.Point0592.input) (pair:=SourceMainFramesV1.Point0592.outputs) SourceMainFramesV1.Point0592.input_defined SourceMainFramesV1.Point0592.outputs_defined (SourceMainFramesV1.Point0592.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=593) (base:=SynergyHeightC.FullMainFrame.base total 593) (input:=SourceMainFramesV1.Point0593.input) (pair:=SourceMainFramesV1.Point0593.outputs) SourceMainFramesV1.Point0593.input_defined SourceMainFramesV1.Point0593.outputs_defined (SourceMainFramesV1.Point0593.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=594) (base:=SynergyHeightC.FullMainFrame.base total 594) (input:=SourceMainFramesV1.Point0594.input) (pair:=SourceMainFramesV1.Point0594.outputs) SourceMainFramesV1.Point0594.input_defined SourceMainFramesV1.Point0594.outputs_defined (SourceMainFramesV1.Point0594.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=595) (base:=SynergyHeightC.FullMainFrame.base total 595) (input:=SourceMainFramesV1.Point0595.input) (pair:=SourceMainFramesV1.Point0595.outputs) SourceMainFramesV1.Point0595.input_defined SourceMainFramesV1.Point0595.outputs_defined (SourceMainFramesV1.Point0595.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=596) (base:=SynergyHeightC.FullMainFrame.base total 596) (input:=SourceMainFramesV1.Point0596.input) (pair:=SourceMainFramesV1.Point0596.outputs) SourceMainFramesV1.Point0596.input_defined SourceMainFramesV1.Point0596.outputs_defined (SourceMainFramesV1.Point0596.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=597) (base:=SynergyHeightC.FullMainFrame.base total 597) (input:=SourceMainFramesV1.Point0597.input) (pair:=SourceMainFramesV1.Point0597.outputs) SourceMainFramesV1.Point0597.input_defined SourceMainFramesV1.Point0597.outputs_defined (SourceMainFramesV1.Point0597.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=598) (base:=SynergyHeightC.FullMainFrame.base total 598) (input:=SourceMainFramesV1.Point0598.input) (pair:=SourceMainFramesV1.Point0598.outputs) SourceMainFramesV1.Point0598.input_defined SourceMainFramesV1.Point0598.outputs_defined (SourceMainFramesV1.Point0598.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=599) (base:=SynergyHeightC.FullMainFrame.base total 599) (input:=SourceMainFramesV1.Point0599.input) (pair:=SourceMainFramesV1.Point0599.outputs) SourceMainFramesV1.Point0599.input_defined SourceMainFramesV1.Point0599.outputs_defined (SourceMainFramesV1.Point0599.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=600) (base:=SynergyHeightC.FullMainFrame.base total 600) (input:=SourceMainFramesV1.Point0600.input) (pair:=SourceMainFramesV1.Point0600.outputs) SourceMainFramesV1.Point0600.input_defined SourceMainFramesV1.Point0600.outputs_defined (SourceMainFramesV1.Point0600.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=601) (base:=SynergyHeightC.FullMainFrame.base total 601) (input:=SourceMainFramesV1.Point0601.input) (pair:=SourceMainFramesV1.Point0601.outputs) SourceMainFramesV1.Point0601.input_defined SourceMainFramesV1.Point0601.outputs_defined (SourceMainFramesV1.Point0601.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=602) (base:=SynergyHeightC.FullMainFrame.base total 602) (input:=SourceMainFramesV1.Point0602.input) (pair:=SourceMainFramesV1.Point0602.outputs) SourceMainFramesV1.Point0602.input_defined SourceMainFramesV1.Point0602.outputs_defined (SourceMainFramesV1.Point0602.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=603) (base:=SynergyHeightC.FullMainFrame.base total 603) (input:=SourceMainFramesV1.Point0603.input) (pair:=SourceMainFramesV1.Point0603.outputs) SourceMainFramesV1.Point0603.input_defined SourceMainFramesV1.Point0603.outputs_defined (SourceMainFramesV1.Point0603.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=604) (base:=SynergyHeightC.FullMainFrame.base total 604) (input:=SourceMainFramesV1.Point0604.input) (pair:=SourceMainFramesV1.Point0604.outputs) SourceMainFramesV1.Point0604.input_defined SourceMainFramesV1.Point0604.outputs_defined (SourceMainFramesV1.Point0604.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=605) (base:=SynergyHeightC.FullMainFrame.base total 605) (input:=SourceMainFramesV1.Point0605.input) (pair:=SourceMainFramesV1.Point0605.outputs) SourceMainFramesV1.Point0605.input_defined SourceMainFramesV1.Point0605.outputs_defined (SourceMainFramesV1.Point0605.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=606) (base:=SynergyHeightC.FullMainFrame.base total 606) (input:=SourceMainFramesV1.Point0606.input) (pair:=SourceMainFramesV1.Point0606.outputs) SourceMainFramesV1.Point0606.input_defined SourceMainFramesV1.Point0606.outputs_defined (SourceMainFramesV1.Point0606.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=607) (base:=SynergyHeightC.FullMainFrame.base total 607) (input:=SourceMainFramesV1.Point0607.input) (pair:=SourceMainFramesV1.Point0607.outputs) SourceMainFramesV1.Point0607.input_defined SourceMainFramesV1.Point0607.outputs_defined (SourceMainFramesV1.Point0607.source_outputs total)
end SourceMainFramesV1.Block18
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Block18.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
