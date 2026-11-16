import SourceMainFramesV1.Point0544
import SourceMainFramesV1.Point0545
import SourceMainFramesV1.Point0546
import SourceMainFramesV1.Point0547
import SourceMainFramesV1.Point0548
import SourceMainFramesV1.Point0549
import SourceMainFramesV1.Point0550
import SourceMainFramesV1.Point0551
import SourceMainFramesV1.Point0552
import SourceMainFramesV1.Point0553
import SourceMainFramesV1.Point0554
import SourceMainFramesV1.Point0555
import SourceMainFramesV1.Point0556
import SourceMainFramesV1.Point0557
import SourceMainFramesV1.Point0558
import SourceMainFramesV1.Point0559
import SourceMainFramesV1.Point0560
import SourceMainFramesV1.Point0561
import SourceMainFramesV1.Point0562
import SourceMainFramesV1.Point0563
import SourceMainFramesV1.Point0564
import SourceMainFramesV1.Point0565
import SourceMainFramesV1.Point0566
import SourceMainFramesV1.Point0567
import SourceMainFramesV1.Point0568
import SourceMainFramesV1.Point0569
import SourceMainFramesV1.Point0570
import SourceMainFramesV1.Point0571
import SourceMainFramesV1.Point0572
import SourceMainFramesV1.Point0573
import SourceMainFramesV1.Point0574
import SourceMainFramesV1.Point0575
import SourceMainFramesV1.PackOutput
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Block17
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (total : ProofBox) (i : ℕ) (lower : 544 ≤ i) (upper : i < 576) :
 ∃ base input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs base input c d := by
 interval_cases i
 · exact SourceMainFramesV1.pack_output (i:=544) (base:=SynergyHeightC.FullMainFrame.base total 544) (input:=SourceMainFramesV1.Point0544.input) (pair:=SourceMainFramesV1.Point0544.outputs) SourceMainFramesV1.Point0544.input_defined SourceMainFramesV1.Point0544.outputs_defined (SourceMainFramesV1.Point0544.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=545) (base:=SynergyHeightC.FullMainFrame.base total 545) (input:=SourceMainFramesV1.Point0545.input) (pair:=SourceMainFramesV1.Point0545.outputs) SourceMainFramesV1.Point0545.input_defined SourceMainFramesV1.Point0545.outputs_defined (SourceMainFramesV1.Point0545.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=546) (base:=SynergyHeightC.FullMainFrame.base total 546) (input:=SourceMainFramesV1.Point0546.input) (pair:=SourceMainFramesV1.Point0546.outputs) SourceMainFramesV1.Point0546.input_defined SourceMainFramesV1.Point0546.outputs_defined (SourceMainFramesV1.Point0546.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=547) (base:=SynergyHeightC.FullMainFrame.base total 547) (input:=SourceMainFramesV1.Point0547.input) (pair:=SourceMainFramesV1.Point0547.outputs) SourceMainFramesV1.Point0547.input_defined SourceMainFramesV1.Point0547.outputs_defined (SourceMainFramesV1.Point0547.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=548) (base:=SynergyHeightC.FullMainFrame.base total 548) (input:=SourceMainFramesV1.Point0548.input) (pair:=SourceMainFramesV1.Point0548.outputs) SourceMainFramesV1.Point0548.input_defined SourceMainFramesV1.Point0548.outputs_defined (SourceMainFramesV1.Point0548.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=549) (base:=SynergyHeightC.FullMainFrame.base total 549) (input:=SourceMainFramesV1.Point0549.input) (pair:=SourceMainFramesV1.Point0549.outputs) SourceMainFramesV1.Point0549.input_defined SourceMainFramesV1.Point0549.outputs_defined (SourceMainFramesV1.Point0549.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=550) (base:=SynergyHeightC.FullMainFrame.base total 550) (input:=SourceMainFramesV1.Point0550.input) (pair:=SourceMainFramesV1.Point0550.outputs) SourceMainFramesV1.Point0550.input_defined SourceMainFramesV1.Point0550.outputs_defined (SourceMainFramesV1.Point0550.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=551) (base:=SynergyHeightC.FullMainFrame.base total 551) (input:=SourceMainFramesV1.Point0551.input) (pair:=SourceMainFramesV1.Point0551.outputs) SourceMainFramesV1.Point0551.input_defined SourceMainFramesV1.Point0551.outputs_defined (SourceMainFramesV1.Point0551.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=552) (base:=SynergyHeightC.FullMainFrame.base total 552) (input:=SourceMainFramesV1.Point0552.input) (pair:=SourceMainFramesV1.Point0552.outputs) SourceMainFramesV1.Point0552.input_defined SourceMainFramesV1.Point0552.outputs_defined (SourceMainFramesV1.Point0552.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=553) (base:=SynergyHeightC.FullMainFrame.base total 553) (input:=SourceMainFramesV1.Point0553.input) (pair:=SourceMainFramesV1.Point0553.outputs) SourceMainFramesV1.Point0553.input_defined SourceMainFramesV1.Point0553.outputs_defined (SourceMainFramesV1.Point0553.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=554) (base:=SynergyHeightC.FullMainFrame.base total 554) (input:=SourceMainFramesV1.Point0554.input) (pair:=SourceMainFramesV1.Point0554.outputs) SourceMainFramesV1.Point0554.input_defined SourceMainFramesV1.Point0554.outputs_defined (SourceMainFramesV1.Point0554.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=555) (base:=SynergyHeightC.FullMainFrame.base total 555) (input:=SourceMainFramesV1.Point0555.input) (pair:=SourceMainFramesV1.Point0555.outputs) SourceMainFramesV1.Point0555.input_defined SourceMainFramesV1.Point0555.outputs_defined (SourceMainFramesV1.Point0555.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=556) (base:=SynergyHeightC.FullMainFrame.base total 556) (input:=SourceMainFramesV1.Point0556.input) (pair:=SourceMainFramesV1.Point0556.outputs) SourceMainFramesV1.Point0556.input_defined SourceMainFramesV1.Point0556.outputs_defined (SourceMainFramesV1.Point0556.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=557) (base:=SynergyHeightC.FullMainFrame.base total 557) (input:=SourceMainFramesV1.Point0557.input) (pair:=SourceMainFramesV1.Point0557.outputs) SourceMainFramesV1.Point0557.input_defined SourceMainFramesV1.Point0557.outputs_defined (SourceMainFramesV1.Point0557.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=558) (base:=SynergyHeightC.FullMainFrame.base total 558) (input:=SourceMainFramesV1.Point0558.input) (pair:=SourceMainFramesV1.Point0558.outputs) SourceMainFramesV1.Point0558.input_defined SourceMainFramesV1.Point0558.outputs_defined (SourceMainFramesV1.Point0558.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=559) (base:=SynergyHeightC.FullMainFrame.base total 559) (input:=SourceMainFramesV1.Point0559.input) (pair:=SourceMainFramesV1.Point0559.outputs) SourceMainFramesV1.Point0559.input_defined SourceMainFramesV1.Point0559.outputs_defined (SourceMainFramesV1.Point0559.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=560) (base:=SynergyHeightC.FullMainFrame.base total 560) (input:=SourceMainFramesV1.Point0560.input) (pair:=SourceMainFramesV1.Point0560.outputs) SourceMainFramesV1.Point0560.input_defined SourceMainFramesV1.Point0560.outputs_defined (SourceMainFramesV1.Point0560.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=561) (base:=SynergyHeightC.FullMainFrame.base total 561) (input:=SourceMainFramesV1.Point0561.input) (pair:=SourceMainFramesV1.Point0561.outputs) SourceMainFramesV1.Point0561.input_defined SourceMainFramesV1.Point0561.outputs_defined (SourceMainFramesV1.Point0561.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=562) (base:=SynergyHeightC.FullMainFrame.base total 562) (input:=SourceMainFramesV1.Point0562.input) (pair:=SourceMainFramesV1.Point0562.outputs) SourceMainFramesV1.Point0562.input_defined SourceMainFramesV1.Point0562.outputs_defined (SourceMainFramesV1.Point0562.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=563) (base:=SynergyHeightC.FullMainFrame.base total 563) (input:=SourceMainFramesV1.Point0563.input) (pair:=SourceMainFramesV1.Point0563.outputs) SourceMainFramesV1.Point0563.input_defined SourceMainFramesV1.Point0563.outputs_defined (SourceMainFramesV1.Point0563.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=564) (base:=SynergyHeightC.FullMainFrame.base total 564) (input:=SourceMainFramesV1.Point0564.input) (pair:=SourceMainFramesV1.Point0564.outputs) SourceMainFramesV1.Point0564.input_defined SourceMainFramesV1.Point0564.outputs_defined (SourceMainFramesV1.Point0564.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=565) (base:=SynergyHeightC.FullMainFrame.base total 565) (input:=SourceMainFramesV1.Point0565.input) (pair:=SourceMainFramesV1.Point0565.outputs) SourceMainFramesV1.Point0565.input_defined SourceMainFramesV1.Point0565.outputs_defined (SourceMainFramesV1.Point0565.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=566) (base:=SynergyHeightC.FullMainFrame.base total 566) (input:=SourceMainFramesV1.Point0566.input) (pair:=SourceMainFramesV1.Point0566.outputs) SourceMainFramesV1.Point0566.input_defined SourceMainFramesV1.Point0566.outputs_defined (SourceMainFramesV1.Point0566.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=567) (base:=SynergyHeightC.FullMainFrame.base total 567) (input:=SourceMainFramesV1.Point0567.input) (pair:=SourceMainFramesV1.Point0567.outputs) SourceMainFramesV1.Point0567.input_defined SourceMainFramesV1.Point0567.outputs_defined (SourceMainFramesV1.Point0567.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=568) (base:=SynergyHeightC.FullMainFrame.base total 568) (input:=SourceMainFramesV1.Point0568.input) (pair:=SourceMainFramesV1.Point0568.outputs) SourceMainFramesV1.Point0568.input_defined SourceMainFramesV1.Point0568.outputs_defined (SourceMainFramesV1.Point0568.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=569) (base:=SynergyHeightC.FullMainFrame.base total 569) (input:=SourceMainFramesV1.Point0569.input) (pair:=SourceMainFramesV1.Point0569.outputs) SourceMainFramesV1.Point0569.input_defined SourceMainFramesV1.Point0569.outputs_defined (SourceMainFramesV1.Point0569.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=570) (base:=SynergyHeightC.FullMainFrame.base total 570) (input:=SourceMainFramesV1.Point0570.input) (pair:=SourceMainFramesV1.Point0570.outputs) SourceMainFramesV1.Point0570.input_defined SourceMainFramesV1.Point0570.outputs_defined (SourceMainFramesV1.Point0570.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=571) (base:=SynergyHeightC.FullMainFrame.base total 571) (input:=SourceMainFramesV1.Point0571.input) (pair:=SourceMainFramesV1.Point0571.outputs) SourceMainFramesV1.Point0571.input_defined SourceMainFramesV1.Point0571.outputs_defined (SourceMainFramesV1.Point0571.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=572) (base:=SynergyHeightC.FullMainFrame.base total 572) (input:=SourceMainFramesV1.Point0572.input) (pair:=SourceMainFramesV1.Point0572.outputs) SourceMainFramesV1.Point0572.input_defined SourceMainFramesV1.Point0572.outputs_defined (SourceMainFramesV1.Point0572.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=573) (base:=SynergyHeightC.FullMainFrame.base total 573) (input:=SourceMainFramesV1.Point0573.input) (pair:=SourceMainFramesV1.Point0573.outputs) SourceMainFramesV1.Point0573.input_defined SourceMainFramesV1.Point0573.outputs_defined (SourceMainFramesV1.Point0573.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=574) (base:=SynergyHeightC.FullMainFrame.base total 574) (input:=SourceMainFramesV1.Point0574.input) (pair:=SourceMainFramesV1.Point0574.outputs) SourceMainFramesV1.Point0574.input_defined SourceMainFramesV1.Point0574.outputs_defined (SourceMainFramesV1.Point0574.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=575) (base:=SynergyHeightC.FullMainFrame.base total 575) (input:=SourceMainFramesV1.Point0575.input) (pair:=SourceMainFramesV1.Point0575.outputs) SourceMainFramesV1.Point0575.input_defined SourceMainFramesV1.Point0575.outputs_defined (SourceMainFramesV1.Point0575.source_outputs total)
end SourceMainFramesV1.Block17
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Block17.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
