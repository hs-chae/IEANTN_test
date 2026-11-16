import SourceMainFramesV1.Point0512
import SourceMainFramesV1.Point0513
import SourceMainFramesV1.Point0514
import SourceMainFramesV1.Point0515
import SourceMainFramesV1.Point0516
import SourceMainFramesV1.Point0517
import SourceMainFramesV1.Point0518
import SourceMainFramesV1.Point0519
import SourceMainFramesV1.Point0520
import SourceMainFramesV1.Point0521
import SourceMainFramesV1.Point0522
import SourceMainFramesV1.Point0523
import SourceMainFramesV1.Point0524
import SourceMainFramesV1.Point0525
import SourceMainFramesV1.Point0526
import SourceMainFramesV1.Point0527
import SourceMainFramesV1.Point0528
import SourceMainFramesV1.Point0529
import SourceMainFramesV1.Point0530
import SourceMainFramesV1.Point0531
import SourceMainFramesV1.Point0532
import SourceMainFramesV1.Point0533
import SourceMainFramesV1.Point0534
import SourceMainFramesV1.Point0535
import SourceMainFramesV1.Point0536
import SourceMainFramesV1.Point0537
import SourceMainFramesV1.Point0538
import SourceMainFramesV1.Point0539
import SourceMainFramesV1.Point0540
import SourceMainFramesV1.Point0541
import SourceMainFramesV1.Point0542
import SourceMainFramesV1.Point0543
import SourceMainFramesV1.PackOutput
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Block16
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (total : ProofBox) (i : ℕ) (lower : 512 ≤ i) (upper : i < 544) :
 ∃ base input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs base input c d := by
 interval_cases i
 · exact SourceMainFramesV1.pack_output (i:=512) (base:=SynergyHeightC.FullMainFrame.base total 512) (input:=SourceMainFramesV1.Point0512.input) (pair:=SourceMainFramesV1.Point0512.outputs) SourceMainFramesV1.Point0512.input_defined SourceMainFramesV1.Point0512.outputs_defined (SourceMainFramesV1.Point0512.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=513) (base:=SynergyHeightC.FullMainFrame.base total 513) (input:=SourceMainFramesV1.Point0513.input) (pair:=SourceMainFramesV1.Point0513.outputs) SourceMainFramesV1.Point0513.input_defined SourceMainFramesV1.Point0513.outputs_defined (SourceMainFramesV1.Point0513.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=514) (base:=SynergyHeightC.FullMainFrame.base total 514) (input:=SourceMainFramesV1.Point0514.input) (pair:=SourceMainFramesV1.Point0514.outputs) SourceMainFramesV1.Point0514.input_defined SourceMainFramesV1.Point0514.outputs_defined (SourceMainFramesV1.Point0514.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=515) (base:=SynergyHeightC.FullMainFrame.base total 515) (input:=SourceMainFramesV1.Point0515.input) (pair:=SourceMainFramesV1.Point0515.outputs) SourceMainFramesV1.Point0515.input_defined SourceMainFramesV1.Point0515.outputs_defined (SourceMainFramesV1.Point0515.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=516) (base:=SynergyHeightC.FullMainFrame.base total 516) (input:=SourceMainFramesV1.Point0516.input) (pair:=SourceMainFramesV1.Point0516.outputs) SourceMainFramesV1.Point0516.input_defined SourceMainFramesV1.Point0516.outputs_defined (SourceMainFramesV1.Point0516.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=517) (base:=SynergyHeightC.FullMainFrame.base total 517) (input:=SourceMainFramesV1.Point0517.input) (pair:=SourceMainFramesV1.Point0517.outputs) SourceMainFramesV1.Point0517.input_defined SourceMainFramesV1.Point0517.outputs_defined (SourceMainFramesV1.Point0517.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=518) (base:=SynergyHeightC.FullMainFrame.base total 518) (input:=SourceMainFramesV1.Point0518.input) (pair:=SourceMainFramesV1.Point0518.outputs) SourceMainFramesV1.Point0518.input_defined SourceMainFramesV1.Point0518.outputs_defined (SourceMainFramesV1.Point0518.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=519) (base:=SynergyHeightC.FullMainFrame.base total 519) (input:=SourceMainFramesV1.Point0519.input) (pair:=SourceMainFramesV1.Point0519.outputs) SourceMainFramesV1.Point0519.input_defined SourceMainFramesV1.Point0519.outputs_defined (SourceMainFramesV1.Point0519.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=520) (base:=SynergyHeightC.FullMainFrame.base total 520) (input:=SourceMainFramesV1.Point0520.input) (pair:=SourceMainFramesV1.Point0520.outputs) SourceMainFramesV1.Point0520.input_defined SourceMainFramesV1.Point0520.outputs_defined (SourceMainFramesV1.Point0520.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=521) (base:=SynergyHeightC.FullMainFrame.base total 521) (input:=SourceMainFramesV1.Point0521.input) (pair:=SourceMainFramesV1.Point0521.outputs) SourceMainFramesV1.Point0521.input_defined SourceMainFramesV1.Point0521.outputs_defined (SourceMainFramesV1.Point0521.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=522) (base:=SynergyHeightC.FullMainFrame.base total 522) (input:=SourceMainFramesV1.Point0522.input) (pair:=SourceMainFramesV1.Point0522.outputs) SourceMainFramesV1.Point0522.input_defined SourceMainFramesV1.Point0522.outputs_defined (SourceMainFramesV1.Point0522.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=523) (base:=SynergyHeightC.FullMainFrame.base total 523) (input:=SourceMainFramesV1.Point0523.input) (pair:=SourceMainFramesV1.Point0523.outputs) SourceMainFramesV1.Point0523.input_defined SourceMainFramesV1.Point0523.outputs_defined (SourceMainFramesV1.Point0523.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=524) (base:=SynergyHeightC.FullMainFrame.base total 524) (input:=SourceMainFramesV1.Point0524.input) (pair:=SourceMainFramesV1.Point0524.outputs) SourceMainFramesV1.Point0524.input_defined SourceMainFramesV1.Point0524.outputs_defined (SourceMainFramesV1.Point0524.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=525) (base:=SynergyHeightC.FullMainFrame.base total 525) (input:=SourceMainFramesV1.Point0525.input) (pair:=SourceMainFramesV1.Point0525.outputs) SourceMainFramesV1.Point0525.input_defined SourceMainFramesV1.Point0525.outputs_defined (SourceMainFramesV1.Point0525.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=526) (base:=SynergyHeightC.FullMainFrame.base total 526) (input:=SourceMainFramesV1.Point0526.input) (pair:=SourceMainFramesV1.Point0526.outputs) SourceMainFramesV1.Point0526.input_defined SourceMainFramesV1.Point0526.outputs_defined (SourceMainFramesV1.Point0526.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=527) (base:=SynergyHeightC.FullMainFrame.base total 527) (input:=SourceMainFramesV1.Point0527.input) (pair:=SourceMainFramesV1.Point0527.outputs) SourceMainFramesV1.Point0527.input_defined SourceMainFramesV1.Point0527.outputs_defined (SourceMainFramesV1.Point0527.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=528) (base:=SynergyHeightC.FullMainFrame.base total 528) (input:=SourceMainFramesV1.Point0528.input) (pair:=SourceMainFramesV1.Point0528.outputs) SourceMainFramesV1.Point0528.input_defined SourceMainFramesV1.Point0528.outputs_defined (SourceMainFramesV1.Point0528.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=529) (base:=SynergyHeightC.FullMainFrame.base total 529) (input:=SourceMainFramesV1.Point0529.input) (pair:=SourceMainFramesV1.Point0529.outputs) SourceMainFramesV1.Point0529.input_defined SourceMainFramesV1.Point0529.outputs_defined (SourceMainFramesV1.Point0529.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=530) (base:=SynergyHeightC.FullMainFrame.base total 530) (input:=SourceMainFramesV1.Point0530.input) (pair:=SourceMainFramesV1.Point0530.outputs) SourceMainFramesV1.Point0530.input_defined SourceMainFramesV1.Point0530.outputs_defined (SourceMainFramesV1.Point0530.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=531) (base:=SynergyHeightC.FullMainFrame.base total 531) (input:=SourceMainFramesV1.Point0531.input) (pair:=SourceMainFramesV1.Point0531.outputs) SourceMainFramesV1.Point0531.input_defined SourceMainFramesV1.Point0531.outputs_defined (SourceMainFramesV1.Point0531.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=532) (base:=SynergyHeightC.FullMainFrame.base total 532) (input:=SourceMainFramesV1.Point0532.input) (pair:=SourceMainFramesV1.Point0532.outputs) SourceMainFramesV1.Point0532.input_defined SourceMainFramesV1.Point0532.outputs_defined (SourceMainFramesV1.Point0532.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=533) (base:=SynergyHeightC.FullMainFrame.base total 533) (input:=SourceMainFramesV1.Point0533.input) (pair:=SourceMainFramesV1.Point0533.outputs) SourceMainFramesV1.Point0533.input_defined SourceMainFramesV1.Point0533.outputs_defined (SourceMainFramesV1.Point0533.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=534) (base:=SynergyHeightC.FullMainFrame.base total 534) (input:=SourceMainFramesV1.Point0534.input) (pair:=SourceMainFramesV1.Point0534.outputs) SourceMainFramesV1.Point0534.input_defined SourceMainFramesV1.Point0534.outputs_defined (SourceMainFramesV1.Point0534.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=535) (base:=SynergyHeightC.FullMainFrame.base total 535) (input:=SourceMainFramesV1.Point0535.input) (pair:=SourceMainFramesV1.Point0535.outputs) SourceMainFramesV1.Point0535.input_defined SourceMainFramesV1.Point0535.outputs_defined (SourceMainFramesV1.Point0535.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=536) (base:=SynergyHeightC.FullMainFrame.base total 536) (input:=SourceMainFramesV1.Point0536.input) (pair:=SourceMainFramesV1.Point0536.outputs) SourceMainFramesV1.Point0536.input_defined SourceMainFramesV1.Point0536.outputs_defined (SourceMainFramesV1.Point0536.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=537) (base:=SynergyHeightC.FullMainFrame.base total 537) (input:=SourceMainFramesV1.Point0537.input) (pair:=SourceMainFramesV1.Point0537.outputs) SourceMainFramesV1.Point0537.input_defined SourceMainFramesV1.Point0537.outputs_defined (SourceMainFramesV1.Point0537.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=538) (base:=SynergyHeightC.FullMainFrame.base total 538) (input:=SourceMainFramesV1.Point0538.input) (pair:=SourceMainFramesV1.Point0538.outputs) SourceMainFramesV1.Point0538.input_defined SourceMainFramesV1.Point0538.outputs_defined (SourceMainFramesV1.Point0538.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=539) (base:=SynergyHeightC.FullMainFrame.base total 539) (input:=SourceMainFramesV1.Point0539.input) (pair:=SourceMainFramesV1.Point0539.outputs) SourceMainFramesV1.Point0539.input_defined SourceMainFramesV1.Point0539.outputs_defined (SourceMainFramesV1.Point0539.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=540) (base:=SynergyHeightC.FullMainFrame.base total 540) (input:=SourceMainFramesV1.Point0540.input) (pair:=SourceMainFramesV1.Point0540.outputs) SourceMainFramesV1.Point0540.input_defined SourceMainFramesV1.Point0540.outputs_defined (SourceMainFramesV1.Point0540.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=541) (base:=SynergyHeightC.FullMainFrame.base total 541) (input:=SourceMainFramesV1.Point0541.input) (pair:=SourceMainFramesV1.Point0541.outputs) SourceMainFramesV1.Point0541.input_defined SourceMainFramesV1.Point0541.outputs_defined (SourceMainFramesV1.Point0541.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=542) (base:=SynergyHeightC.FullMainFrame.base total 542) (input:=SourceMainFramesV1.Point0542.input) (pair:=SourceMainFramesV1.Point0542.outputs) SourceMainFramesV1.Point0542.input_defined SourceMainFramesV1.Point0542.outputs_defined (SourceMainFramesV1.Point0542.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=543) (base:=SynergyHeightC.FullMainFrame.base total 543) (input:=SourceMainFramesV1.Point0543.input) (pair:=SourceMainFramesV1.Point0543.outputs) SourceMainFramesV1.Point0543.input_defined SourceMainFramesV1.Point0543.outputs_defined (SourceMainFramesV1.Point0543.source_outputs total)
end SourceMainFramesV1.Block16
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Block16.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
