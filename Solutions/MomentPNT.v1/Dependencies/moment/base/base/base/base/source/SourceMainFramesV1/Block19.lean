import SourceMainFramesV1.Point0608
import SourceMainFramesV1.Point0609
import SourceMainFramesV1.Point0610
import SourceMainFramesV1.Point0611
import SourceMainFramesV1.Point0612
import SourceMainFramesV1.Point0613
import SourceMainFramesV1.Point0614
import SourceMainFramesV1.Point0615
import SourceMainFramesV1.Point0616
import SourceMainFramesV1.Point0617
import SourceMainFramesV1.Point0618
import SourceMainFramesV1.Point0619
import SourceMainFramesV1.Point0620
import SourceMainFramesV1.Point0621
import SourceMainFramesV1.Point0622
import SourceMainFramesV1.Point0623
import SourceMainFramesV1.Point0624
import SourceMainFramesV1.Point0625
import SourceMainFramesV1.Point0626
import SourceMainFramesV1.Point0627
import SourceMainFramesV1.Point0628
import SourceMainFramesV1.Point0629
import SourceMainFramesV1.Point0630
import SourceMainFramesV1.Point0631
import SourceMainFramesV1.Point0632
import SourceMainFramesV1.Point0633
import SourceMainFramesV1.Point0634
import SourceMainFramesV1.Point0635
import SourceMainFramesV1.Point0636
import SourceMainFramesV1.Point0637
import SourceMainFramesV1.Point0638
import SourceMainFramesV1.Point0639
import SourceMainFramesV1.PackOutput
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Block19
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (total : ProofBox) (i : ℕ) (lower : 608 ≤ i) (upper : i < 640) :
 ∃ base input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs base input c d := by
 interval_cases i
 · exact SourceMainFramesV1.pack_output (i:=608) (base:=SynergyHeightC.FullMainFrame.base total 608) (input:=SourceMainFramesV1.Point0608.input) (pair:=SourceMainFramesV1.Point0608.outputs) SourceMainFramesV1.Point0608.input_defined SourceMainFramesV1.Point0608.outputs_defined (SourceMainFramesV1.Point0608.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=609) (base:=SynergyHeightC.FullMainFrame.base total 609) (input:=SourceMainFramesV1.Point0609.input) (pair:=SourceMainFramesV1.Point0609.outputs) SourceMainFramesV1.Point0609.input_defined SourceMainFramesV1.Point0609.outputs_defined (SourceMainFramesV1.Point0609.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=610) (base:=SynergyHeightC.FullMainFrame.base total 610) (input:=SourceMainFramesV1.Point0610.input) (pair:=SourceMainFramesV1.Point0610.outputs) SourceMainFramesV1.Point0610.input_defined SourceMainFramesV1.Point0610.outputs_defined (SourceMainFramesV1.Point0610.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=611) (base:=SynergyHeightC.FullMainFrame.base total 611) (input:=SourceMainFramesV1.Point0611.input) (pair:=SourceMainFramesV1.Point0611.outputs) SourceMainFramesV1.Point0611.input_defined SourceMainFramesV1.Point0611.outputs_defined (SourceMainFramesV1.Point0611.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=612) (base:=SynergyHeightC.FullMainFrame.base total 612) (input:=SourceMainFramesV1.Point0612.input) (pair:=SourceMainFramesV1.Point0612.outputs) SourceMainFramesV1.Point0612.input_defined SourceMainFramesV1.Point0612.outputs_defined (SourceMainFramesV1.Point0612.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=613) (base:=SynergyHeightC.FullMainFrame.base total 613) (input:=SourceMainFramesV1.Point0613.input) (pair:=SourceMainFramesV1.Point0613.outputs) SourceMainFramesV1.Point0613.input_defined SourceMainFramesV1.Point0613.outputs_defined (SourceMainFramesV1.Point0613.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=614) (base:=SynergyHeightC.FullMainFrame.base total 614) (input:=SourceMainFramesV1.Point0614.input) (pair:=SourceMainFramesV1.Point0614.outputs) SourceMainFramesV1.Point0614.input_defined SourceMainFramesV1.Point0614.outputs_defined (SourceMainFramesV1.Point0614.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=615) (base:=SynergyHeightC.FullMainFrame.base total 615) (input:=SourceMainFramesV1.Point0615.input) (pair:=SourceMainFramesV1.Point0615.outputs) SourceMainFramesV1.Point0615.input_defined SourceMainFramesV1.Point0615.outputs_defined (SourceMainFramesV1.Point0615.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=616) (base:=SynergyHeightC.FullMainFrame.base total 616) (input:=SourceMainFramesV1.Point0616.input) (pair:=SourceMainFramesV1.Point0616.outputs) SourceMainFramesV1.Point0616.input_defined SourceMainFramesV1.Point0616.outputs_defined (SourceMainFramesV1.Point0616.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=617) (base:=SynergyHeightC.FullMainFrame.base total 617) (input:=SourceMainFramesV1.Point0617.input) (pair:=SourceMainFramesV1.Point0617.outputs) SourceMainFramesV1.Point0617.input_defined SourceMainFramesV1.Point0617.outputs_defined (SourceMainFramesV1.Point0617.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=618) (base:=SynergyHeightC.FullMainFrame.base total 618) (input:=SourceMainFramesV1.Point0618.input) (pair:=SourceMainFramesV1.Point0618.outputs) SourceMainFramesV1.Point0618.input_defined SourceMainFramesV1.Point0618.outputs_defined (SourceMainFramesV1.Point0618.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=619) (base:=SynergyHeightC.FullMainFrame.base total 619) (input:=SourceMainFramesV1.Point0619.input) (pair:=SourceMainFramesV1.Point0619.outputs) SourceMainFramesV1.Point0619.input_defined SourceMainFramesV1.Point0619.outputs_defined (SourceMainFramesV1.Point0619.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=620) (base:=SynergyHeightC.FullMainFrame.base total 620) (input:=SourceMainFramesV1.Point0620.input) (pair:=SourceMainFramesV1.Point0620.outputs) SourceMainFramesV1.Point0620.input_defined SourceMainFramesV1.Point0620.outputs_defined (SourceMainFramesV1.Point0620.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=621) (base:=SynergyHeightC.FullMainFrame.base total 621) (input:=SourceMainFramesV1.Point0621.input) (pair:=SourceMainFramesV1.Point0621.outputs) SourceMainFramesV1.Point0621.input_defined SourceMainFramesV1.Point0621.outputs_defined (SourceMainFramesV1.Point0621.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=622) (base:=SynergyHeightC.FullMainFrame.base total 622) (input:=SourceMainFramesV1.Point0622.input) (pair:=SourceMainFramesV1.Point0622.outputs) SourceMainFramesV1.Point0622.input_defined SourceMainFramesV1.Point0622.outputs_defined (SourceMainFramesV1.Point0622.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=623) (base:=SynergyHeightC.FullMainFrame.base total 623) (input:=SourceMainFramesV1.Point0623.input) (pair:=SourceMainFramesV1.Point0623.outputs) SourceMainFramesV1.Point0623.input_defined SourceMainFramesV1.Point0623.outputs_defined (SourceMainFramesV1.Point0623.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=624) (base:=SynergyHeightC.FullMainFrame.base total 624) (input:=SourceMainFramesV1.Point0624.input) (pair:=SourceMainFramesV1.Point0624.outputs) SourceMainFramesV1.Point0624.input_defined SourceMainFramesV1.Point0624.outputs_defined (SourceMainFramesV1.Point0624.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=625) (base:=SynergyHeightC.FullMainFrame.base total 625) (input:=SourceMainFramesV1.Point0625.input) (pair:=SourceMainFramesV1.Point0625.outputs) SourceMainFramesV1.Point0625.input_defined SourceMainFramesV1.Point0625.outputs_defined (SourceMainFramesV1.Point0625.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=626) (base:=SynergyHeightC.FullMainFrame.base total 626) (input:=SourceMainFramesV1.Point0626.input) (pair:=SourceMainFramesV1.Point0626.outputs) SourceMainFramesV1.Point0626.input_defined SourceMainFramesV1.Point0626.outputs_defined (SourceMainFramesV1.Point0626.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=627) (base:=SynergyHeightC.FullMainFrame.base total 627) (input:=SourceMainFramesV1.Point0627.input) (pair:=SourceMainFramesV1.Point0627.outputs) SourceMainFramesV1.Point0627.input_defined SourceMainFramesV1.Point0627.outputs_defined (SourceMainFramesV1.Point0627.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=628) (base:=SynergyHeightC.FullMainFrame.base total 628) (input:=SourceMainFramesV1.Point0628.input) (pair:=SourceMainFramesV1.Point0628.outputs) SourceMainFramesV1.Point0628.input_defined SourceMainFramesV1.Point0628.outputs_defined (SourceMainFramesV1.Point0628.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=629) (base:=SynergyHeightC.FullMainFrame.base total 629) (input:=SourceMainFramesV1.Point0629.input) (pair:=SourceMainFramesV1.Point0629.outputs) SourceMainFramesV1.Point0629.input_defined SourceMainFramesV1.Point0629.outputs_defined (SourceMainFramesV1.Point0629.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=630) (base:=SynergyHeightC.FullMainFrame.base total 630) (input:=SourceMainFramesV1.Point0630.input) (pair:=SourceMainFramesV1.Point0630.outputs) SourceMainFramesV1.Point0630.input_defined SourceMainFramesV1.Point0630.outputs_defined (SourceMainFramesV1.Point0630.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=631) (base:=SynergyHeightC.FullMainFrame.base total 631) (input:=SourceMainFramesV1.Point0631.input) (pair:=SourceMainFramesV1.Point0631.outputs) SourceMainFramesV1.Point0631.input_defined SourceMainFramesV1.Point0631.outputs_defined (SourceMainFramesV1.Point0631.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=632) (base:=SynergyHeightC.FullMainFrame.base total 632) (input:=SourceMainFramesV1.Point0632.input) (pair:=SourceMainFramesV1.Point0632.outputs) SourceMainFramesV1.Point0632.input_defined SourceMainFramesV1.Point0632.outputs_defined (SourceMainFramesV1.Point0632.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=633) (base:=SynergyHeightC.FullMainFrame.base total 633) (input:=SourceMainFramesV1.Point0633.input) (pair:=SourceMainFramesV1.Point0633.outputs) SourceMainFramesV1.Point0633.input_defined SourceMainFramesV1.Point0633.outputs_defined (SourceMainFramesV1.Point0633.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=634) (base:=SynergyHeightC.FullMainFrame.base total 634) (input:=SourceMainFramesV1.Point0634.input) (pair:=SourceMainFramesV1.Point0634.outputs) SourceMainFramesV1.Point0634.input_defined SourceMainFramesV1.Point0634.outputs_defined (SourceMainFramesV1.Point0634.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=635) (base:=SynergyHeightC.FullMainFrame.base total 635) (input:=SourceMainFramesV1.Point0635.input) (pair:=SourceMainFramesV1.Point0635.outputs) SourceMainFramesV1.Point0635.input_defined SourceMainFramesV1.Point0635.outputs_defined (SourceMainFramesV1.Point0635.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=636) (base:=SynergyHeightC.FullMainFrame.base total 636) (input:=SourceMainFramesV1.Point0636.input) (pair:=SourceMainFramesV1.Point0636.outputs) SourceMainFramesV1.Point0636.input_defined SourceMainFramesV1.Point0636.outputs_defined (SourceMainFramesV1.Point0636.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=637) (base:=SynergyHeightC.FullMainFrame.base total 637) (input:=SourceMainFramesV1.Point0637.input) (pair:=SourceMainFramesV1.Point0637.outputs) SourceMainFramesV1.Point0637.input_defined SourceMainFramesV1.Point0637.outputs_defined (SourceMainFramesV1.Point0637.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=638) (base:=SynergyHeightC.FullMainFrame.base total 638) (input:=SourceMainFramesV1.Point0638.input) (pair:=SourceMainFramesV1.Point0638.outputs) SourceMainFramesV1.Point0638.input_defined SourceMainFramesV1.Point0638.outputs_defined (SourceMainFramesV1.Point0638.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=639) (base:=SynergyHeightC.FullMainFrame.base total 639) (input:=SourceMainFramesV1.Point0639.input) (pair:=SourceMainFramesV1.Point0639.outputs) SourceMainFramesV1.Point0639.input_defined SourceMainFramesV1.Point0639.outputs_defined (SourceMainFramesV1.Point0639.source_outputs total)
end SourceMainFramesV1.Block19
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Block19.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
