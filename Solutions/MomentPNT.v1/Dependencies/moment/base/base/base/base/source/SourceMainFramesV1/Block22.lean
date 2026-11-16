import SourceMainFramesV1.Point0704
import SourceMainFramesV1.Point0705
import SourceMainFramesV1.Point0706
import SourceMainFramesV1.Point0707
import SourceMainFramesV1.Point0708
import SourceMainFramesV1.Point0709
import SourceMainFramesV1.Point0710
import SourceMainFramesV1.Point0711
import SourceMainFramesV1.Point0712
import SourceMainFramesV1.Point0713
import SourceMainFramesV1.Point0714
import SourceMainFramesV1.Point0715
import SourceMainFramesV1.Point0716
import SourceMainFramesV1.Point0717
import SourceMainFramesV1.Point0718
import SourceMainFramesV1.Point0719
import SourceMainFramesV1.Point0720
import SourceMainFramesV1.Point0721
import SourceMainFramesV1.Point0722
import SourceMainFramesV1.Point0723
import SourceMainFramesV1.Point0724
import SourceMainFramesV1.Point0725
import SourceMainFramesV1.Point0726
import SourceMainFramesV1.Point0727
import SourceMainFramesV1.Point0728
import SourceMainFramesV1.Point0729
import SourceMainFramesV1.Point0730
import SourceMainFramesV1.Point0731
import SourceMainFramesV1.Point0732
import SourceMainFramesV1.Point0733
import SourceMainFramesV1.Point0734
import SourceMainFramesV1.Point0735
import SourceMainFramesV1.PackOutput
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Block22
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (total : ProofBox) (i : ℕ) (lower : 704 ≤ i) (upper : i < 736) :
 ∃ base input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs base input c d := by
 interval_cases i
 · exact SourceMainFramesV1.pack_output (i:=704) (base:=SynergyHeightC.FullMainFrame.base total 704) (input:=SourceMainFramesV1.Point0704.input) (pair:=SourceMainFramesV1.Point0704.outputs) SourceMainFramesV1.Point0704.input_defined SourceMainFramesV1.Point0704.outputs_defined (SourceMainFramesV1.Point0704.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=705) (base:=SynergyHeightC.FullMainFrame.base total 705) (input:=SourceMainFramesV1.Point0705.input) (pair:=SourceMainFramesV1.Point0705.outputs) SourceMainFramesV1.Point0705.input_defined SourceMainFramesV1.Point0705.outputs_defined (SourceMainFramesV1.Point0705.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=706) (base:=SynergyHeightC.FullMainFrame.base total 706) (input:=SourceMainFramesV1.Point0706.input) (pair:=SourceMainFramesV1.Point0706.outputs) SourceMainFramesV1.Point0706.input_defined SourceMainFramesV1.Point0706.outputs_defined (SourceMainFramesV1.Point0706.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=707) (base:=SynergyHeightC.FullMainFrame.base total 707) (input:=SourceMainFramesV1.Point0707.input) (pair:=SourceMainFramesV1.Point0707.outputs) SourceMainFramesV1.Point0707.input_defined SourceMainFramesV1.Point0707.outputs_defined (SourceMainFramesV1.Point0707.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=708) (base:=SynergyHeightC.FullMainFrame.base total 708) (input:=SourceMainFramesV1.Point0708.input) (pair:=SourceMainFramesV1.Point0708.outputs) SourceMainFramesV1.Point0708.input_defined SourceMainFramesV1.Point0708.outputs_defined (SourceMainFramesV1.Point0708.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=709) (base:=SynergyHeightC.FullMainFrame.base total 709) (input:=SourceMainFramesV1.Point0709.input) (pair:=SourceMainFramesV1.Point0709.outputs) SourceMainFramesV1.Point0709.input_defined SourceMainFramesV1.Point0709.outputs_defined (SourceMainFramesV1.Point0709.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=710) (base:=SynergyHeightC.FullMainFrame.base total 710) (input:=SourceMainFramesV1.Point0710.input) (pair:=SourceMainFramesV1.Point0710.outputs) SourceMainFramesV1.Point0710.input_defined SourceMainFramesV1.Point0710.outputs_defined (SourceMainFramesV1.Point0710.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=711) (base:=SynergyHeightC.FullMainFrame.base total 711) (input:=SourceMainFramesV1.Point0711.input) (pair:=SourceMainFramesV1.Point0711.outputs) SourceMainFramesV1.Point0711.input_defined SourceMainFramesV1.Point0711.outputs_defined (SourceMainFramesV1.Point0711.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=712) (base:=SynergyHeightC.FullMainFrame.base total 712) (input:=SourceMainFramesV1.Point0712.input) (pair:=SourceMainFramesV1.Point0712.outputs) SourceMainFramesV1.Point0712.input_defined SourceMainFramesV1.Point0712.outputs_defined (SourceMainFramesV1.Point0712.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=713) (base:=SynergyHeightC.FullMainFrame.base total 713) (input:=SourceMainFramesV1.Point0713.input) (pair:=SourceMainFramesV1.Point0713.outputs) SourceMainFramesV1.Point0713.input_defined SourceMainFramesV1.Point0713.outputs_defined (SourceMainFramesV1.Point0713.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=714) (base:=SynergyHeightC.FullMainFrame.base total 714) (input:=SourceMainFramesV1.Point0714.input) (pair:=SourceMainFramesV1.Point0714.outputs) SourceMainFramesV1.Point0714.input_defined SourceMainFramesV1.Point0714.outputs_defined (SourceMainFramesV1.Point0714.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=715) (base:=SynergyHeightC.FullMainFrame.base total 715) (input:=SourceMainFramesV1.Point0715.input) (pair:=SourceMainFramesV1.Point0715.outputs) SourceMainFramesV1.Point0715.input_defined SourceMainFramesV1.Point0715.outputs_defined (SourceMainFramesV1.Point0715.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=716) (base:=SynergyHeightC.FullMainFrame.base total 716) (input:=SourceMainFramesV1.Point0716.input) (pair:=SourceMainFramesV1.Point0716.outputs) SourceMainFramesV1.Point0716.input_defined SourceMainFramesV1.Point0716.outputs_defined (SourceMainFramesV1.Point0716.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=717) (base:=SynergyHeightC.FullMainFrame.base total 717) (input:=SourceMainFramesV1.Point0717.input) (pair:=SourceMainFramesV1.Point0717.outputs) SourceMainFramesV1.Point0717.input_defined SourceMainFramesV1.Point0717.outputs_defined (SourceMainFramesV1.Point0717.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=718) (base:=SynergyHeightC.FullMainFrame.base total 718) (input:=SourceMainFramesV1.Point0718.input) (pair:=SourceMainFramesV1.Point0718.outputs) SourceMainFramesV1.Point0718.input_defined SourceMainFramesV1.Point0718.outputs_defined (SourceMainFramesV1.Point0718.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=719) (base:=SynergyHeightC.FullMainFrame.base total 719) (input:=SourceMainFramesV1.Point0719.input) (pair:=SourceMainFramesV1.Point0719.outputs) SourceMainFramesV1.Point0719.input_defined SourceMainFramesV1.Point0719.outputs_defined (SourceMainFramesV1.Point0719.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=720) (base:=SynergyHeightC.FullMainFrame.base total 720) (input:=SourceMainFramesV1.Point0720.input) (pair:=SourceMainFramesV1.Point0720.outputs) SourceMainFramesV1.Point0720.input_defined SourceMainFramesV1.Point0720.outputs_defined (SourceMainFramesV1.Point0720.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=721) (base:=SynergyHeightC.FullMainFrame.base total 721) (input:=SourceMainFramesV1.Point0721.input) (pair:=SourceMainFramesV1.Point0721.outputs) SourceMainFramesV1.Point0721.input_defined SourceMainFramesV1.Point0721.outputs_defined (SourceMainFramesV1.Point0721.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=722) (base:=SynergyHeightC.FullMainFrame.base total 722) (input:=SourceMainFramesV1.Point0722.input) (pair:=SourceMainFramesV1.Point0722.outputs) SourceMainFramesV1.Point0722.input_defined SourceMainFramesV1.Point0722.outputs_defined (SourceMainFramesV1.Point0722.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=723) (base:=SynergyHeightC.FullMainFrame.base total 723) (input:=SourceMainFramesV1.Point0723.input) (pair:=SourceMainFramesV1.Point0723.outputs) SourceMainFramesV1.Point0723.input_defined SourceMainFramesV1.Point0723.outputs_defined (SourceMainFramesV1.Point0723.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=724) (base:=SynergyHeightC.FullMainFrame.base total 724) (input:=SourceMainFramesV1.Point0724.input) (pair:=SourceMainFramesV1.Point0724.outputs) SourceMainFramesV1.Point0724.input_defined SourceMainFramesV1.Point0724.outputs_defined (SourceMainFramesV1.Point0724.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=725) (base:=SynergyHeightC.FullMainFrame.base total 725) (input:=SourceMainFramesV1.Point0725.input) (pair:=SourceMainFramesV1.Point0725.outputs) SourceMainFramesV1.Point0725.input_defined SourceMainFramesV1.Point0725.outputs_defined (SourceMainFramesV1.Point0725.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=726) (base:=SynergyHeightC.FullMainFrame.base total 726) (input:=SourceMainFramesV1.Point0726.input) (pair:=SourceMainFramesV1.Point0726.outputs) SourceMainFramesV1.Point0726.input_defined SourceMainFramesV1.Point0726.outputs_defined (SourceMainFramesV1.Point0726.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=727) (base:=SynergyHeightC.FullMainFrame.base total 727) (input:=SourceMainFramesV1.Point0727.input) (pair:=SourceMainFramesV1.Point0727.outputs) SourceMainFramesV1.Point0727.input_defined SourceMainFramesV1.Point0727.outputs_defined (SourceMainFramesV1.Point0727.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=728) (base:=SynergyHeightC.FullMainFrame.base total 728) (input:=SourceMainFramesV1.Point0728.input) (pair:=SourceMainFramesV1.Point0728.outputs) SourceMainFramesV1.Point0728.input_defined SourceMainFramesV1.Point0728.outputs_defined (SourceMainFramesV1.Point0728.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=729) (base:=SynergyHeightC.FullMainFrame.base total 729) (input:=SourceMainFramesV1.Point0729.input) (pair:=SourceMainFramesV1.Point0729.outputs) SourceMainFramesV1.Point0729.input_defined SourceMainFramesV1.Point0729.outputs_defined (SourceMainFramesV1.Point0729.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=730) (base:=SynergyHeightC.FullMainFrame.base total 730) (input:=SourceMainFramesV1.Point0730.input) (pair:=SourceMainFramesV1.Point0730.outputs) SourceMainFramesV1.Point0730.input_defined SourceMainFramesV1.Point0730.outputs_defined (SourceMainFramesV1.Point0730.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=731) (base:=SynergyHeightC.FullMainFrame.base total 731) (input:=SourceMainFramesV1.Point0731.input) (pair:=SourceMainFramesV1.Point0731.outputs) SourceMainFramesV1.Point0731.input_defined SourceMainFramesV1.Point0731.outputs_defined (SourceMainFramesV1.Point0731.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=732) (base:=SynergyHeightC.FullMainFrame.base total 732) (input:=SourceMainFramesV1.Point0732.input) (pair:=SourceMainFramesV1.Point0732.outputs) SourceMainFramesV1.Point0732.input_defined SourceMainFramesV1.Point0732.outputs_defined (SourceMainFramesV1.Point0732.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=733) (base:=SynergyHeightC.FullMainFrame.base total 733) (input:=SourceMainFramesV1.Point0733.input) (pair:=SourceMainFramesV1.Point0733.outputs) SourceMainFramesV1.Point0733.input_defined SourceMainFramesV1.Point0733.outputs_defined (SourceMainFramesV1.Point0733.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=734) (base:=SynergyHeightC.FullMainFrame.base total 734) (input:=SourceMainFramesV1.Point0734.input) (pair:=SourceMainFramesV1.Point0734.outputs) SourceMainFramesV1.Point0734.input_defined SourceMainFramesV1.Point0734.outputs_defined (SourceMainFramesV1.Point0734.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=735) (base:=SynergyHeightC.FullMainFrame.base total 735) (input:=SourceMainFramesV1.Point0735.input) (pair:=SourceMainFramesV1.Point0735.outputs) SourceMainFramesV1.Point0735.input_defined SourceMainFramesV1.Point0735.outputs_defined (SourceMainFramesV1.Point0735.source_outputs total)
end SourceMainFramesV1.Block22
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Block22.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
