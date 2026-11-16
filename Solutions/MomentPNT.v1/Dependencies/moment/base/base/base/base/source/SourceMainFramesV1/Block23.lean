import SourceMainFramesV1.Point0736
import SourceMainFramesV1.Point0737
import SourceMainFramesV1.Point0738
import SourceMainFramesV1.Point0739
import SourceMainFramesV1.Point0740
import SourceMainFramesV1.Point0741
import SourceMainFramesV1.Point0742
import SourceMainFramesV1.Point0743
import SourceMainFramesV1.Point0744
import SourceMainFramesV1.Point0745
import SourceMainFramesV1.Point0746
import SourceMainFramesV1.Point0747
import SourceMainFramesV1.Point0748
import SourceMainFramesV1.Point0749
import SourceMainFramesV1.Point0750
import SourceMainFramesV1.Point0751
import SourceMainFramesV1.Point0752
import SourceMainFramesV1.Point0753
import SourceMainFramesV1.Point0754
import SourceMainFramesV1.Point0755
import SourceMainFramesV1.Point0756
import SourceMainFramesV1.Point0757
import SourceMainFramesV1.Point0758
import SourceMainFramesV1.Point0759
import SourceMainFramesV1.Point0760
import SourceMainFramesV1.Point0761
import SourceMainFramesV1.Point0762
import SourceMainFramesV1.Point0763
import SourceMainFramesV1.Point0764
import SourceMainFramesV1.Point0765
import SourceMainFramesV1.Point0766
import SourceMainFramesV1.Point0767
import SourceMainFramesV1.PackOutput
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Block23
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (total : ProofBox) (i : ℕ) (lower : 736 ≤ i) (upper : i < 768) :
 ∃ base input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs base input c d := by
 interval_cases i
 · exact SourceMainFramesV1.pack_output (i:=736) (base:=SynergyHeightC.FullMainFrame.base total 736) (input:=SourceMainFramesV1.Point0736.input) (pair:=SourceMainFramesV1.Point0736.outputs) SourceMainFramesV1.Point0736.input_defined SourceMainFramesV1.Point0736.outputs_defined (SourceMainFramesV1.Point0736.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=737) (base:=SynergyHeightC.FullMainFrame.base total 737) (input:=SourceMainFramesV1.Point0737.input) (pair:=SourceMainFramesV1.Point0737.outputs) SourceMainFramesV1.Point0737.input_defined SourceMainFramesV1.Point0737.outputs_defined (SourceMainFramesV1.Point0737.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=738) (base:=SynergyHeightC.FullMainFrame.base total 738) (input:=SourceMainFramesV1.Point0738.input) (pair:=SourceMainFramesV1.Point0738.outputs) SourceMainFramesV1.Point0738.input_defined SourceMainFramesV1.Point0738.outputs_defined (SourceMainFramesV1.Point0738.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=739) (base:=SynergyHeightC.FullMainFrame.base total 739) (input:=SourceMainFramesV1.Point0739.input) (pair:=SourceMainFramesV1.Point0739.outputs) SourceMainFramesV1.Point0739.input_defined SourceMainFramesV1.Point0739.outputs_defined (SourceMainFramesV1.Point0739.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=740) (base:=SynergyHeightC.FullMainFrame.base total 740) (input:=SourceMainFramesV1.Point0740.input) (pair:=SourceMainFramesV1.Point0740.outputs) SourceMainFramesV1.Point0740.input_defined SourceMainFramesV1.Point0740.outputs_defined (SourceMainFramesV1.Point0740.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=741) (base:=SynergyHeightC.FullMainFrame.base total 741) (input:=SourceMainFramesV1.Point0741.input) (pair:=SourceMainFramesV1.Point0741.outputs) SourceMainFramesV1.Point0741.input_defined SourceMainFramesV1.Point0741.outputs_defined (SourceMainFramesV1.Point0741.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=742) (base:=SynergyHeightC.FullMainFrame.base total 742) (input:=SourceMainFramesV1.Point0742.input) (pair:=SourceMainFramesV1.Point0742.outputs) SourceMainFramesV1.Point0742.input_defined SourceMainFramesV1.Point0742.outputs_defined (SourceMainFramesV1.Point0742.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=743) (base:=SynergyHeightC.FullMainFrame.base total 743) (input:=SourceMainFramesV1.Point0743.input) (pair:=SourceMainFramesV1.Point0743.outputs) SourceMainFramesV1.Point0743.input_defined SourceMainFramesV1.Point0743.outputs_defined (SourceMainFramesV1.Point0743.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=744) (base:=SynergyHeightC.FullMainFrame.base total 744) (input:=SourceMainFramesV1.Point0744.input) (pair:=SourceMainFramesV1.Point0744.outputs) SourceMainFramesV1.Point0744.input_defined SourceMainFramesV1.Point0744.outputs_defined (SourceMainFramesV1.Point0744.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=745) (base:=SynergyHeightC.FullMainFrame.base total 745) (input:=SourceMainFramesV1.Point0745.input) (pair:=SourceMainFramesV1.Point0745.outputs) SourceMainFramesV1.Point0745.input_defined SourceMainFramesV1.Point0745.outputs_defined (SourceMainFramesV1.Point0745.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=746) (base:=SynergyHeightC.FullMainFrame.base total 746) (input:=SourceMainFramesV1.Point0746.input) (pair:=SourceMainFramesV1.Point0746.outputs) SourceMainFramesV1.Point0746.input_defined SourceMainFramesV1.Point0746.outputs_defined (SourceMainFramesV1.Point0746.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=747) (base:=SynergyHeightC.FullMainFrame.base total 747) (input:=SourceMainFramesV1.Point0747.input) (pair:=SourceMainFramesV1.Point0747.outputs) SourceMainFramesV1.Point0747.input_defined SourceMainFramesV1.Point0747.outputs_defined (SourceMainFramesV1.Point0747.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=748) (base:=SynergyHeightC.FullMainFrame.base total 748) (input:=SourceMainFramesV1.Point0748.input) (pair:=SourceMainFramesV1.Point0748.outputs) SourceMainFramesV1.Point0748.input_defined SourceMainFramesV1.Point0748.outputs_defined (SourceMainFramesV1.Point0748.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=749) (base:=SynergyHeightC.FullMainFrame.base total 749) (input:=SourceMainFramesV1.Point0749.input) (pair:=SourceMainFramesV1.Point0749.outputs) SourceMainFramesV1.Point0749.input_defined SourceMainFramesV1.Point0749.outputs_defined (SourceMainFramesV1.Point0749.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=750) (base:=SynergyHeightC.FullMainFrame.base total 750) (input:=SourceMainFramesV1.Point0750.input) (pair:=SourceMainFramesV1.Point0750.outputs) SourceMainFramesV1.Point0750.input_defined SourceMainFramesV1.Point0750.outputs_defined (SourceMainFramesV1.Point0750.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=751) (base:=SynergyHeightC.FullMainFrame.base total 751) (input:=SourceMainFramesV1.Point0751.input) (pair:=SourceMainFramesV1.Point0751.outputs) SourceMainFramesV1.Point0751.input_defined SourceMainFramesV1.Point0751.outputs_defined (SourceMainFramesV1.Point0751.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=752) (base:=SynergyHeightC.FullMainFrame.base total 752) (input:=SourceMainFramesV1.Point0752.input) (pair:=SourceMainFramesV1.Point0752.outputs) SourceMainFramesV1.Point0752.input_defined SourceMainFramesV1.Point0752.outputs_defined (SourceMainFramesV1.Point0752.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=753) (base:=SynergyHeightC.FullMainFrame.base total 753) (input:=SourceMainFramesV1.Point0753.input) (pair:=SourceMainFramesV1.Point0753.outputs) SourceMainFramesV1.Point0753.input_defined SourceMainFramesV1.Point0753.outputs_defined (SourceMainFramesV1.Point0753.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=754) (base:=SynergyHeightC.FullMainFrame.base total 754) (input:=SourceMainFramesV1.Point0754.input) (pair:=SourceMainFramesV1.Point0754.outputs) SourceMainFramesV1.Point0754.input_defined SourceMainFramesV1.Point0754.outputs_defined (SourceMainFramesV1.Point0754.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=755) (base:=SynergyHeightC.FullMainFrame.base total 755) (input:=SourceMainFramesV1.Point0755.input) (pair:=SourceMainFramesV1.Point0755.outputs) SourceMainFramesV1.Point0755.input_defined SourceMainFramesV1.Point0755.outputs_defined (SourceMainFramesV1.Point0755.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=756) (base:=SynergyHeightC.FullMainFrame.base total 756) (input:=SourceMainFramesV1.Point0756.input) (pair:=SourceMainFramesV1.Point0756.outputs) SourceMainFramesV1.Point0756.input_defined SourceMainFramesV1.Point0756.outputs_defined (SourceMainFramesV1.Point0756.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=757) (base:=SynergyHeightC.FullMainFrame.base total 757) (input:=SourceMainFramesV1.Point0757.input) (pair:=SourceMainFramesV1.Point0757.outputs) SourceMainFramesV1.Point0757.input_defined SourceMainFramesV1.Point0757.outputs_defined (SourceMainFramesV1.Point0757.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=758) (base:=SynergyHeightC.FullMainFrame.base total 758) (input:=SourceMainFramesV1.Point0758.input) (pair:=SourceMainFramesV1.Point0758.outputs) SourceMainFramesV1.Point0758.input_defined SourceMainFramesV1.Point0758.outputs_defined (SourceMainFramesV1.Point0758.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=759) (base:=SynergyHeightC.FullMainFrame.base total 759) (input:=SourceMainFramesV1.Point0759.input) (pair:=SourceMainFramesV1.Point0759.outputs) SourceMainFramesV1.Point0759.input_defined SourceMainFramesV1.Point0759.outputs_defined (SourceMainFramesV1.Point0759.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=760) (base:=SynergyHeightC.FullMainFrame.base total 760) (input:=SourceMainFramesV1.Point0760.input) (pair:=SourceMainFramesV1.Point0760.outputs) SourceMainFramesV1.Point0760.input_defined SourceMainFramesV1.Point0760.outputs_defined (SourceMainFramesV1.Point0760.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=761) (base:=SynergyHeightC.FullMainFrame.base total 761) (input:=SourceMainFramesV1.Point0761.input) (pair:=SourceMainFramesV1.Point0761.outputs) SourceMainFramesV1.Point0761.input_defined SourceMainFramesV1.Point0761.outputs_defined (SourceMainFramesV1.Point0761.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=762) (base:=SynergyHeightC.FullMainFrame.base total 762) (input:=SourceMainFramesV1.Point0762.input) (pair:=SourceMainFramesV1.Point0762.outputs) SourceMainFramesV1.Point0762.input_defined SourceMainFramesV1.Point0762.outputs_defined (SourceMainFramesV1.Point0762.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=763) (base:=SynergyHeightC.FullMainFrame.base total 763) (input:=SourceMainFramesV1.Point0763.input) (pair:=SourceMainFramesV1.Point0763.outputs) SourceMainFramesV1.Point0763.input_defined SourceMainFramesV1.Point0763.outputs_defined (SourceMainFramesV1.Point0763.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=764) (base:=SynergyHeightC.FullMainFrame.base total 764) (input:=SourceMainFramesV1.Point0764.input) (pair:=SourceMainFramesV1.Point0764.outputs) SourceMainFramesV1.Point0764.input_defined SourceMainFramesV1.Point0764.outputs_defined (SourceMainFramesV1.Point0764.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=765) (base:=SynergyHeightC.FullMainFrame.base total 765) (input:=SourceMainFramesV1.Point0765.input) (pair:=SourceMainFramesV1.Point0765.outputs) SourceMainFramesV1.Point0765.input_defined SourceMainFramesV1.Point0765.outputs_defined (SourceMainFramesV1.Point0765.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=766) (base:=SynergyHeightC.FullMainFrame.base total 766) (input:=SourceMainFramesV1.Point0766.input) (pair:=SourceMainFramesV1.Point0766.outputs) SourceMainFramesV1.Point0766.input_defined SourceMainFramesV1.Point0766.outputs_defined (SourceMainFramesV1.Point0766.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=767) (base:=SynergyHeightC.FullMainFrame.base total 767) (input:=SourceMainFramesV1.Point0767.input) (pair:=SourceMainFramesV1.Point0767.outputs) SourceMainFramesV1.Point0767.input_defined SourceMainFramesV1.Point0767.outputs_defined (SourceMainFramesV1.Point0767.source_outputs total)
end SourceMainFramesV1.Block23
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Block23.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
