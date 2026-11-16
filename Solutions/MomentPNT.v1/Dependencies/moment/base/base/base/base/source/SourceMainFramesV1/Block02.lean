import SourceMainFramesV1.Point0064
import SourceMainFramesV1.Point0065
import SourceMainFramesV1.Point0066
import SourceMainFramesV1.Point0067
import SourceMainFramesV1.Point0068
import SourceMainFramesV1.Point0069
import SourceMainFramesV1.Point0070
import SourceMainFramesV1.Point0071
import SourceMainFramesV1.Point0072
import SourceMainFramesV1.Point0073
import SourceMainFramesV1.Point0074
import SourceMainFramesV1.Point0075
import SourceMainFramesV1.Point0076
import SourceMainFramesV1.Point0077
import SourceMainFramesV1.Point0078
import SourceMainFramesV1.Point0079
import SourceMainFramesV1.Point0080
import SourceMainFramesV1.Point0081
import SourceMainFramesV1.Point0082
import SourceMainFramesV1.Point0083
import SourceMainFramesV1.Point0084
import SourceMainFramesV1.Point0085
import SourceMainFramesV1.Point0086
import SourceMainFramesV1.Point0087
import SourceMainFramesV1.Point0088
import SourceMainFramesV1.Point0089
import SourceMainFramesV1.Point0090
import SourceMainFramesV1.Point0091
import SourceMainFramesV1.Point0092
import SourceMainFramesV1.Point0093
import SourceMainFramesV1.Point0094
import SourceMainFramesV1.Point0095
import SourceMainFramesV1.PackOutput
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Block02
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (total : ProofBox) (i : ℕ) (lower : 64 ≤ i) (upper : i < 96) :
 ∃ base input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs base input c d := by
 interval_cases i
 · exact SourceMainFramesV1.pack_output (i:=64) (base:=SynergyHeightC.FullMainFrame.base total 64) (input:=SourceMainFramesV1.Point0064.input) (pair:=SourceMainFramesV1.Point0064.outputs) SourceMainFramesV1.Point0064.input_defined SourceMainFramesV1.Point0064.outputs_defined (SourceMainFramesV1.Point0064.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=65) (base:=SynergyHeightC.FullMainFrame.base total 65) (input:=SourceMainFramesV1.Point0065.input) (pair:=SourceMainFramesV1.Point0065.outputs) SourceMainFramesV1.Point0065.input_defined SourceMainFramesV1.Point0065.outputs_defined (SourceMainFramesV1.Point0065.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=66) (base:=SynergyHeightC.FullMainFrame.base total 66) (input:=SourceMainFramesV1.Point0066.input) (pair:=SourceMainFramesV1.Point0066.outputs) SourceMainFramesV1.Point0066.input_defined SourceMainFramesV1.Point0066.outputs_defined (SourceMainFramesV1.Point0066.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=67) (base:=SynergyHeightC.FullMainFrame.base total 67) (input:=SourceMainFramesV1.Point0067.input) (pair:=SourceMainFramesV1.Point0067.outputs) SourceMainFramesV1.Point0067.input_defined SourceMainFramesV1.Point0067.outputs_defined (SourceMainFramesV1.Point0067.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=68) (base:=SynergyHeightC.FullMainFrame.base total 68) (input:=SourceMainFramesV1.Point0068.input) (pair:=SourceMainFramesV1.Point0068.outputs) SourceMainFramesV1.Point0068.input_defined SourceMainFramesV1.Point0068.outputs_defined (SourceMainFramesV1.Point0068.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=69) (base:=SynergyHeightC.FullMainFrame.base total 69) (input:=SourceMainFramesV1.Point0069.input) (pair:=SourceMainFramesV1.Point0069.outputs) SourceMainFramesV1.Point0069.input_defined SourceMainFramesV1.Point0069.outputs_defined (SourceMainFramesV1.Point0069.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=70) (base:=SynergyHeightC.FullMainFrame.base total 70) (input:=SourceMainFramesV1.Point0070.input) (pair:=SourceMainFramesV1.Point0070.outputs) SourceMainFramesV1.Point0070.input_defined SourceMainFramesV1.Point0070.outputs_defined (SourceMainFramesV1.Point0070.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=71) (base:=SynergyHeightC.FullMainFrame.base total 71) (input:=SourceMainFramesV1.Point0071.input) (pair:=SourceMainFramesV1.Point0071.outputs) SourceMainFramesV1.Point0071.input_defined SourceMainFramesV1.Point0071.outputs_defined (SourceMainFramesV1.Point0071.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=72) (base:=SynergyHeightC.FullMainFrame.base total 72) (input:=SourceMainFramesV1.Point0072.input) (pair:=SourceMainFramesV1.Point0072.outputs) SourceMainFramesV1.Point0072.input_defined SourceMainFramesV1.Point0072.outputs_defined (SourceMainFramesV1.Point0072.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=73) (base:=SynergyHeightC.FullMainFrame.base total 73) (input:=SourceMainFramesV1.Point0073.input) (pair:=SourceMainFramesV1.Point0073.outputs) SourceMainFramesV1.Point0073.input_defined SourceMainFramesV1.Point0073.outputs_defined (SourceMainFramesV1.Point0073.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=74) (base:=SynergyHeightC.FullMainFrame.base total 74) (input:=SourceMainFramesV1.Point0074.input) (pair:=SourceMainFramesV1.Point0074.outputs) SourceMainFramesV1.Point0074.input_defined SourceMainFramesV1.Point0074.outputs_defined (SourceMainFramesV1.Point0074.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=75) (base:=SynergyHeightC.FullMainFrame.base total 75) (input:=SourceMainFramesV1.Point0075.input) (pair:=SourceMainFramesV1.Point0075.outputs) SourceMainFramesV1.Point0075.input_defined SourceMainFramesV1.Point0075.outputs_defined (SourceMainFramesV1.Point0075.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=76) (base:=SynergyHeightC.FullMainFrame.base total 76) (input:=SourceMainFramesV1.Point0076.input) (pair:=SourceMainFramesV1.Point0076.outputs) SourceMainFramesV1.Point0076.input_defined SourceMainFramesV1.Point0076.outputs_defined (SourceMainFramesV1.Point0076.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=77) (base:=SynergyHeightC.FullMainFrame.base total 77) (input:=SourceMainFramesV1.Point0077.input) (pair:=SourceMainFramesV1.Point0077.outputs) SourceMainFramesV1.Point0077.input_defined SourceMainFramesV1.Point0077.outputs_defined (SourceMainFramesV1.Point0077.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=78) (base:=SynergyHeightC.FullMainFrame.base total 78) (input:=SourceMainFramesV1.Point0078.input) (pair:=SourceMainFramesV1.Point0078.outputs) SourceMainFramesV1.Point0078.input_defined SourceMainFramesV1.Point0078.outputs_defined (SourceMainFramesV1.Point0078.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=79) (base:=SynergyHeightC.FullMainFrame.base total 79) (input:=SourceMainFramesV1.Point0079.input) (pair:=SourceMainFramesV1.Point0079.outputs) SourceMainFramesV1.Point0079.input_defined SourceMainFramesV1.Point0079.outputs_defined (SourceMainFramesV1.Point0079.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=80) (base:=SynergyHeightC.FullMainFrame.base total 80) (input:=SourceMainFramesV1.Point0080.input) (pair:=SourceMainFramesV1.Point0080.outputs) SourceMainFramesV1.Point0080.input_defined SourceMainFramesV1.Point0080.outputs_defined (SourceMainFramesV1.Point0080.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=81) (base:=SynergyHeightC.FullMainFrame.base total 81) (input:=SourceMainFramesV1.Point0081.input) (pair:=SourceMainFramesV1.Point0081.outputs) SourceMainFramesV1.Point0081.input_defined SourceMainFramesV1.Point0081.outputs_defined (SourceMainFramesV1.Point0081.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=82) (base:=SynergyHeightC.FullMainFrame.base total 82) (input:=SourceMainFramesV1.Point0082.input) (pair:=SourceMainFramesV1.Point0082.outputs) SourceMainFramesV1.Point0082.input_defined SourceMainFramesV1.Point0082.outputs_defined (SourceMainFramesV1.Point0082.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=83) (base:=SynergyHeightC.FullMainFrame.base total 83) (input:=SourceMainFramesV1.Point0083.input) (pair:=SourceMainFramesV1.Point0083.outputs) SourceMainFramesV1.Point0083.input_defined SourceMainFramesV1.Point0083.outputs_defined (SourceMainFramesV1.Point0083.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=84) (base:=SynergyHeightC.FullMainFrame.base total 84) (input:=SourceMainFramesV1.Point0084.input) (pair:=SourceMainFramesV1.Point0084.outputs) SourceMainFramesV1.Point0084.input_defined SourceMainFramesV1.Point0084.outputs_defined (SourceMainFramesV1.Point0084.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=85) (base:=SynergyHeightC.FullMainFrame.base total 85) (input:=SourceMainFramesV1.Point0085.input) (pair:=SourceMainFramesV1.Point0085.outputs) SourceMainFramesV1.Point0085.input_defined SourceMainFramesV1.Point0085.outputs_defined (SourceMainFramesV1.Point0085.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=86) (base:=SynergyHeightC.FullMainFrame.base total 86) (input:=SourceMainFramesV1.Point0086.input) (pair:=SourceMainFramesV1.Point0086.outputs) SourceMainFramesV1.Point0086.input_defined SourceMainFramesV1.Point0086.outputs_defined (SourceMainFramesV1.Point0086.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=87) (base:=SynergyHeightC.FullMainFrame.base total 87) (input:=SourceMainFramesV1.Point0087.input) (pair:=SourceMainFramesV1.Point0087.outputs) SourceMainFramesV1.Point0087.input_defined SourceMainFramesV1.Point0087.outputs_defined (SourceMainFramesV1.Point0087.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=88) (base:=SynergyHeightC.FullMainFrame.base total 88) (input:=SourceMainFramesV1.Point0088.input) (pair:=SourceMainFramesV1.Point0088.outputs) SourceMainFramesV1.Point0088.input_defined SourceMainFramesV1.Point0088.outputs_defined (SourceMainFramesV1.Point0088.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=89) (base:=SynergyHeightC.FullMainFrame.base total 89) (input:=SourceMainFramesV1.Point0089.input) (pair:=SourceMainFramesV1.Point0089.outputs) SourceMainFramesV1.Point0089.input_defined SourceMainFramesV1.Point0089.outputs_defined (SourceMainFramesV1.Point0089.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=90) (base:=SynergyHeightC.FullMainFrame.base total 90) (input:=SourceMainFramesV1.Point0090.input) (pair:=SourceMainFramesV1.Point0090.outputs) SourceMainFramesV1.Point0090.input_defined SourceMainFramesV1.Point0090.outputs_defined (SourceMainFramesV1.Point0090.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=91) (base:=SynergyHeightC.FullMainFrame.base total 91) (input:=SourceMainFramesV1.Point0091.input) (pair:=SourceMainFramesV1.Point0091.outputs) SourceMainFramesV1.Point0091.input_defined SourceMainFramesV1.Point0091.outputs_defined (SourceMainFramesV1.Point0091.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=92) (base:=SynergyHeightC.FullMainFrame.base total 92) (input:=SourceMainFramesV1.Point0092.input) (pair:=SourceMainFramesV1.Point0092.outputs) SourceMainFramesV1.Point0092.input_defined SourceMainFramesV1.Point0092.outputs_defined (SourceMainFramesV1.Point0092.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=93) (base:=SynergyHeightC.FullMainFrame.base total 93) (input:=SourceMainFramesV1.Point0093.input) (pair:=SourceMainFramesV1.Point0093.outputs) SourceMainFramesV1.Point0093.input_defined SourceMainFramesV1.Point0093.outputs_defined (SourceMainFramesV1.Point0093.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=94) (base:=SynergyHeightC.FullMainFrame.base total 94) (input:=SourceMainFramesV1.Point0094.input) (pair:=SourceMainFramesV1.Point0094.outputs) SourceMainFramesV1.Point0094.input_defined SourceMainFramesV1.Point0094.outputs_defined (SourceMainFramesV1.Point0094.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=95) (base:=SynergyHeightC.FullMainFrame.base total 95) (input:=SourceMainFramesV1.Point0095.input) (pair:=SourceMainFramesV1.Point0095.outputs) SourceMainFramesV1.Point0095.input_defined SourceMainFramesV1.Point0095.outputs_defined (SourceMainFramesV1.Point0095.source_outputs total)
end SourceMainFramesV1.Block02
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Block02.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
