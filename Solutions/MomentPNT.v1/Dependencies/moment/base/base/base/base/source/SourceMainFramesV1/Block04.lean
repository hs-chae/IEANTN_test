import SourceMainFramesV1.Point0128
import SourceMainFramesV1.Point0129
import SourceMainFramesV1.Point0130
import SourceMainFramesV1.Point0131
import SourceMainFramesV1.Point0132
import SourceMainFramesV1.Point0133
import SourceMainFramesV1.Point0134
import SourceMainFramesV1.Point0135
import SourceMainFramesV1.Point0136
import SourceMainFramesV1.Point0137
import SourceMainFramesV1.Point0138
import SourceMainFramesV1.Point0139
import SourceMainFramesV1.Point0140
import SourceMainFramesV1.Point0141
import SourceMainFramesV1.Point0142
import SourceMainFramesV1.Point0143
import SourceMainFramesV1.Point0144
import SourceMainFramesV1.Point0145
import SourceMainFramesV1.Point0146
import SourceMainFramesV1.Point0147
import SourceMainFramesV1.Point0148
import SourceMainFramesV1.Point0149
import SourceMainFramesV1.Point0150
import SourceMainFramesV1.Point0151
import SourceMainFramesV1.Point0152
import SourceMainFramesV1.Point0153
import SourceMainFramesV1.Point0154
import SourceMainFramesV1.Point0155
import SourceMainFramesV1.Point0156
import SourceMainFramesV1.Point0157
import SourceMainFramesV1.Point0158
import SourceMainFramesV1.Point0159
import SourceMainFramesV1.PackOutput
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Block04
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (total : ProofBox) (i : ℕ) (lower : 128 ≤ i) (upper : i < 160) :
 ∃ base input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs base input c d := by
 interval_cases i
 · exact SourceMainFramesV1.pack_output (i:=128) (base:=SynergyHeightC.FullMainFrame.base total 128) (input:=SourceMainFramesV1.Point0128.input) (pair:=SourceMainFramesV1.Point0128.outputs) SourceMainFramesV1.Point0128.input_defined SourceMainFramesV1.Point0128.outputs_defined (SourceMainFramesV1.Point0128.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=129) (base:=SynergyHeightC.FullMainFrame.base total 129) (input:=SourceMainFramesV1.Point0129.input) (pair:=SourceMainFramesV1.Point0129.outputs) SourceMainFramesV1.Point0129.input_defined SourceMainFramesV1.Point0129.outputs_defined (SourceMainFramesV1.Point0129.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=130) (base:=SynergyHeightC.FullMainFrame.base total 130) (input:=SourceMainFramesV1.Point0130.input) (pair:=SourceMainFramesV1.Point0130.outputs) SourceMainFramesV1.Point0130.input_defined SourceMainFramesV1.Point0130.outputs_defined (SourceMainFramesV1.Point0130.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=131) (base:=SynergyHeightC.FullMainFrame.base total 131) (input:=SourceMainFramesV1.Point0131.input) (pair:=SourceMainFramesV1.Point0131.outputs) SourceMainFramesV1.Point0131.input_defined SourceMainFramesV1.Point0131.outputs_defined (SourceMainFramesV1.Point0131.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=132) (base:=SynergyHeightC.FullMainFrame.base total 132) (input:=SourceMainFramesV1.Point0132.input) (pair:=SourceMainFramesV1.Point0132.outputs) SourceMainFramesV1.Point0132.input_defined SourceMainFramesV1.Point0132.outputs_defined (SourceMainFramesV1.Point0132.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=133) (base:=SynergyHeightC.FullMainFrame.base total 133) (input:=SourceMainFramesV1.Point0133.input) (pair:=SourceMainFramesV1.Point0133.outputs) SourceMainFramesV1.Point0133.input_defined SourceMainFramesV1.Point0133.outputs_defined (SourceMainFramesV1.Point0133.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=134) (base:=SynergyHeightC.FullMainFrame.base total 134) (input:=SourceMainFramesV1.Point0134.input) (pair:=SourceMainFramesV1.Point0134.outputs) SourceMainFramesV1.Point0134.input_defined SourceMainFramesV1.Point0134.outputs_defined (SourceMainFramesV1.Point0134.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=135) (base:=SynergyHeightC.FullMainFrame.base total 135) (input:=SourceMainFramesV1.Point0135.input) (pair:=SourceMainFramesV1.Point0135.outputs) SourceMainFramesV1.Point0135.input_defined SourceMainFramesV1.Point0135.outputs_defined (SourceMainFramesV1.Point0135.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=136) (base:=SynergyHeightC.FullMainFrame.base total 136) (input:=SourceMainFramesV1.Point0136.input) (pair:=SourceMainFramesV1.Point0136.outputs) SourceMainFramesV1.Point0136.input_defined SourceMainFramesV1.Point0136.outputs_defined (SourceMainFramesV1.Point0136.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=137) (base:=SynergyHeightC.FullMainFrame.base total 137) (input:=SourceMainFramesV1.Point0137.input) (pair:=SourceMainFramesV1.Point0137.outputs) SourceMainFramesV1.Point0137.input_defined SourceMainFramesV1.Point0137.outputs_defined (SourceMainFramesV1.Point0137.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=138) (base:=SynergyHeightC.FullMainFrame.base total 138) (input:=SourceMainFramesV1.Point0138.input) (pair:=SourceMainFramesV1.Point0138.outputs) SourceMainFramesV1.Point0138.input_defined SourceMainFramesV1.Point0138.outputs_defined (SourceMainFramesV1.Point0138.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=139) (base:=SynergyHeightC.FullMainFrame.base total 139) (input:=SourceMainFramesV1.Point0139.input) (pair:=SourceMainFramesV1.Point0139.outputs) SourceMainFramesV1.Point0139.input_defined SourceMainFramesV1.Point0139.outputs_defined (SourceMainFramesV1.Point0139.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=140) (base:=SynergyHeightC.FullMainFrame.base total 140) (input:=SourceMainFramesV1.Point0140.input) (pair:=SourceMainFramesV1.Point0140.outputs) SourceMainFramesV1.Point0140.input_defined SourceMainFramesV1.Point0140.outputs_defined (SourceMainFramesV1.Point0140.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=141) (base:=SynergyHeightC.FullMainFrame.base total 141) (input:=SourceMainFramesV1.Point0141.input) (pair:=SourceMainFramesV1.Point0141.outputs) SourceMainFramesV1.Point0141.input_defined SourceMainFramesV1.Point0141.outputs_defined (SourceMainFramesV1.Point0141.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=142) (base:=SynergyHeightC.FullMainFrame.base total 142) (input:=SourceMainFramesV1.Point0142.input) (pair:=SourceMainFramesV1.Point0142.outputs) SourceMainFramesV1.Point0142.input_defined SourceMainFramesV1.Point0142.outputs_defined (SourceMainFramesV1.Point0142.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=143) (base:=SynergyHeightC.FullMainFrame.base total 143) (input:=SourceMainFramesV1.Point0143.input) (pair:=SourceMainFramesV1.Point0143.outputs) SourceMainFramesV1.Point0143.input_defined SourceMainFramesV1.Point0143.outputs_defined (SourceMainFramesV1.Point0143.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=144) (base:=SynergyHeightC.FullMainFrame.base total 144) (input:=SourceMainFramesV1.Point0144.input) (pair:=SourceMainFramesV1.Point0144.outputs) SourceMainFramesV1.Point0144.input_defined SourceMainFramesV1.Point0144.outputs_defined (SourceMainFramesV1.Point0144.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=145) (base:=SynergyHeightC.FullMainFrame.base total 145) (input:=SourceMainFramesV1.Point0145.input) (pair:=SourceMainFramesV1.Point0145.outputs) SourceMainFramesV1.Point0145.input_defined SourceMainFramesV1.Point0145.outputs_defined (SourceMainFramesV1.Point0145.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=146) (base:=SynergyHeightC.FullMainFrame.base total 146) (input:=SourceMainFramesV1.Point0146.input) (pair:=SourceMainFramesV1.Point0146.outputs) SourceMainFramesV1.Point0146.input_defined SourceMainFramesV1.Point0146.outputs_defined (SourceMainFramesV1.Point0146.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=147) (base:=SynergyHeightC.FullMainFrame.base total 147) (input:=SourceMainFramesV1.Point0147.input) (pair:=SourceMainFramesV1.Point0147.outputs) SourceMainFramesV1.Point0147.input_defined SourceMainFramesV1.Point0147.outputs_defined (SourceMainFramesV1.Point0147.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=148) (base:=SynergyHeightC.FullMainFrame.base total 148) (input:=SourceMainFramesV1.Point0148.input) (pair:=SourceMainFramesV1.Point0148.outputs) SourceMainFramesV1.Point0148.input_defined SourceMainFramesV1.Point0148.outputs_defined (SourceMainFramesV1.Point0148.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=149) (base:=SynergyHeightC.FullMainFrame.base total 149) (input:=SourceMainFramesV1.Point0149.input) (pair:=SourceMainFramesV1.Point0149.outputs) SourceMainFramesV1.Point0149.input_defined SourceMainFramesV1.Point0149.outputs_defined (SourceMainFramesV1.Point0149.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=150) (base:=SynergyHeightC.FullMainFrame.base total 150) (input:=SourceMainFramesV1.Point0150.input) (pair:=SourceMainFramesV1.Point0150.outputs) SourceMainFramesV1.Point0150.input_defined SourceMainFramesV1.Point0150.outputs_defined (SourceMainFramesV1.Point0150.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=151) (base:=SynergyHeightC.FullMainFrame.base total 151) (input:=SourceMainFramesV1.Point0151.input) (pair:=SourceMainFramesV1.Point0151.outputs) SourceMainFramesV1.Point0151.input_defined SourceMainFramesV1.Point0151.outputs_defined (SourceMainFramesV1.Point0151.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=152) (base:=SynergyHeightC.FullMainFrame.base total 152) (input:=SourceMainFramesV1.Point0152.input) (pair:=SourceMainFramesV1.Point0152.outputs) SourceMainFramesV1.Point0152.input_defined SourceMainFramesV1.Point0152.outputs_defined (SourceMainFramesV1.Point0152.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=153) (base:=SynergyHeightC.FullMainFrame.base total 153) (input:=SourceMainFramesV1.Point0153.input) (pair:=SourceMainFramesV1.Point0153.outputs) SourceMainFramesV1.Point0153.input_defined SourceMainFramesV1.Point0153.outputs_defined (SourceMainFramesV1.Point0153.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=154) (base:=SynergyHeightC.FullMainFrame.base total 154) (input:=SourceMainFramesV1.Point0154.input) (pair:=SourceMainFramesV1.Point0154.outputs) SourceMainFramesV1.Point0154.input_defined SourceMainFramesV1.Point0154.outputs_defined (SourceMainFramesV1.Point0154.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=155) (base:=SynergyHeightC.FullMainFrame.base total 155) (input:=SourceMainFramesV1.Point0155.input) (pair:=SourceMainFramesV1.Point0155.outputs) SourceMainFramesV1.Point0155.input_defined SourceMainFramesV1.Point0155.outputs_defined (SourceMainFramesV1.Point0155.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=156) (base:=SynergyHeightC.FullMainFrame.base total 156) (input:=SourceMainFramesV1.Point0156.input) (pair:=SourceMainFramesV1.Point0156.outputs) SourceMainFramesV1.Point0156.input_defined SourceMainFramesV1.Point0156.outputs_defined (SourceMainFramesV1.Point0156.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=157) (base:=SynergyHeightC.FullMainFrame.base total 157) (input:=SourceMainFramesV1.Point0157.input) (pair:=SourceMainFramesV1.Point0157.outputs) SourceMainFramesV1.Point0157.input_defined SourceMainFramesV1.Point0157.outputs_defined (SourceMainFramesV1.Point0157.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=158) (base:=SynergyHeightC.FullMainFrame.base total 158) (input:=SourceMainFramesV1.Point0158.input) (pair:=SourceMainFramesV1.Point0158.outputs) SourceMainFramesV1.Point0158.input_defined SourceMainFramesV1.Point0158.outputs_defined (SourceMainFramesV1.Point0158.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=159) (base:=SynergyHeightC.FullMainFrame.base total 159) (input:=SourceMainFramesV1.Point0159.input) (pair:=SourceMainFramesV1.Point0159.outputs) SourceMainFramesV1.Point0159.input_defined SourceMainFramesV1.Point0159.outputs_defined (SourceMainFramesV1.Point0159.source_outputs total)
end SourceMainFramesV1.Block04
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Block04.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
