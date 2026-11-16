import SourceMainFramesV1.Point0160
import SourceMainFramesV1.Point0161
import SourceMainFramesV1.Point0162
import SourceMainFramesV1.Point0163
import SourceMainFramesV1.Point0164
import SourceMainFramesV1.Point0165
import SourceMainFramesV1.Point0166
import SourceMainFramesV1.Point0167
import SourceMainFramesV1.Point0168
import SourceMainFramesV1.Point0169
import SourceMainFramesV1.Point0170
import SourceMainFramesV1.Point0171
import SourceMainFramesV1.Point0172
import SourceMainFramesV1.Point0173
import SourceMainFramesV1.Point0174
import SourceMainFramesV1.Point0175
import SourceMainFramesV1.Point0176
import SourceMainFramesV1.Point0177
import SourceMainFramesV1.Point0178
import SourceMainFramesV1.Point0179
import SourceMainFramesV1.Point0180
import SourceMainFramesV1.Point0181
import SourceMainFramesV1.Point0182
import SourceMainFramesV1.Point0183
import SourceMainFramesV1.Point0184
import SourceMainFramesV1.Point0185
import SourceMainFramesV1.Point0186
import SourceMainFramesV1.Point0187
import SourceMainFramesV1.Point0188
import SourceMainFramesV1.Point0189
import SourceMainFramesV1.Point0190
import SourceMainFramesV1.Point0191
import SourceMainFramesV1.PackOutput
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Block05
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (total : ProofBox) (i : ℕ) (lower : 160 ≤ i) (upper : i < 192) :
 ∃ base input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs base input c d := by
 interval_cases i
 · exact SourceMainFramesV1.pack_output (i:=160) (base:=SynergyHeightC.FullMainFrame.base total 160) (input:=SourceMainFramesV1.Point0160.input) (pair:=SourceMainFramesV1.Point0160.outputs) SourceMainFramesV1.Point0160.input_defined SourceMainFramesV1.Point0160.outputs_defined (SourceMainFramesV1.Point0160.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=161) (base:=SynergyHeightC.FullMainFrame.base total 161) (input:=SourceMainFramesV1.Point0161.input) (pair:=SourceMainFramesV1.Point0161.outputs) SourceMainFramesV1.Point0161.input_defined SourceMainFramesV1.Point0161.outputs_defined (SourceMainFramesV1.Point0161.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=162) (base:=SynergyHeightC.FullMainFrame.base total 162) (input:=SourceMainFramesV1.Point0162.input) (pair:=SourceMainFramesV1.Point0162.outputs) SourceMainFramesV1.Point0162.input_defined SourceMainFramesV1.Point0162.outputs_defined (SourceMainFramesV1.Point0162.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=163) (base:=SynergyHeightC.FullMainFrame.base total 163) (input:=SourceMainFramesV1.Point0163.input) (pair:=SourceMainFramesV1.Point0163.outputs) SourceMainFramesV1.Point0163.input_defined SourceMainFramesV1.Point0163.outputs_defined (SourceMainFramesV1.Point0163.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=164) (base:=SynergyHeightC.FullMainFrame.base total 164) (input:=SourceMainFramesV1.Point0164.input) (pair:=SourceMainFramesV1.Point0164.outputs) SourceMainFramesV1.Point0164.input_defined SourceMainFramesV1.Point0164.outputs_defined (SourceMainFramesV1.Point0164.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=165) (base:=SynergyHeightC.FullMainFrame.base total 165) (input:=SourceMainFramesV1.Point0165.input) (pair:=SourceMainFramesV1.Point0165.outputs) SourceMainFramesV1.Point0165.input_defined SourceMainFramesV1.Point0165.outputs_defined (SourceMainFramesV1.Point0165.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=166) (base:=SynergyHeightC.FullMainFrame.base total 166) (input:=SourceMainFramesV1.Point0166.input) (pair:=SourceMainFramesV1.Point0166.outputs) SourceMainFramesV1.Point0166.input_defined SourceMainFramesV1.Point0166.outputs_defined (SourceMainFramesV1.Point0166.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=167) (base:=SynergyHeightC.FullMainFrame.base total 167) (input:=SourceMainFramesV1.Point0167.input) (pair:=SourceMainFramesV1.Point0167.outputs) SourceMainFramesV1.Point0167.input_defined SourceMainFramesV1.Point0167.outputs_defined (SourceMainFramesV1.Point0167.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=168) (base:=SynergyHeightC.FullMainFrame.base total 168) (input:=SourceMainFramesV1.Point0168.input) (pair:=SourceMainFramesV1.Point0168.outputs) SourceMainFramesV1.Point0168.input_defined SourceMainFramesV1.Point0168.outputs_defined (SourceMainFramesV1.Point0168.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=169) (base:=SynergyHeightC.FullMainFrame.base total 169) (input:=SourceMainFramesV1.Point0169.input) (pair:=SourceMainFramesV1.Point0169.outputs) SourceMainFramesV1.Point0169.input_defined SourceMainFramesV1.Point0169.outputs_defined (SourceMainFramesV1.Point0169.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=170) (base:=SynergyHeightC.FullMainFrame.base total 170) (input:=SourceMainFramesV1.Point0170.input) (pair:=SourceMainFramesV1.Point0170.outputs) SourceMainFramesV1.Point0170.input_defined SourceMainFramesV1.Point0170.outputs_defined (SourceMainFramesV1.Point0170.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=171) (base:=SynergyHeightC.FullMainFrame.base total 171) (input:=SourceMainFramesV1.Point0171.input) (pair:=SourceMainFramesV1.Point0171.outputs) SourceMainFramesV1.Point0171.input_defined SourceMainFramesV1.Point0171.outputs_defined (SourceMainFramesV1.Point0171.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=172) (base:=SynergyHeightC.FullMainFrame.base total 172) (input:=SourceMainFramesV1.Point0172.input) (pair:=SourceMainFramesV1.Point0172.outputs) SourceMainFramesV1.Point0172.input_defined SourceMainFramesV1.Point0172.outputs_defined (SourceMainFramesV1.Point0172.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=173) (base:=SynergyHeightC.FullMainFrame.base total 173) (input:=SourceMainFramesV1.Point0173.input) (pair:=SourceMainFramesV1.Point0173.outputs) SourceMainFramesV1.Point0173.input_defined SourceMainFramesV1.Point0173.outputs_defined (SourceMainFramesV1.Point0173.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=174) (base:=SynergyHeightC.FullMainFrame.base total 174) (input:=SourceMainFramesV1.Point0174.input) (pair:=SourceMainFramesV1.Point0174.outputs) SourceMainFramesV1.Point0174.input_defined SourceMainFramesV1.Point0174.outputs_defined (SourceMainFramesV1.Point0174.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=175) (base:=SynergyHeightC.FullMainFrame.base total 175) (input:=SourceMainFramesV1.Point0175.input) (pair:=SourceMainFramesV1.Point0175.outputs) SourceMainFramesV1.Point0175.input_defined SourceMainFramesV1.Point0175.outputs_defined (SourceMainFramesV1.Point0175.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=176) (base:=SynergyHeightC.FullMainFrame.base total 176) (input:=SourceMainFramesV1.Point0176.input) (pair:=SourceMainFramesV1.Point0176.outputs) SourceMainFramesV1.Point0176.input_defined SourceMainFramesV1.Point0176.outputs_defined (SourceMainFramesV1.Point0176.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=177) (base:=SynergyHeightC.FullMainFrame.base total 177) (input:=SourceMainFramesV1.Point0177.input) (pair:=SourceMainFramesV1.Point0177.outputs) SourceMainFramesV1.Point0177.input_defined SourceMainFramesV1.Point0177.outputs_defined (SourceMainFramesV1.Point0177.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=178) (base:=SynergyHeightC.FullMainFrame.base total 178) (input:=SourceMainFramesV1.Point0178.input) (pair:=SourceMainFramesV1.Point0178.outputs) SourceMainFramesV1.Point0178.input_defined SourceMainFramesV1.Point0178.outputs_defined (SourceMainFramesV1.Point0178.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=179) (base:=SynergyHeightC.FullMainFrame.base total 179) (input:=SourceMainFramesV1.Point0179.input) (pair:=SourceMainFramesV1.Point0179.outputs) SourceMainFramesV1.Point0179.input_defined SourceMainFramesV1.Point0179.outputs_defined (SourceMainFramesV1.Point0179.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=180) (base:=SynergyHeightC.FullMainFrame.base total 180) (input:=SourceMainFramesV1.Point0180.input) (pair:=SourceMainFramesV1.Point0180.outputs) SourceMainFramesV1.Point0180.input_defined SourceMainFramesV1.Point0180.outputs_defined (SourceMainFramesV1.Point0180.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=181) (base:=SynergyHeightC.FullMainFrame.base total 181) (input:=SourceMainFramesV1.Point0181.input) (pair:=SourceMainFramesV1.Point0181.outputs) SourceMainFramesV1.Point0181.input_defined SourceMainFramesV1.Point0181.outputs_defined (SourceMainFramesV1.Point0181.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=182) (base:=SynergyHeightC.FullMainFrame.base total 182) (input:=SourceMainFramesV1.Point0182.input) (pair:=SourceMainFramesV1.Point0182.outputs) SourceMainFramesV1.Point0182.input_defined SourceMainFramesV1.Point0182.outputs_defined (SourceMainFramesV1.Point0182.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=183) (base:=SynergyHeightC.FullMainFrame.base total 183) (input:=SourceMainFramesV1.Point0183.input) (pair:=SourceMainFramesV1.Point0183.outputs) SourceMainFramesV1.Point0183.input_defined SourceMainFramesV1.Point0183.outputs_defined (SourceMainFramesV1.Point0183.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=184) (base:=SynergyHeightC.FullMainFrame.base total 184) (input:=SourceMainFramesV1.Point0184.input) (pair:=SourceMainFramesV1.Point0184.outputs) SourceMainFramesV1.Point0184.input_defined SourceMainFramesV1.Point0184.outputs_defined (SourceMainFramesV1.Point0184.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=185) (base:=SynergyHeightC.FullMainFrame.base total 185) (input:=SourceMainFramesV1.Point0185.input) (pair:=SourceMainFramesV1.Point0185.outputs) SourceMainFramesV1.Point0185.input_defined SourceMainFramesV1.Point0185.outputs_defined (SourceMainFramesV1.Point0185.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=186) (base:=SynergyHeightC.FullMainFrame.base total 186) (input:=SourceMainFramesV1.Point0186.input) (pair:=SourceMainFramesV1.Point0186.outputs) SourceMainFramesV1.Point0186.input_defined SourceMainFramesV1.Point0186.outputs_defined (SourceMainFramesV1.Point0186.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=187) (base:=SynergyHeightC.FullMainFrame.base total 187) (input:=SourceMainFramesV1.Point0187.input) (pair:=SourceMainFramesV1.Point0187.outputs) SourceMainFramesV1.Point0187.input_defined SourceMainFramesV1.Point0187.outputs_defined (SourceMainFramesV1.Point0187.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=188) (base:=SynergyHeightC.FullMainFrame.base total 188) (input:=SourceMainFramesV1.Point0188.input) (pair:=SourceMainFramesV1.Point0188.outputs) SourceMainFramesV1.Point0188.input_defined SourceMainFramesV1.Point0188.outputs_defined (SourceMainFramesV1.Point0188.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=189) (base:=SynergyHeightC.FullMainFrame.base total 189) (input:=SourceMainFramesV1.Point0189.input) (pair:=SourceMainFramesV1.Point0189.outputs) SourceMainFramesV1.Point0189.input_defined SourceMainFramesV1.Point0189.outputs_defined (SourceMainFramesV1.Point0189.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=190) (base:=SynergyHeightC.FullMainFrame.base total 190) (input:=SourceMainFramesV1.Point0190.input) (pair:=SourceMainFramesV1.Point0190.outputs) SourceMainFramesV1.Point0190.input_defined SourceMainFramesV1.Point0190.outputs_defined (SourceMainFramesV1.Point0190.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=191) (base:=SynergyHeightC.FullMainFrame.base total 191) (input:=SourceMainFramesV1.Point0191.input) (pair:=SourceMainFramesV1.Point0191.outputs) SourceMainFramesV1.Point0191.input_defined SourceMainFramesV1.Point0191.outputs_defined (SourceMainFramesV1.Point0191.source_outputs total)
end SourceMainFramesV1.Block05
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Block05.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
