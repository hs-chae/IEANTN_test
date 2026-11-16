import SourceMainFramesV1.Point0192
import SourceMainFramesV1.Point0193
import SourceMainFramesV1.Point0194
import SourceMainFramesV1.Point0195
import SourceMainFramesV1.Point0196
import SourceMainFramesV1.Point0197
import SourceMainFramesV1.Point0198
import SourceMainFramesV1.Point0199
import SourceMainFramesV1.Point0200
import SourceMainFramesV1.Point0201
import SourceMainFramesV1.Point0202
import SourceMainFramesV1.Point0203
import SourceMainFramesV1.Point0204
import SourceMainFramesV1.Point0205
import SourceMainFramesV1.Point0206
import SourceMainFramesV1.Point0207
import SourceMainFramesV1.Point0208
import SourceMainFramesV1.Point0209
import SourceMainFramesV1.Point0210
import SourceMainFramesV1.Point0211
import SourceMainFramesV1.Point0212
import SourceMainFramesV1.Point0213
import SourceMainFramesV1.Point0214
import SourceMainFramesV1.Point0215
import SourceMainFramesV1.Point0216
import SourceMainFramesV1.Point0217
import SourceMainFramesV1.Point0218
import SourceMainFramesV1.Point0219
import SourceMainFramesV1.Point0220
import SourceMainFramesV1.Point0221
import SourceMainFramesV1.Point0222
import SourceMainFramesV1.Point0223
import SourceMainFramesV1.PackOutput
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Block06
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (total : ProofBox) (i : ℕ) (lower : 192 ≤ i) (upper : i < 224) :
 ∃ base input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs base input c d := by
 interval_cases i
 · exact SourceMainFramesV1.pack_output (i:=192) (base:=SynergyHeightC.FullMainFrame.base total 192) (input:=SourceMainFramesV1.Point0192.input) (pair:=SourceMainFramesV1.Point0192.outputs) SourceMainFramesV1.Point0192.input_defined SourceMainFramesV1.Point0192.outputs_defined (SourceMainFramesV1.Point0192.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=193) (base:=SynergyHeightC.FullMainFrame.base total 193) (input:=SourceMainFramesV1.Point0193.input) (pair:=SourceMainFramesV1.Point0193.outputs) SourceMainFramesV1.Point0193.input_defined SourceMainFramesV1.Point0193.outputs_defined (SourceMainFramesV1.Point0193.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=194) (base:=SynergyHeightC.FullMainFrame.base total 194) (input:=SourceMainFramesV1.Point0194.input) (pair:=SourceMainFramesV1.Point0194.outputs) SourceMainFramesV1.Point0194.input_defined SourceMainFramesV1.Point0194.outputs_defined (SourceMainFramesV1.Point0194.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=195) (base:=SynergyHeightC.FullMainFrame.base total 195) (input:=SourceMainFramesV1.Point0195.input) (pair:=SourceMainFramesV1.Point0195.outputs) SourceMainFramesV1.Point0195.input_defined SourceMainFramesV1.Point0195.outputs_defined (SourceMainFramesV1.Point0195.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=196) (base:=SynergyHeightC.FullMainFrame.base total 196) (input:=SourceMainFramesV1.Point0196.input) (pair:=SourceMainFramesV1.Point0196.outputs) SourceMainFramesV1.Point0196.input_defined SourceMainFramesV1.Point0196.outputs_defined (SourceMainFramesV1.Point0196.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=197) (base:=SynergyHeightC.FullMainFrame.base total 197) (input:=SourceMainFramesV1.Point0197.input) (pair:=SourceMainFramesV1.Point0197.outputs) SourceMainFramesV1.Point0197.input_defined SourceMainFramesV1.Point0197.outputs_defined (SourceMainFramesV1.Point0197.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=198) (base:=SynergyHeightC.FullMainFrame.base total 198) (input:=SourceMainFramesV1.Point0198.input) (pair:=SourceMainFramesV1.Point0198.outputs) SourceMainFramesV1.Point0198.input_defined SourceMainFramesV1.Point0198.outputs_defined (SourceMainFramesV1.Point0198.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=199) (base:=SynergyHeightC.FullMainFrame.base total 199) (input:=SourceMainFramesV1.Point0199.input) (pair:=SourceMainFramesV1.Point0199.outputs) SourceMainFramesV1.Point0199.input_defined SourceMainFramesV1.Point0199.outputs_defined (SourceMainFramesV1.Point0199.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=200) (base:=SynergyHeightC.FullMainFrame.base total 200) (input:=SourceMainFramesV1.Point0200.input) (pair:=SourceMainFramesV1.Point0200.outputs) SourceMainFramesV1.Point0200.input_defined SourceMainFramesV1.Point0200.outputs_defined (SourceMainFramesV1.Point0200.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=201) (base:=SynergyHeightC.FullMainFrame.base total 201) (input:=SourceMainFramesV1.Point0201.input) (pair:=SourceMainFramesV1.Point0201.outputs) SourceMainFramesV1.Point0201.input_defined SourceMainFramesV1.Point0201.outputs_defined (SourceMainFramesV1.Point0201.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=202) (base:=SynergyHeightC.FullMainFrame.base total 202) (input:=SourceMainFramesV1.Point0202.input) (pair:=SourceMainFramesV1.Point0202.outputs) SourceMainFramesV1.Point0202.input_defined SourceMainFramesV1.Point0202.outputs_defined (SourceMainFramesV1.Point0202.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=203) (base:=SynergyHeightC.FullMainFrame.base total 203) (input:=SourceMainFramesV1.Point0203.input) (pair:=SourceMainFramesV1.Point0203.outputs) SourceMainFramesV1.Point0203.input_defined SourceMainFramesV1.Point0203.outputs_defined (SourceMainFramesV1.Point0203.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=204) (base:=SynergyHeightC.FullMainFrame.base total 204) (input:=SourceMainFramesV1.Point0204.input) (pair:=SourceMainFramesV1.Point0204.outputs) SourceMainFramesV1.Point0204.input_defined SourceMainFramesV1.Point0204.outputs_defined (SourceMainFramesV1.Point0204.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=205) (base:=SynergyHeightC.FullMainFrame.base total 205) (input:=SourceMainFramesV1.Point0205.input) (pair:=SourceMainFramesV1.Point0205.outputs) SourceMainFramesV1.Point0205.input_defined SourceMainFramesV1.Point0205.outputs_defined (SourceMainFramesV1.Point0205.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=206) (base:=SynergyHeightC.FullMainFrame.base total 206) (input:=SourceMainFramesV1.Point0206.input) (pair:=SourceMainFramesV1.Point0206.outputs) SourceMainFramesV1.Point0206.input_defined SourceMainFramesV1.Point0206.outputs_defined (SourceMainFramesV1.Point0206.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=207) (base:=SynergyHeightC.FullMainFrame.base total 207) (input:=SourceMainFramesV1.Point0207.input) (pair:=SourceMainFramesV1.Point0207.outputs) SourceMainFramesV1.Point0207.input_defined SourceMainFramesV1.Point0207.outputs_defined (SourceMainFramesV1.Point0207.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=208) (base:=SynergyHeightC.FullMainFrame.base total 208) (input:=SourceMainFramesV1.Point0208.input) (pair:=SourceMainFramesV1.Point0208.outputs) SourceMainFramesV1.Point0208.input_defined SourceMainFramesV1.Point0208.outputs_defined (SourceMainFramesV1.Point0208.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=209) (base:=SynergyHeightC.FullMainFrame.base total 209) (input:=SourceMainFramesV1.Point0209.input) (pair:=SourceMainFramesV1.Point0209.outputs) SourceMainFramesV1.Point0209.input_defined SourceMainFramesV1.Point0209.outputs_defined (SourceMainFramesV1.Point0209.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=210) (base:=SynergyHeightC.FullMainFrame.base total 210) (input:=SourceMainFramesV1.Point0210.input) (pair:=SourceMainFramesV1.Point0210.outputs) SourceMainFramesV1.Point0210.input_defined SourceMainFramesV1.Point0210.outputs_defined (SourceMainFramesV1.Point0210.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=211) (base:=SynergyHeightC.FullMainFrame.base total 211) (input:=SourceMainFramesV1.Point0211.input) (pair:=SourceMainFramesV1.Point0211.outputs) SourceMainFramesV1.Point0211.input_defined SourceMainFramesV1.Point0211.outputs_defined (SourceMainFramesV1.Point0211.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=212) (base:=SynergyHeightC.FullMainFrame.base total 212) (input:=SourceMainFramesV1.Point0212.input) (pair:=SourceMainFramesV1.Point0212.outputs) SourceMainFramesV1.Point0212.input_defined SourceMainFramesV1.Point0212.outputs_defined (SourceMainFramesV1.Point0212.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=213) (base:=SynergyHeightC.FullMainFrame.base total 213) (input:=SourceMainFramesV1.Point0213.input) (pair:=SourceMainFramesV1.Point0213.outputs) SourceMainFramesV1.Point0213.input_defined SourceMainFramesV1.Point0213.outputs_defined (SourceMainFramesV1.Point0213.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=214) (base:=SynergyHeightC.FullMainFrame.base total 214) (input:=SourceMainFramesV1.Point0214.input) (pair:=SourceMainFramesV1.Point0214.outputs) SourceMainFramesV1.Point0214.input_defined SourceMainFramesV1.Point0214.outputs_defined (SourceMainFramesV1.Point0214.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=215) (base:=SynergyHeightC.FullMainFrame.base total 215) (input:=SourceMainFramesV1.Point0215.input) (pair:=SourceMainFramesV1.Point0215.outputs) SourceMainFramesV1.Point0215.input_defined SourceMainFramesV1.Point0215.outputs_defined (SourceMainFramesV1.Point0215.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=216) (base:=SynergyHeightC.FullMainFrame.base total 216) (input:=SourceMainFramesV1.Point0216.input) (pair:=SourceMainFramesV1.Point0216.outputs) SourceMainFramesV1.Point0216.input_defined SourceMainFramesV1.Point0216.outputs_defined (SourceMainFramesV1.Point0216.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=217) (base:=SynergyHeightC.FullMainFrame.base total 217) (input:=SourceMainFramesV1.Point0217.input) (pair:=SourceMainFramesV1.Point0217.outputs) SourceMainFramesV1.Point0217.input_defined SourceMainFramesV1.Point0217.outputs_defined (SourceMainFramesV1.Point0217.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=218) (base:=SynergyHeightC.FullMainFrame.base total 218) (input:=SourceMainFramesV1.Point0218.input) (pair:=SourceMainFramesV1.Point0218.outputs) SourceMainFramesV1.Point0218.input_defined SourceMainFramesV1.Point0218.outputs_defined (SourceMainFramesV1.Point0218.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=219) (base:=SynergyHeightC.FullMainFrame.base total 219) (input:=SourceMainFramesV1.Point0219.input) (pair:=SourceMainFramesV1.Point0219.outputs) SourceMainFramesV1.Point0219.input_defined SourceMainFramesV1.Point0219.outputs_defined (SourceMainFramesV1.Point0219.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=220) (base:=SynergyHeightC.FullMainFrame.base total 220) (input:=SourceMainFramesV1.Point0220.input) (pair:=SourceMainFramesV1.Point0220.outputs) SourceMainFramesV1.Point0220.input_defined SourceMainFramesV1.Point0220.outputs_defined (SourceMainFramesV1.Point0220.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=221) (base:=SynergyHeightC.FullMainFrame.base total 221) (input:=SourceMainFramesV1.Point0221.input) (pair:=SourceMainFramesV1.Point0221.outputs) SourceMainFramesV1.Point0221.input_defined SourceMainFramesV1.Point0221.outputs_defined (SourceMainFramesV1.Point0221.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=222) (base:=SynergyHeightC.FullMainFrame.base total 222) (input:=SourceMainFramesV1.Point0222.input) (pair:=SourceMainFramesV1.Point0222.outputs) SourceMainFramesV1.Point0222.input_defined SourceMainFramesV1.Point0222.outputs_defined (SourceMainFramesV1.Point0222.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=223) (base:=SynergyHeightC.FullMainFrame.base total 223) (input:=SourceMainFramesV1.Point0223.input) (pair:=SourceMainFramesV1.Point0223.outputs) SourceMainFramesV1.Point0223.input_defined SourceMainFramesV1.Point0223.outputs_defined (SourceMainFramesV1.Point0223.source_outputs total)
end SourceMainFramesV1.Block06
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Block06.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
