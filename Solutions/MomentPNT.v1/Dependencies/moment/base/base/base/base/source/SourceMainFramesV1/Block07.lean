import SourceMainFramesV1.Point0224
import SourceMainFramesV1.Point0225
import SourceMainFramesV1.Point0226
import SourceMainFramesV1.Point0227
import SourceMainFramesV1.Point0228
import SourceMainFramesV1.Point0229
import SourceMainFramesV1.Point0230
import SourceMainFramesV1.Point0231
import SourceMainFramesV1.Point0232
import SourceMainFramesV1.Point0233
import SourceMainFramesV1.Point0234
import SourceMainFramesV1.Point0235
import SourceMainFramesV1.Point0236
import SourceMainFramesV1.Point0237
import SourceMainFramesV1.Point0238
import SourceMainFramesV1.Point0239
import SourceMainFramesV1.Point0240
import SourceMainFramesV1.Point0241
import SourceMainFramesV1.Point0242
import SourceMainFramesV1.Point0243
import SourceMainFramesV1.Point0244
import SourceMainFramesV1.Point0245
import SourceMainFramesV1.Point0246
import SourceMainFramesV1.Point0247
import SourceMainFramesV1.Point0248
import SourceMainFramesV1.Point0249
import SourceMainFramesV1.Point0250
import SourceMainFramesV1.Point0251
import SourceMainFramesV1.Point0252
import SourceMainFramesV1.Point0253
import SourceMainFramesV1.Point0254
import SourceMainFramesV1.Point0255
import SourceMainFramesV1.PackOutput
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Block07
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (total : ProofBox) (i : ℕ) (lower : 224 ≤ i) (upper : i < 256) :
 ∃ base input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs base input c d := by
 interval_cases i
 · exact SourceMainFramesV1.pack_output (i:=224) (base:=SynergyHeightC.FullMainFrame.base total 224) (input:=SourceMainFramesV1.Point0224.input) (pair:=SourceMainFramesV1.Point0224.outputs) SourceMainFramesV1.Point0224.input_defined SourceMainFramesV1.Point0224.outputs_defined (SourceMainFramesV1.Point0224.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=225) (base:=SynergyHeightC.FullMainFrame.base total 225) (input:=SourceMainFramesV1.Point0225.input) (pair:=SourceMainFramesV1.Point0225.outputs) SourceMainFramesV1.Point0225.input_defined SourceMainFramesV1.Point0225.outputs_defined (SourceMainFramesV1.Point0225.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=226) (base:=SynergyHeightC.FullMainFrame.base total 226) (input:=SourceMainFramesV1.Point0226.input) (pair:=SourceMainFramesV1.Point0226.outputs) SourceMainFramesV1.Point0226.input_defined SourceMainFramesV1.Point0226.outputs_defined (SourceMainFramesV1.Point0226.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=227) (base:=SynergyHeightC.FullMainFrame.base total 227) (input:=SourceMainFramesV1.Point0227.input) (pair:=SourceMainFramesV1.Point0227.outputs) SourceMainFramesV1.Point0227.input_defined SourceMainFramesV1.Point0227.outputs_defined (SourceMainFramesV1.Point0227.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=228) (base:=SynergyHeightC.FullMainFrame.base total 228) (input:=SourceMainFramesV1.Point0228.input) (pair:=SourceMainFramesV1.Point0228.outputs) SourceMainFramesV1.Point0228.input_defined SourceMainFramesV1.Point0228.outputs_defined (SourceMainFramesV1.Point0228.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=229) (base:=SynergyHeightC.FullMainFrame.base total 229) (input:=SourceMainFramesV1.Point0229.input) (pair:=SourceMainFramesV1.Point0229.outputs) SourceMainFramesV1.Point0229.input_defined SourceMainFramesV1.Point0229.outputs_defined (SourceMainFramesV1.Point0229.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=230) (base:=SynergyHeightC.FullMainFrame.base total 230) (input:=SourceMainFramesV1.Point0230.input) (pair:=SourceMainFramesV1.Point0230.outputs) SourceMainFramesV1.Point0230.input_defined SourceMainFramesV1.Point0230.outputs_defined (SourceMainFramesV1.Point0230.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=231) (base:=SynergyHeightC.FullMainFrame.base total 231) (input:=SourceMainFramesV1.Point0231.input) (pair:=SourceMainFramesV1.Point0231.outputs) SourceMainFramesV1.Point0231.input_defined SourceMainFramesV1.Point0231.outputs_defined (SourceMainFramesV1.Point0231.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=232) (base:=SynergyHeightC.FullMainFrame.base total 232) (input:=SourceMainFramesV1.Point0232.input) (pair:=SourceMainFramesV1.Point0232.outputs) SourceMainFramesV1.Point0232.input_defined SourceMainFramesV1.Point0232.outputs_defined (SourceMainFramesV1.Point0232.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=233) (base:=SynergyHeightC.FullMainFrame.base total 233) (input:=SourceMainFramesV1.Point0233.input) (pair:=SourceMainFramesV1.Point0233.outputs) SourceMainFramesV1.Point0233.input_defined SourceMainFramesV1.Point0233.outputs_defined (SourceMainFramesV1.Point0233.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=234) (base:=SynergyHeightC.FullMainFrame.base total 234) (input:=SourceMainFramesV1.Point0234.input) (pair:=SourceMainFramesV1.Point0234.outputs) SourceMainFramesV1.Point0234.input_defined SourceMainFramesV1.Point0234.outputs_defined (SourceMainFramesV1.Point0234.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=235) (base:=SynergyHeightC.FullMainFrame.base total 235) (input:=SourceMainFramesV1.Point0235.input) (pair:=SourceMainFramesV1.Point0235.outputs) SourceMainFramesV1.Point0235.input_defined SourceMainFramesV1.Point0235.outputs_defined (SourceMainFramesV1.Point0235.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=236) (base:=SynergyHeightC.FullMainFrame.base total 236) (input:=SourceMainFramesV1.Point0236.input) (pair:=SourceMainFramesV1.Point0236.outputs) SourceMainFramesV1.Point0236.input_defined SourceMainFramesV1.Point0236.outputs_defined (SourceMainFramesV1.Point0236.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=237) (base:=SynergyHeightC.FullMainFrame.base total 237) (input:=SourceMainFramesV1.Point0237.input) (pair:=SourceMainFramesV1.Point0237.outputs) SourceMainFramesV1.Point0237.input_defined SourceMainFramesV1.Point0237.outputs_defined (SourceMainFramesV1.Point0237.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=238) (base:=SynergyHeightC.FullMainFrame.base total 238) (input:=SourceMainFramesV1.Point0238.input) (pair:=SourceMainFramesV1.Point0238.outputs) SourceMainFramesV1.Point0238.input_defined SourceMainFramesV1.Point0238.outputs_defined (SourceMainFramesV1.Point0238.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=239) (base:=SynergyHeightC.FullMainFrame.base total 239) (input:=SourceMainFramesV1.Point0239.input) (pair:=SourceMainFramesV1.Point0239.outputs) SourceMainFramesV1.Point0239.input_defined SourceMainFramesV1.Point0239.outputs_defined (SourceMainFramesV1.Point0239.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=240) (base:=SynergyHeightC.FullMainFrame.base total 240) (input:=SourceMainFramesV1.Point0240.input) (pair:=SourceMainFramesV1.Point0240.outputs) SourceMainFramesV1.Point0240.input_defined SourceMainFramesV1.Point0240.outputs_defined (SourceMainFramesV1.Point0240.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=241) (base:=SynergyHeightC.FullMainFrame.base total 241) (input:=SourceMainFramesV1.Point0241.input) (pair:=SourceMainFramesV1.Point0241.outputs) SourceMainFramesV1.Point0241.input_defined SourceMainFramesV1.Point0241.outputs_defined (SourceMainFramesV1.Point0241.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=242) (base:=SynergyHeightC.FullMainFrame.base total 242) (input:=SourceMainFramesV1.Point0242.input) (pair:=SourceMainFramesV1.Point0242.outputs) SourceMainFramesV1.Point0242.input_defined SourceMainFramesV1.Point0242.outputs_defined (SourceMainFramesV1.Point0242.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=243) (base:=SynergyHeightC.FullMainFrame.base total 243) (input:=SourceMainFramesV1.Point0243.input) (pair:=SourceMainFramesV1.Point0243.outputs) SourceMainFramesV1.Point0243.input_defined SourceMainFramesV1.Point0243.outputs_defined (SourceMainFramesV1.Point0243.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=244) (base:=SynergyHeightC.FullMainFrame.base total 244) (input:=SourceMainFramesV1.Point0244.input) (pair:=SourceMainFramesV1.Point0244.outputs) SourceMainFramesV1.Point0244.input_defined SourceMainFramesV1.Point0244.outputs_defined (SourceMainFramesV1.Point0244.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=245) (base:=SynergyHeightC.FullMainFrame.base total 245) (input:=SourceMainFramesV1.Point0245.input) (pair:=SourceMainFramesV1.Point0245.outputs) SourceMainFramesV1.Point0245.input_defined SourceMainFramesV1.Point0245.outputs_defined (SourceMainFramesV1.Point0245.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=246) (base:=SynergyHeightC.FullMainFrame.base total 246) (input:=SourceMainFramesV1.Point0246.input) (pair:=SourceMainFramesV1.Point0246.outputs) SourceMainFramesV1.Point0246.input_defined SourceMainFramesV1.Point0246.outputs_defined (SourceMainFramesV1.Point0246.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=247) (base:=SynergyHeightC.FullMainFrame.base total 247) (input:=SourceMainFramesV1.Point0247.input) (pair:=SourceMainFramesV1.Point0247.outputs) SourceMainFramesV1.Point0247.input_defined SourceMainFramesV1.Point0247.outputs_defined (SourceMainFramesV1.Point0247.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=248) (base:=SynergyHeightC.FullMainFrame.base total 248) (input:=SourceMainFramesV1.Point0248.input) (pair:=SourceMainFramesV1.Point0248.outputs) SourceMainFramesV1.Point0248.input_defined SourceMainFramesV1.Point0248.outputs_defined (SourceMainFramesV1.Point0248.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=249) (base:=SynergyHeightC.FullMainFrame.base total 249) (input:=SourceMainFramesV1.Point0249.input) (pair:=SourceMainFramesV1.Point0249.outputs) SourceMainFramesV1.Point0249.input_defined SourceMainFramesV1.Point0249.outputs_defined (SourceMainFramesV1.Point0249.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=250) (base:=SynergyHeightC.FullMainFrame.base total 250) (input:=SourceMainFramesV1.Point0250.input) (pair:=SourceMainFramesV1.Point0250.outputs) SourceMainFramesV1.Point0250.input_defined SourceMainFramesV1.Point0250.outputs_defined (SourceMainFramesV1.Point0250.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=251) (base:=SynergyHeightC.FullMainFrame.base total 251) (input:=SourceMainFramesV1.Point0251.input) (pair:=SourceMainFramesV1.Point0251.outputs) SourceMainFramesV1.Point0251.input_defined SourceMainFramesV1.Point0251.outputs_defined (SourceMainFramesV1.Point0251.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=252) (base:=SynergyHeightC.FullMainFrame.base total 252) (input:=SourceMainFramesV1.Point0252.input) (pair:=SourceMainFramesV1.Point0252.outputs) SourceMainFramesV1.Point0252.input_defined SourceMainFramesV1.Point0252.outputs_defined (SourceMainFramesV1.Point0252.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=253) (base:=SynergyHeightC.FullMainFrame.base total 253) (input:=SourceMainFramesV1.Point0253.input) (pair:=SourceMainFramesV1.Point0253.outputs) SourceMainFramesV1.Point0253.input_defined SourceMainFramesV1.Point0253.outputs_defined (SourceMainFramesV1.Point0253.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=254) (base:=SynergyHeightC.FullMainFrame.base total 254) (input:=SourceMainFramesV1.Point0254.input) (pair:=SourceMainFramesV1.Point0254.outputs) SourceMainFramesV1.Point0254.input_defined SourceMainFramesV1.Point0254.outputs_defined (SourceMainFramesV1.Point0254.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=255) (base:=SynergyHeightC.FullMainFrame.base total 255) (input:=SourceMainFramesV1.Point0255.input) (pair:=SourceMainFramesV1.Point0255.outputs) SourceMainFramesV1.Point0255.input_defined SourceMainFramesV1.Point0255.outputs_defined (SourceMainFramesV1.Point0255.source_outputs total)
end SourceMainFramesV1.Block07
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Block07.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
