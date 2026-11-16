import SourceMainFramesV1.Point0288
import SourceMainFramesV1.Point0289
import SourceMainFramesV1.Point0290
import SourceMainFramesV1.Point0291
import SourceMainFramesV1.Point0292
import SourceMainFramesV1.Point0293
import SourceMainFramesV1.Point0294
import SourceMainFramesV1.Point0295
import SourceMainFramesV1.Point0296
import SourceMainFramesV1.Point0297
import SourceMainFramesV1.Point0298
import SourceMainFramesV1.Point0299
import SourceMainFramesV1.Point0300
import SourceMainFramesV1.Point0301
import SourceMainFramesV1.Point0302
import SourceMainFramesV1.Point0303
import SourceMainFramesV1.Point0304
import SourceMainFramesV1.Point0305
import SourceMainFramesV1.Point0306
import SourceMainFramesV1.Point0307
import SourceMainFramesV1.Point0308
import SourceMainFramesV1.Point0309
import SourceMainFramesV1.Point0310
import SourceMainFramesV1.Point0311
import SourceMainFramesV1.Point0312
import SourceMainFramesV1.Point0313
import SourceMainFramesV1.Point0314
import SourceMainFramesV1.Point0315
import SourceMainFramesV1.Point0316
import SourceMainFramesV1.Point0317
import SourceMainFramesV1.Point0318
import SourceMainFramesV1.Point0319
import SourceMainFramesV1.PackOutput
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Block09
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (total : ProofBox) (i : ℕ) (lower : 288 ≤ i) (upper : i < 320) :
 ∃ base input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs base input c d := by
 interval_cases i
 · exact SourceMainFramesV1.pack_output (i:=288) (base:=SynergyHeightC.FullMainFrame.base total 288) (input:=SourceMainFramesV1.Point0288.input) (pair:=SourceMainFramesV1.Point0288.outputs) SourceMainFramesV1.Point0288.input_defined SourceMainFramesV1.Point0288.outputs_defined (SourceMainFramesV1.Point0288.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=289) (base:=SynergyHeightC.FullMainFrame.base total 289) (input:=SourceMainFramesV1.Point0289.input) (pair:=SourceMainFramesV1.Point0289.outputs) SourceMainFramesV1.Point0289.input_defined SourceMainFramesV1.Point0289.outputs_defined (SourceMainFramesV1.Point0289.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=290) (base:=SynergyHeightC.FullMainFrame.base total 290) (input:=SourceMainFramesV1.Point0290.input) (pair:=SourceMainFramesV1.Point0290.outputs) SourceMainFramesV1.Point0290.input_defined SourceMainFramesV1.Point0290.outputs_defined (SourceMainFramesV1.Point0290.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=291) (base:=SynergyHeightC.FullMainFrame.base total 291) (input:=SourceMainFramesV1.Point0291.input) (pair:=SourceMainFramesV1.Point0291.outputs) SourceMainFramesV1.Point0291.input_defined SourceMainFramesV1.Point0291.outputs_defined (SourceMainFramesV1.Point0291.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=292) (base:=SynergyHeightC.FullMainFrame.base total 292) (input:=SourceMainFramesV1.Point0292.input) (pair:=SourceMainFramesV1.Point0292.outputs) SourceMainFramesV1.Point0292.input_defined SourceMainFramesV1.Point0292.outputs_defined (SourceMainFramesV1.Point0292.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=293) (base:=SynergyHeightC.FullMainFrame.base total 293) (input:=SourceMainFramesV1.Point0293.input) (pair:=SourceMainFramesV1.Point0293.outputs) SourceMainFramesV1.Point0293.input_defined SourceMainFramesV1.Point0293.outputs_defined (SourceMainFramesV1.Point0293.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=294) (base:=SynergyHeightC.FullMainFrame.base total 294) (input:=SourceMainFramesV1.Point0294.input) (pair:=SourceMainFramesV1.Point0294.outputs) SourceMainFramesV1.Point0294.input_defined SourceMainFramesV1.Point0294.outputs_defined (SourceMainFramesV1.Point0294.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=295) (base:=SynergyHeightC.FullMainFrame.base total 295) (input:=SourceMainFramesV1.Point0295.input) (pair:=SourceMainFramesV1.Point0295.outputs) SourceMainFramesV1.Point0295.input_defined SourceMainFramesV1.Point0295.outputs_defined (SourceMainFramesV1.Point0295.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=296) (base:=SynergyHeightC.FullMainFrame.base total 296) (input:=SourceMainFramesV1.Point0296.input) (pair:=SourceMainFramesV1.Point0296.outputs) SourceMainFramesV1.Point0296.input_defined SourceMainFramesV1.Point0296.outputs_defined (SourceMainFramesV1.Point0296.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=297) (base:=SynergyHeightC.FullMainFrame.base total 297) (input:=SourceMainFramesV1.Point0297.input) (pair:=SourceMainFramesV1.Point0297.outputs) SourceMainFramesV1.Point0297.input_defined SourceMainFramesV1.Point0297.outputs_defined (SourceMainFramesV1.Point0297.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=298) (base:=SynergyHeightC.FullMainFrame.base total 298) (input:=SourceMainFramesV1.Point0298.input) (pair:=SourceMainFramesV1.Point0298.outputs) SourceMainFramesV1.Point0298.input_defined SourceMainFramesV1.Point0298.outputs_defined (SourceMainFramesV1.Point0298.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=299) (base:=SynergyHeightC.FullMainFrame.base total 299) (input:=SourceMainFramesV1.Point0299.input) (pair:=SourceMainFramesV1.Point0299.outputs) SourceMainFramesV1.Point0299.input_defined SourceMainFramesV1.Point0299.outputs_defined (SourceMainFramesV1.Point0299.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=300) (base:=SynergyHeightC.FullMainFrame.base total 300) (input:=SourceMainFramesV1.Point0300.input) (pair:=SourceMainFramesV1.Point0300.outputs) SourceMainFramesV1.Point0300.input_defined SourceMainFramesV1.Point0300.outputs_defined (SourceMainFramesV1.Point0300.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=301) (base:=SynergyHeightC.FullMainFrame.base total 301) (input:=SourceMainFramesV1.Point0301.input) (pair:=SourceMainFramesV1.Point0301.outputs) SourceMainFramesV1.Point0301.input_defined SourceMainFramesV1.Point0301.outputs_defined (SourceMainFramesV1.Point0301.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=302) (base:=SynergyHeightC.FullMainFrame.base total 302) (input:=SourceMainFramesV1.Point0302.input) (pair:=SourceMainFramesV1.Point0302.outputs) SourceMainFramesV1.Point0302.input_defined SourceMainFramesV1.Point0302.outputs_defined (SourceMainFramesV1.Point0302.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=303) (base:=SynergyHeightC.FullMainFrame.base total 303) (input:=SourceMainFramesV1.Point0303.input) (pair:=SourceMainFramesV1.Point0303.outputs) SourceMainFramesV1.Point0303.input_defined SourceMainFramesV1.Point0303.outputs_defined (SourceMainFramesV1.Point0303.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=304) (base:=SynergyHeightC.FullMainFrame.base total 304) (input:=SourceMainFramesV1.Point0304.input) (pair:=SourceMainFramesV1.Point0304.outputs) SourceMainFramesV1.Point0304.input_defined SourceMainFramesV1.Point0304.outputs_defined (SourceMainFramesV1.Point0304.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=305) (base:=SynergyHeightC.FullMainFrame.base total 305) (input:=SourceMainFramesV1.Point0305.input) (pair:=SourceMainFramesV1.Point0305.outputs) SourceMainFramesV1.Point0305.input_defined SourceMainFramesV1.Point0305.outputs_defined (SourceMainFramesV1.Point0305.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=306) (base:=SynergyHeightC.FullMainFrame.base total 306) (input:=SourceMainFramesV1.Point0306.input) (pair:=SourceMainFramesV1.Point0306.outputs) SourceMainFramesV1.Point0306.input_defined SourceMainFramesV1.Point0306.outputs_defined (SourceMainFramesV1.Point0306.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=307) (base:=SynergyHeightC.FullMainFrame.base total 307) (input:=SourceMainFramesV1.Point0307.input) (pair:=SourceMainFramesV1.Point0307.outputs) SourceMainFramesV1.Point0307.input_defined SourceMainFramesV1.Point0307.outputs_defined (SourceMainFramesV1.Point0307.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=308) (base:=SynergyHeightC.FullMainFrame.base total 308) (input:=SourceMainFramesV1.Point0308.input) (pair:=SourceMainFramesV1.Point0308.outputs) SourceMainFramesV1.Point0308.input_defined SourceMainFramesV1.Point0308.outputs_defined (SourceMainFramesV1.Point0308.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=309) (base:=SynergyHeightC.FullMainFrame.base total 309) (input:=SourceMainFramesV1.Point0309.input) (pair:=SourceMainFramesV1.Point0309.outputs) SourceMainFramesV1.Point0309.input_defined SourceMainFramesV1.Point0309.outputs_defined (SourceMainFramesV1.Point0309.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=310) (base:=SynergyHeightC.FullMainFrame.base total 310) (input:=SourceMainFramesV1.Point0310.input) (pair:=SourceMainFramesV1.Point0310.outputs) SourceMainFramesV1.Point0310.input_defined SourceMainFramesV1.Point0310.outputs_defined (SourceMainFramesV1.Point0310.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=311) (base:=SynergyHeightC.FullMainFrame.base total 311) (input:=SourceMainFramesV1.Point0311.input) (pair:=SourceMainFramesV1.Point0311.outputs) SourceMainFramesV1.Point0311.input_defined SourceMainFramesV1.Point0311.outputs_defined (SourceMainFramesV1.Point0311.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=312) (base:=SynergyHeightC.FullMainFrame.base total 312) (input:=SourceMainFramesV1.Point0312.input) (pair:=SourceMainFramesV1.Point0312.outputs) SourceMainFramesV1.Point0312.input_defined SourceMainFramesV1.Point0312.outputs_defined (SourceMainFramesV1.Point0312.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=313) (base:=SynergyHeightC.FullMainFrame.base total 313) (input:=SourceMainFramesV1.Point0313.input) (pair:=SourceMainFramesV1.Point0313.outputs) SourceMainFramesV1.Point0313.input_defined SourceMainFramesV1.Point0313.outputs_defined (SourceMainFramesV1.Point0313.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=314) (base:=SynergyHeightC.FullMainFrame.base total 314) (input:=SourceMainFramesV1.Point0314.input) (pair:=SourceMainFramesV1.Point0314.outputs) SourceMainFramesV1.Point0314.input_defined SourceMainFramesV1.Point0314.outputs_defined (SourceMainFramesV1.Point0314.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=315) (base:=SynergyHeightC.FullMainFrame.base total 315) (input:=SourceMainFramesV1.Point0315.input) (pair:=SourceMainFramesV1.Point0315.outputs) SourceMainFramesV1.Point0315.input_defined SourceMainFramesV1.Point0315.outputs_defined (SourceMainFramesV1.Point0315.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=316) (base:=SynergyHeightC.FullMainFrame.base total 316) (input:=SourceMainFramesV1.Point0316.input) (pair:=SourceMainFramesV1.Point0316.outputs) SourceMainFramesV1.Point0316.input_defined SourceMainFramesV1.Point0316.outputs_defined (SourceMainFramesV1.Point0316.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=317) (base:=SynergyHeightC.FullMainFrame.base total 317) (input:=SourceMainFramesV1.Point0317.input) (pair:=SourceMainFramesV1.Point0317.outputs) SourceMainFramesV1.Point0317.input_defined SourceMainFramesV1.Point0317.outputs_defined (SourceMainFramesV1.Point0317.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=318) (base:=SynergyHeightC.FullMainFrame.base total 318) (input:=SourceMainFramesV1.Point0318.input) (pair:=SourceMainFramesV1.Point0318.outputs) SourceMainFramesV1.Point0318.input_defined SourceMainFramesV1.Point0318.outputs_defined (SourceMainFramesV1.Point0318.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=319) (base:=SynergyHeightC.FullMainFrame.base total 319) (input:=SourceMainFramesV1.Point0319.input) (pair:=SourceMainFramesV1.Point0319.outputs) SourceMainFramesV1.Point0319.input_defined SourceMainFramesV1.Point0319.outputs_defined (SourceMainFramesV1.Point0319.source_outputs total)
end SourceMainFramesV1.Block09
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Block09.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
