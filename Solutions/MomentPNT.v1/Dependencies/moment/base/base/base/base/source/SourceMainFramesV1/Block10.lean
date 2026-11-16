import SourceMainFramesV1.Point0320
import SourceMainFramesV1.Point0321
import SourceMainFramesV1.Point0322
import SourceMainFramesV1.Point0323
import SourceMainFramesV1.Point0324
import SourceMainFramesV1.Point0325
import SourceMainFramesV1.Point0326
import SourceMainFramesV1.Point0327
import SourceMainFramesV1.Point0328
import SourceMainFramesV1.Point0329
import SourceMainFramesV1.Point0330
import SourceMainFramesV1.Point0331
import SourceMainFramesV1.Point0332
import SourceMainFramesV1.Point0333
import SourceMainFramesV1.Point0334
import SourceMainFramesV1.Point0335
import SourceMainFramesV1.Point0336
import SourceMainFramesV1.Point0337
import SourceMainFramesV1.Point0338
import SourceMainFramesV1.Point0339
import SourceMainFramesV1.Point0340
import SourceMainFramesV1.Point0341
import SourceMainFramesV1.Point0342
import SourceMainFramesV1.Point0343
import SourceMainFramesV1.Point0344
import SourceMainFramesV1.Point0345
import SourceMainFramesV1.Point0346
import SourceMainFramesV1.Point0347
import SourceMainFramesV1.Point0348
import SourceMainFramesV1.Point0349
import SourceMainFramesV1.Point0350
import SourceMainFramesV1.Point0351
import SourceMainFramesV1.PackOutput
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Block10
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (total : ProofBox) (i : ℕ) (lower : 320 ≤ i) (upper : i < 352) :
 ∃ base input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs base input c d := by
 interval_cases i
 · exact SourceMainFramesV1.pack_output (i:=320) (base:=SynergyHeightC.FullMainFrame.base total 320) (input:=SourceMainFramesV1.Point0320.input) (pair:=SourceMainFramesV1.Point0320.outputs) SourceMainFramesV1.Point0320.input_defined SourceMainFramesV1.Point0320.outputs_defined (SourceMainFramesV1.Point0320.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=321) (base:=SynergyHeightC.FullMainFrame.base total 321) (input:=SourceMainFramesV1.Point0321.input) (pair:=SourceMainFramesV1.Point0321.outputs) SourceMainFramesV1.Point0321.input_defined SourceMainFramesV1.Point0321.outputs_defined (SourceMainFramesV1.Point0321.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=322) (base:=SynergyHeightC.FullMainFrame.base total 322) (input:=SourceMainFramesV1.Point0322.input) (pair:=SourceMainFramesV1.Point0322.outputs) SourceMainFramesV1.Point0322.input_defined SourceMainFramesV1.Point0322.outputs_defined (SourceMainFramesV1.Point0322.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=323) (base:=SynergyHeightC.FullMainFrame.base total 323) (input:=SourceMainFramesV1.Point0323.input) (pair:=SourceMainFramesV1.Point0323.outputs) SourceMainFramesV1.Point0323.input_defined SourceMainFramesV1.Point0323.outputs_defined (SourceMainFramesV1.Point0323.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=324) (base:=SynergyHeightC.FullMainFrame.base total 324) (input:=SourceMainFramesV1.Point0324.input) (pair:=SourceMainFramesV1.Point0324.outputs) SourceMainFramesV1.Point0324.input_defined SourceMainFramesV1.Point0324.outputs_defined (SourceMainFramesV1.Point0324.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=325) (base:=SynergyHeightC.FullMainFrame.base total 325) (input:=SourceMainFramesV1.Point0325.input) (pair:=SourceMainFramesV1.Point0325.outputs) SourceMainFramesV1.Point0325.input_defined SourceMainFramesV1.Point0325.outputs_defined (SourceMainFramesV1.Point0325.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=326) (base:=SynergyHeightC.FullMainFrame.base total 326) (input:=SourceMainFramesV1.Point0326.input) (pair:=SourceMainFramesV1.Point0326.outputs) SourceMainFramesV1.Point0326.input_defined SourceMainFramesV1.Point0326.outputs_defined (SourceMainFramesV1.Point0326.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=327) (base:=SynergyHeightC.FullMainFrame.base total 327) (input:=SourceMainFramesV1.Point0327.input) (pair:=SourceMainFramesV1.Point0327.outputs) SourceMainFramesV1.Point0327.input_defined SourceMainFramesV1.Point0327.outputs_defined (SourceMainFramesV1.Point0327.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=328) (base:=SynergyHeightC.FullMainFrame.base total 328) (input:=SourceMainFramesV1.Point0328.input) (pair:=SourceMainFramesV1.Point0328.outputs) SourceMainFramesV1.Point0328.input_defined SourceMainFramesV1.Point0328.outputs_defined (SourceMainFramesV1.Point0328.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=329) (base:=SynergyHeightC.FullMainFrame.base total 329) (input:=SourceMainFramesV1.Point0329.input) (pair:=SourceMainFramesV1.Point0329.outputs) SourceMainFramesV1.Point0329.input_defined SourceMainFramesV1.Point0329.outputs_defined (SourceMainFramesV1.Point0329.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=330) (base:=SynergyHeightC.FullMainFrame.base total 330) (input:=SourceMainFramesV1.Point0330.input) (pair:=SourceMainFramesV1.Point0330.outputs) SourceMainFramesV1.Point0330.input_defined SourceMainFramesV1.Point0330.outputs_defined (SourceMainFramesV1.Point0330.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=331) (base:=SynergyHeightC.FullMainFrame.base total 331) (input:=SourceMainFramesV1.Point0331.input) (pair:=SourceMainFramesV1.Point0331.outputs) SourceMainFramesV1.Point0331.input_defined SourceMainFramesV1.Point0331.outputs_defined (SourceMainFramesV1.Point0331.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=332) (base:=SynergyHeightC.FullMainFrame.base total 332) (input:=SourceMainFramesV1.Point0332.input) (pair:=SourceMainFramesV1.Point0332.outputs) SourceMainFramesV1.Point0332.input_defined SourceMainFramesV1.Point0332.outputs_defined (SourceMainFramesV1.Point0332.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=333) (base:=SynergyHeightC.FullMainFrame.base total 333) (input:=SourceMainFramesV1.Point0333.input) (pair:=SourceMainFramesV1.Point0333.outputs) SourceMainFramesV1.Point0333.input_defined SourceMainFramesV1.Point0333.outputs_defined (SourceMainFramesV1.Point0333.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=334) (base:=SynergyHeightC.FullMainFrame.base total 334) (input:=SourceMainFramesV1.Point0334.input) (pair:=SourceMainFramesV1.Point0334.outputs) SourceMainFramesV1.Point0334.input_defined SourceMainFramesV1.Point0334.outputs_defined (SourceMainFramesV1.Point0334.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=335) (base:=SynergyHeightC.FullMainFrame.base total 335) (input:=SourceMainFramesV1.Point0335.input) (pair:=SourceMainFramesV1.Point0335.outputs) SourceMainFramesV1.Point0335.input_defined SourceMainFramesV1.Point0335.outputs_defined (SourceMainFramesV1.Point0335.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=336) (base:=SynergyHeightC.FullMainFrame.base total 336) (input:=SourceMainFramesV1.Point0336.input) (pair:=SourceMainFramesV1.Point0336.outputs) SourceMainFramesV1.Point0336.input_defined SourceMainFramesV1.Point0336.outputs_defined (SourceMainFramesV1.Point0336.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=337) (base:=SynergyHeightC.FullMainFrame.base total 337) (input:=SourceMainFramesV1.Point0337.input) (pair:=SourceMainFramesV1.Point0337.outputs) SourceMainFramesV1.Point0337.input_defined SourceMainFramesV1.Point0337.outputs_defined (SourceMainFramesV1.Point0337.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=338) (base:=SynergyHeightC.FullMainFrame.base total 338) (input:=SourceMainFramesV1.Point0338.input) (pair:=SourceMainFramesV1.Point0338.outputs) SourceMainFramesV1.Point0338.input_defined SourceMainFramesV1.Point0338.outputs_defined (SourceMainFramesV1.Point0338.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=339) (base:=SynergyHeightC.FullMainFrame.base total 339) (input:=SourceMainFramesV1.Point0339.input) (pair:=SourceMainFramesV1.Point0339.outputs) SourceMainFramesV1.Point0339.input_defined SourceMainFramesV1.Point0339.outputs_defined (SourceMainFramesV1.Point0339.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=340) (base:=SynergyHeightC.FullMainFrame.base total 340) (input:=SourceMainFramesV1.Point0340.input) (pair:=SourceMainFramesV1.Point0340.outputs) SourceMainFramesV1.Point0340.input_defined SourceMainFramesV1.Point0340.outputs_defined (SourceMainFramesV1.Point0340.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=341) (base:=SynergyHeightC.FullMainFrame.base total 341) (input:=SourceMainFramesV1.Point0341.input) (pair:=SourceMainFramesV1.Point0341.outputs) SourceMainFramesV1.Point0341.input_defined SourceMainFramesV1.Point0341.outputs_defined (SourceMainFramesV1.Point0341.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=342) (base:=SynergyHeightC.FullMainFrame.base total 342) (input:=SourceMainFramesV1.Point0342.input) (pair:=SourceMainFramesV1.Point0342.outputs) SourceMainFramesV1.Point0342.input_defined SourceMainFramesV1.Point0342.outputs_defined (SourceMainFramesV1.Point0342.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=343) (base:=SynergyHeightC.FullMainFrame.base total 343) (input:=SourceMainFramesV1.Point0343.input) (pair:=SourceMainFramesV1.Point0343.outputs) SourceMainFramesV1.Point0343.input_defined SourceMainFramesV1.Point0343.outputs_defined (SourceMainFramesV1.Point0343.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=344) (base:=SynergyHeightC.FullMainFrame.base total 344) (input:=SourceMainFramesV1.Point0344.input) (pair:=SourceMainFramesV1.Point0344.outputs) SourceMainFramesV1.Point0344.input_defined SourceMainFramesV1.Point0344.outputs_defined (SourceMainFramesV1.Point0344.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=345) (base:=SynergyHeightC.FullMainFrame.base total 345) (input:=SourceMainFramesV1.Point0345.input) (pair:=SourceMainFramesV1.Point0345.outputs) SourceMainFramesV1.Point0345.input_defined SourceMainFramesV1.Point0345.outputs_defined (SourceMainFramesV1.Point0345.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=346) (base:=SynergyHeightC.FullMainFrame.base total 346) (input:=SourceMainFramesV1.Point0346.input) (pair:=SourceMainFramesV1.Point0346.outputs) SourceMainFramesV1.Point0346.input_defined SourceMainFramesV1.Point0346.outputs_defined (SourceMainFramesV1.Point0346.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=347) (base:=SynergyHeightC.FullMainFrame.base total 347) (input:=SourceMainFramesV1.Point0347.input) (pair:=SourceMainFramesV1.Point0347.outputs) SourceMainFramesV1.Point0347.input_defined SourceMainFramesV1.Point0347.outputs_defined (SourceMainFramesV1.Point0347.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=348) (base:=SynergyHeightC.FullMainFrame.base total 348) (input:=SourceMainFramesV1.Point0348.input) (pair:=SourceMainFramesV1.Point0348.outputs) SourceMainFramesV1.Point0348.input_defined SourceMainFramesV1.Point0348.outputs_defined (SourceMainFramesV1.Point0348.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=349) (base:=SynergyHeightC.FullMainFrame.base total 349) (input:=SourceMainFramesV1.Point0349.input) (pair:=SourceMainFramesV1.Point0349.outputs) SourceMainFramesV1.Point0349.input_defined SourceMainFramesV1.Point0349.outputs_defined (SourceMainFramesV1.Point0349.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=350) (base:=SynergyHeightC.FullMainFrame.base total 350) (input:=SourceMainFramesV1.Point0350.input) (pair:=SourceMainFramesV1.Point0350.outputs) SourceMainFramesV1.Point0350.input_defined SourceMainFramesV1.Point0350.outputs_defined (SourceMainFramesV1.Point0350.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=351) (base:=SynergyHeightC.FullMainFrame.base total 351) (input:=SourceMainFramesV1.Point0351.input) (pair:=SourceMainFramesV1.Point0351.outputs) SourceMainFramesV1.Point0351.input_defined SourceMainFramesV1.Point0351.outputs_defined (SourceMainFramesV1.Point0351.source_outputs total)
end SourceMainFramesV1.Block10
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Block10.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
