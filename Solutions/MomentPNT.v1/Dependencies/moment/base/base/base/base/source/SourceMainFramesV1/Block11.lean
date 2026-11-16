import SourceMainFramesV1.Point0352
import SourceMainFramesV1.Point0353
import SourceMainFramesV1.Point0354
import SourceMainFramesV1.Point0355
import SourceMainFramesV1.Point0356
import SourceMainFramesV1.Point0357
import SourceMainFramesV1.Point0358
import SourceMainFramesV1.Point0359
import SourceMainFramesV1.Point0360
import SourceMainFramesV1.Point0361
import SourceMainFramesV1.Point0362
import SourceMainFramesV1.Point0363
import SourceMainFramesV1.Point0364
import SourceMainFramesV1.Point0365
import SourceMainFramesV1.Point0366
import SourceMainFramesV1.Point0367
import SourceMainFramesV1.Point0368
import SourceMainFramesV1.Point0369
import SourceMainFramesV1.Point0370
import SourceMainFramesV1.Point0371
import SourceMainFramesV1.Point0372
import SourceMainFramesV1.Point0373
import SourceMainFramesV1.Point0374
import SourceMainFramesV1.Point0375
import SourceMainFramesV1.Point0376
import SourceMainFramesV1.Point0377
import SourceMainFramesV1.Point0378
import SourceMainFramesV1.Point0379
import SourceMainFramesV1.Point0380
import SourceMainFramesV1.Point0381
import SourceMainFramesV1.Point0382
import SourceMainFramesV1.Point0383
import SourceMainFramesV1.PackOutput
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Block11
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (total : ProofBox) (i : ℕ) (lower : 352 ≤ i) (upper : i < 384) :
 ∃ base input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs base input c d := by
 interval_cases i
 · exact SourceMainFramesV1.pack_output (i:=352) (base:=SynergyHeightC.FullMainFrame.base total 352) (input:=SourceMainFramesV1.Point0352.input) (pair:=SourceMainFramesV1.Point0352.outputs) SourceMainFramesV1.Point0352.input_defined SourceMainFramesV1.Point0352.outputs_defined (SourceMainFramesV1.Point0352.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=353) (base:=SynergyHeightC.FullMainFrame.base total 353) (input:=SourceMainFramesV1.Point0353.input) (pair:=SourceMainFramesV1.Point0353.outputs) SourceMainFramesV1.Point0353.input_defined SourceMainFramesV1.Point0353.outputs_defined (SourceMainFramesV1.Point0353.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=354) (base:=SynergyHeightC.FullMainFrame.base total 354) (input:=SourceMainFramesV1.Point0354.input) (pair:=SourceMainFramesV1.Point0354.outputs) SourceMainFramesV1.Point0354.input_defined SourceMainFramesV1.Point0354.outputs_defined (SourceMainFramesV1.Point0354.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=355) (base:=SynergyHeightC.FullMainFrame.base total 355) (input:=SourceMainFramesV1.Point0355.input) (pair:=SourceMainFramesV1.Point0355.outputs) SourceMainFramesV1.Point0355.input_defined SourceMainFramesV1.Point0355.outputs_defined (SourceMainFramesV1.Point0355.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=356) (base:=SynergyHeightC.FullMainFrame.base total 356) (input:=SourceMainFramesV1.Point0356.input) (pair:=SourceMainFramesV1.Point0356.outputs) SourceMainFramesV1.Point0356.input_defined SourceMainFramesV1.Point0356.outputs_defined (SourceMainFramesV1.Point0356.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=357) (base:=SynergyHeightC.FullMainFrame.base total 357) (input:=SourceMainFramesV1.Point0357.input) (pair:=SourceMainFramesV1.Point0357.outputs) SourceMainFramesV1.Point0357.input_defined SourceMainFramesV1.Point0357.outputs_defined (SourceMainFramesV1.Point0357.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=358) (base:=SynergyHeightC.FullMainFrame.base total 358) (input:=SourceMainFramesV1.Point0358.input) (pair:=SourceMainFramesV1.Point0358.outputs) SourceMainFramesV1.Point0358.input_defined SourceMainFramesV1.Point0358.outputs_defined (SourceMainFramesV1.Point0358.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=359) (base:=SynergyHeightC.FullMainFrame.base total 359) (input:=SourceMainFramesV1.Point0359.input) (pair:=SourceMainFramesV1.Point0359.outputs) SourceMainFramesV1.Point0359.input_defined SourceMainFramesV1.Point0359.outputs_defined (SourceMainFramesV1.Point0359.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=360) (base:=SynergyHeightC.FullMainFrame.base total 360) (input:=SourceMainFramesV1.Point0360.input) (pair:=SourceMainFramesV1.Point0360.outputs) SourceMainFramesV1.Point0360.input_defined SourceMainFramesV1.Point0360.outputs_defined (SourceMainFramesV1.Point0360.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=361) (base:=SynergyHeightC.FullMainFrame.base total 361) (input:=SourceMainFramesV1.Point0361.input) (pair:=SourceMainFramesV1.Point0361.outputs) SourceMainFramesV1.Point0361.input_defined SourceMainFramesV1.Point0361.outputs_defined (SourceMainFramesV1.Point0361.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=362) (base:=SynergyHeightC.FullMainFrame.base total 362) (input:=SourceMainFramesV1.Point0362.input) (pair:=SourceMainFramesV1.Point0362.outputs) SourceMainFramesV1.Point0362.input_defined SourceMainFramesV1.Point0362.outputs_defined (SourceMainFramesV1.Point0362.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=363) (base:=SynergyHeightC.FullMainFrame.base total 363) (input:=SourceMainFramesV1.Point0363.input) (pair:=SourceMainFramesV1.Point0363.outputs) SourceMainFramesV1.Point0363.input_defined SourceMainFramesV1.Point0363.outputs_defined (SourceMainFramesV1.Point0363.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=364) (base:=SynergyHeightC.FullMainFrame.base total 364) (input:=SourceMainFramesV1.Point0364.input) (pair:=SourceMainFramesV1.Point0364.outputs) SourceMainFramesV1.Point0364.input_defined SourceMainFramesV1.Point0364.outputs_defined (SourceMainFramesV1.Point0364.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=365) (base:=SynergyHeightC.FullMainFrame.base total 365) (input:=SourceMainFramesV1.Point0365.input) (pair:=SourceMainFramesV1.Point0365.outputs) SourceMainFramesV1.Point0365.input_defined SourceMainFramesV1.Point0365.outputs_defined (SourceMainFramesV1.Point0365.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=366) (base:=SynergyHeightC.FullMainFrame.base total 366) (input:=SourceMainFramesV1.Point0366.input) (pair:=SourceMainFramesV1.Point0366.outputs) SourceMainFramesV1.Point0366.input_defined SourceMainFramesV1.Point0366.outputs_defined (SourceMainFramesV1.Point0366.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=367) (base:=SynergyHeightC.FullMainFrame.base total 367) (input:=SourceMainFramesV1.Point0367.input) (pair:=SourceMainFramesV1.Point0367.outputs) SourceMainFramesV1.Point0367.input_defined SourceMainFramesV1.Point0367.outputs_defined (SourceMainFramesV1.Point0367.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=368) (base:=SynergyHeightC.FullMainFrame.base total 368) (input:=SourceMainFramesV1.Point0368.input) (pair:=SourceMainFramesV1.Point0368.outputs) SourceMainFramesV1.Point0368.input_defined SourceMainFramesV1.Point0368.outputs_defined (SourceMainFramesV1.Point0368.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=369) (base:=SynergyHeightC.FullMainFrame.base total 369) (input:=SourceMainFramesV1.Point0369.input) (pair:=SourceMainFramesV1.Point0369.outputs) SourceMainFramesV1.Point0369.input_defined SourceMainFramesV1.Point0369.outputs_defined (SourceMainFramesV1.Point0369.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=370) (base:=SynergyHeightC.FullMainFrame.base total 370) (input:=SourceMainFramesV1.Point0370.input) (pair:=SourceMainFramesV1.Point0370.outputs) SourceMainFramesV1.Point0370.input_defined SourceMainFramesV1.Point0370.outputs_defined (SourceMainFramesV1.Point0370.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=371) (base:=SynergyHeightC.FullMainFrame.base total 371) (input:=SourceMainFramesV1.Point0371.input) (pair:=SourceMainFramesV1.Point0371.outputs) SourceMainFramesV1.Point0371.input_defined SourceMainFramesV1.Point0371.outputs_defined (SourceMainFramesV1.Point0371.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=372) (base:=SynergyHeightC.FullMainFrame.base total 372) (input:=SourceMainFramesV1.Point0372.input) (pair:=SourceMainFramesV1.Point0372.outputs) SourceMainFramesV1.Point0372.input_defined SourceMainFramesV1.Point0372.outputs_defined (SourceMainFramesV1.Point0372.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=373) (base:=SynergyHeightC.FullMainFrame.base total 373) (input:=SourceMainFramesV1.Point0373.input) (pair:=SourceMainFramesV1.Point0373.outputs) SourceMainFramesV1.Point0373.input_defined SourceMainFramesV1.Point0373.outputs_defined (SourceMainFramesV1.Point0373.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=374) (base:=SynergyHeightC.FullMainFrame.base total 374) (input:=SourceMainFramesV1.Point0374.input) (pair:=SourceMainFramesV1.Point0374.outputs) SourceMainFramesV1.Point0374.input_defined SourceMainFramesV1.Point0374.outputs_defined (SourceMainFramesV1.Point0374.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=375) (base:=SynergyHeightC.FullMainFrame.base total 375) (input:=SourceMainFramesV1.Point0375.input) (pair:=SourceMainFramesV1.Point0375.outputs) SourceMainFramesV1.Point0375.input_defined SourceMainFramesV1.Point0375.outputs_defined (SourceMainFramesV1.Point0375.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=376) (base:=SynergyHeightC.FullMainFrame.base total 376) (input:=SourceMainFramesV1.Point0376.input) (pair:=SourceMainFramesV1.Point0376.outputs) SourceMainFramesV1.Point0376.input_defined SourceMainFramesV1.Point0376.outputs_defined (SourceMainFramesV1.Point0376.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=377) (base:=SynergyHeightC.FullMainFrame.base total 377) (input:=SourceMainFramesV1.Point0377.input) (pair:=SourceMainFramesV1.Point0377.outputs) SourceMainFramesV1.Point0377.input_defined SourceMainFramesV1.Point0377.outputs_defined (SourceMainFramesV1.Point0377.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=378) (base:=SynergyHeightC.FullMainFrame.base total 378) (input:=SourceMainFramesV1.Point0378.input) (pair:=SourceMainFramesV1.Point0378.outputs) SourceMainFramesV1.Point0378.input_defined SourceMainFramesV1.Point0378.outputs_defined (SourceMainFramesV1.Point0378.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=379) (base:=SynergyHeightC.FullMainFrame.base total 379) (input:=SourceMainFramesV1.Point0379.input) (pair:=SourceMainFramesV1.Point0379.outputs) SourceMainFramesV1.Point0379.input_defined SourceMainFramesV1.Point0379.outputs_defined (SourceMainFramesV1.Point0379.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=380) (base:=SynergyHeightC.FullMainFrame.base total 380) (input:=SourceMainFramesV1.Point0380.input) (pair:=SourceMainFramesV1.Point0380.outputs) SourceMainFramesV1.Point0380.input_defined SourceMainFramesV1.Point0380.outputs_defined (SourceMainFramesV1.Point0380.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=381) (base:=SynergyHeightC.FullMainFrame.base total 381) (input:=SourceMainFramesV1.Point0381.input) (pair:=SourceMainFramesV1.Point0381.outputs) SourceMainFramesV1.Point0381.input_defined SourceMainFramesV1.Point0381.outputs_defined (SourceMainFramesV1.Point0381.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=382) (base:=SynergyHeightC.FullMainFrame.base total 382) (input:=SourceMainFramesV1.Point0382.input) (pair:=SourceMainFramesV1.Point0382.outputs) SourceMainFramesV1.Point0382.input_defined SourceMainFramesV1.Point0382.outputs_defined (SourceMainFramesV1.Point0382.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=383) (base:=SynergyHeightC.FullMainFrame.base total 383) (input:=SourceMainFramesV1.Point0383.input) (pair:=SourceMainFramesV1.Point0383.outputs) SourceMainFramesV1.Point0383.input_defined SourceMainFramesV1.Point0383.outputs_defined (SourceMainFramesV1.Point0383.source_outputs total)
end SourceMainFramesV1.Block11
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Block11.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
