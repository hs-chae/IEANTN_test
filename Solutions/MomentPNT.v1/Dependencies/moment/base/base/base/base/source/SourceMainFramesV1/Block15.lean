import SourceMainFramesV1.Point0480
import SourceMainFramesV1.Point0481
import SourceMainFramesV1.Point0482
import SourceMainFramesV1.Point0483
import SourceMainFramesV1.Point0484
import SourceMainFramesV1.Point0485
import SourceMainFramesV1.Point0486
import SourceMainFramesV1.Point0487
import SourceMainFramesV1.Point0488
import SourceMainFramesV1.Point0489
import SourceMainFramesV1.Point0490
import SourceMainFramesV1.Point0491
import SourceMainFramesV1.Point0492
import SourceMainFramesV1.Point0493
import SourceMainFramesV1.Point0494
import SourceMainFramesV1.Point0495
import SourceMainFramesV1.Point0496
import SourceMainFramesV1.Point0497
import SourceMainFramesV1.Point0498
import SourceMainFramesV1.Point0499
import SourceMainFramesV1.Point0500
import SourceMainFramesV1.Point0501
import SourceMainFramesV1.Point0502
import SourceMainFramesV1.Point0503
import SourceMainFramesV1.Point0504
import SourceMainFramesV1.Point0505
import SourceMainFramesV1.Point0506
import SourceMainFramesV1.Point0507
import SourceMainFramesV1.Point0508
import SourceMainFramesV1.Point0509
import SourceMainFramesV1.Point0510
import SourceMainFramesV1.Point0511
import SourceMainFramesV1.PackOutput
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Block15
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (total : ProofBox) (i : ℕ) (lower : 480 ≤ i) (upper : i < 512) :
 ∃ base input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs base input c d := by
 interval_cases i
 · exact SourceMainFramesV1.pack_output (i:=480) (base:=SynergyHeightC.FullMainFrame.base total 480) (input:=SourceMainFramesV1.Point0480.input) (pair:=SourceMainFramesV1.Point0480.outputs) SourceMainFramesV1.Point0480.input_defined SourceMainFramesV1.Point0480.outputs_defined (SourceMainFramesV1.Point0480.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=481) (base:=SynergyHeightC.FullMainFrame.base total 481) (input:=SourceMainFramesV1.Point0481.input) (pair:=SourceMainFramesV1.Point0481.outputs) SourceMainFramesV1.Point0481.input_defined SourceMainFramesV1.Point0481.outputs_defined (SourceMainFramesV1.Point0481.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=482) (base:=SynergyHeightC.FullMainFrame.base total 482) (input:=SourceMainFramesV1.Point0482.input) (pair:=SourceMainFramesV1.Point0482.outputs) SourceMainFramesV1.Point0482.input_defined SourceMainFramesV1.Point0482.outputs_defined (SourceMainFramesV1.Point0482.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=483) (base:=SynergyHeightC.FullMainFrame.base total 483) (input:=SourceMainFramesV1.Point0483.input) (pair:=SourceMainFramesV1.Point0483.outputs) SourceMainFramesV1.Point0483.input_defined SourceMainFramesV1.Point0483.outputs_defined (SourceMainFramesV1.Point0483.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=484) (base:=SynergyHeightC.FullMainFrame.base total 484) (input:=SourceMainFramesV1.Point0484.input) (pair:=SourceMainFramesV1.Point0484.outputs) SourceMainFramesV1.Point0484.input_defined SourceMainFramesV1.Point0484.outputs_defined (SourceMainFramesV1.Point0484.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=485) (base:=SynergyHeightC.FullMainFrame.base total 485) (input:=SourceMainFramesV1.Point0485.input) (pair:=SourceMainFramesV1.Point0485.outputs) SourceMainFramesV1.Point0485.input_defined SourceMainFramesV1.Point0485.outputs_defined (SourceMainFramesV1.Point0485.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=486) (base:=SynergyHeightC.FullMainFrame.base total 486) (input:=SourceMainFramesV1.Point0486.input) (pair:=SourceMainFramesV1.Point0486.outputs) SourceMainFramesV1.Point0486.input_defined SourceMainFramesV1.Point0486.outputs_defined (SourceMainFramesV1.Point0486.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=487) (base:=SynergyHeightC.FullMainFrame.base total 487) (input:=SourceMainFramesV1.Point0487.input) (pair:=SourceMainFramesV1.Point0487.outputs) SourceMainFramesV1.Point0487.input_defined SourceMainFramesV1.Point0487.outputs_defined (SourceMainFramesV1.Point0487.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=488) (base:=SynergyHeightC.FullMainFrame.base total 488) (input:=SourceMainFramesV1.Point0488.input) (pair:=SourceMainFramesV1.Point0488.outputs) SourceMainFramesV1.Point0488.input_defined SourceMainFramesV1.Point0488.outputs_defined (SourceMainFramesV1.Point0488.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=489) (base:=SynergyHeightC.FullMainFrame.base total 489) (input:=SourceMainFramesV1.Point0489.input) (pair:=SourceMainFramesV1.Point0489.outputs) SourceMainFramesV1.Point0489.input_defined SourceMainFramesV1.Point0489.outputs_defined (SourceMainFramesV1.Point0489.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=490) (base:=SynergyHeightC.FullMainFrame.base total 490) (input:=SourceMainFramesV1.Point0490.input) (pair:=SourceMainFramesV1.Point0490.outputs) SourceMainFramesV1.Point0490.input_defined SourceMainFramesV1.Point0490.outputs_defined (SourceMainFramesV1.Point0490.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=491) (base:=SynergyHeightC.FullMainFrame.base total 491) (input:=SourceMainFramesV1.Point0491.input) (pair:=SourceMainFramesV1.Point0491.outputs) SourceMainFramesV1.Point0491.input_defined SourceMainFramesV1.Point0491.outputs_defined (SourceMainFramesV1.Point0491.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=492) (base:=SynergyHeightC.FullMainFrame.base total 492) (input:=SourceMainFramesV1.Point0492.input) (pair:=SourceMainFramesV1.Point0492.outputs) SourceMainFramesV1.Point0492.input_defined SourceMainFramesV1.Point0492.outputs_defined (SourceMainFramesV1.Point0492.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=493) (base:=SynergyHeightC.FullMainFrame.base total 493) (input:=SourceMainFramesV1.Point0493.input) (pair:=SourceMainFramesV1.Point0493.outputs) SourceMainFramesV1.Point0493.input_defined SourceMainFramesV1.Point0493.outputs_defined (SourceMainFramesV1.Point0493.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=494) (base:=SynergyHeightC.FullMainFrame.base total 494) (input:=SourceMainFramesV1.Point0494.input) (pair:=SourceMainFramesV1.Point0494.outputs) SourceMainFramesV1.Point0494.input_defined SourceMainFramesV1.Point0494.outputs_defined (SourceMainFramesV1.Point0494.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=495) (base:=SynergyHeightC.FullMainFrame.base total 495) (input:=SourceMainFramesV1.Point0495.input) (pair:=SourceMainFramesV1.Point0495.outputs) SourceMainFramesV1.Point0495.input_defined SourceMainFramesV1.Point0495.outputs_defined (SourceMainFramesV1.Point0495.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=496) (base:=SynergyHeightC.FullMainFrame.base total 496) (input:=SourceMainFramesV1.Point0496.input) (pair:=SourceMainFramesV1.Point0496.outputs) SourceMainFramesV1.Point0496.input_defined SourceMainFramesV1.Point0496.outputs_defined (SourceMainFramesV1.Point0496.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=497) (base:=SynergyHeightC.FullMainFrame.base total 497) (input:=SourceMainFramesV1.Point0497.input) (pair:=SourceMainFramesV1.Point0497.outputs) SourceMainFramesV1.Point0497.input_defined SourceMainFramesV1.Point0497.outputs_defined (SourceMainFramesV1.Point0497.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=498) (base:=SynergyHeightC.FullMainFrame.base total 498) (input:=SourceMainFramesV1.Point0498.input) (pair:=SourceMainFramesV1.Point0498.outputs) SourceMainFramesV1.Point0498.input_defined SourceMainFramesV1.Point0498.outputs_defined (SourceMainFramesV1.Point0498.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=499) (base:=SynergyHeightC.FullMainFrame.base total 499) (input:=SourceMainFramesV1.Point0499.input) (pair:=SourceMainFramesV1.Point0499.outputs) SourceMainFramesV1.Point0499.input_defined SourceMainFramesV1.Point0499.outputs_defined (SourceMainFramesV1.Point0499.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=500) (base:=SynergyHeightC.FullMainFrame.base total 500) (input:=SourceMainFramesV1.Point0500.input) (pair:=SourceMainFramesV1.Point0500.outputs) SourceMainFramesV1.Point0500.input_defined SourceMainFramesV1.Point0500.outputs_defined (SourceMainFramesV1.Point0500.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=501) (base:=SynergyHeightC.FullMainFrame.base total 501) (input:=SourceMainFramesV1.Point0501.input) (pair:=SourceMainFramesV1.Point0501.outputs) SourceMainFramesV1.Point0501.input_defined SourceMainFramesV1.Point0501.outputs_defined (SourceMainFramesV1.Point0501.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=502) (base:=SynergyHeightC.FullMainFrame.base total 502) (input:=SourceMainFramesV1.Point0502.input) (pair:=SourceMainFramesV1.Point0502.outputs) SourceMainFramesV1.Point0502.input_defined SourceMainFramesV1.Point0502.outputs_defined (SourceMainFramesV1.Point0502.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=503) (base:=SynergyHeightC.FullMainFrame.base total 503) (input:=SourceMainFramesV1.Point0503.input) (pair:=SourceMainFramesV1.Point0503.outputs) SourceMainFramesV1.Point0503.input_defined SourceMainFramesV1.Point0503.outputs_defined (SourceMainFramesV1.Point0503.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=504) (base:=SynergyHeightC.FullMainFrame.base total 504) (input:=SourceMainFramesV1.Point0504.input) (pair:=SourceMainFramesV1.Point0504.outputs) SourceMainFramesV1.Point0504.input_defined SourceMainFramesV1.Point0504.outputs_defined (SourceMainFramesV1.Point0504.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=505) (base:=SynergyHeightC.FullMainFrame.base total 505) (input:=SourceMainFramesV1.Point0505.input) (pair:=SourceMainFramesV1.Point0505.outputs) SourceMainFramesV1.Point0505.input_defined SourceMainFramesV1.Point0505.outputs_defined (SourceMainFramesV1.Point0505.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=506) (base:=SynergyHeightC.FullMainFrame.base total 506) (input:=SourceMainFramesV1.Point0506.input) (pair:=SourceMainFramesV1.Point0506.outputs) SourceMainFramesV1.Point0506.input_defined SourceMainFramesV1.Point0506.outputs_defined (SourceMainFramesV1.Point0506.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=507) (base:=SynergyHeightC.FullMainFrame.base total 507) (input:=SourceMainFramesV1.Point0507.input) (pair:=SourceMainFramesV1.Point0507.outputs) SourceMainFramesV1.Point0507.input_defined SourceMainFramesV1.Point0507.outputs_defined (SourceMainFramesV1.Point0507.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=508) (base:=SynergyHeightC.FullMainFrame.base total 508) (input:=SourceMainFramesV1.Point0508.input) (pair:=SourceMainFramesV1.Point0508.outputs) SourceMainFramesV1.Point0508.input_defined SourceMainFramesV1.Point0508.outputs_defined (SourceMainFramesV1.Point0508.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=509) (base:=SynergyHeightC.FullMainFrame.base total 509) (input:=SourceMainFramesV1.Point0509.input) (pair:=SourceMainFramesV1.Point0509.outputs) SourceMainFramesV1.Point0509.input_defined SourceMainFramesV1.Point0509.outputs_defined (SourceMainFramesV1.Point0509.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=510) (base:=SynergyHeightC.FullMainFrame.base total 510) (input:=SourceMainFramesV1.Point0510.input) (pair:=SourceMainFramesV1.Point0510.outputs) SourceMainFramesV1.Point0510.input_defined SourceMainFramesV1.Point0510.outputs_defined (SourceMainFramesV1.Point0510.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=511) (base:=SynergyHeightC.FullMainFrame.base total 511) (input:=SourceMainFramesV1.Point0511.input) (pair:=SourceMainFramesV1.Point0511.outputs) SourceMainFramesV1.Point0511.input_defined SourceMainFramesV1.Point0511.outputs_defined (SourceMainFramesV1.Point0511.source_outputs total)
end SourceMainFramesV1.Block15
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Block15.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
