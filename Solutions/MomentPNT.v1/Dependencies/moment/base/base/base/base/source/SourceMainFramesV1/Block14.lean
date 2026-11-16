import SourceMainFramesV1.Point0448
import SourceMainFramesV1.Point0449
import SourceMainFramesV1.Point0450
import SourceMainFramesV1.Point0451
import SourceMainFramesV1.Point0452
import SourceMainFramesV1.Point0453
import SourceMainFramesV1.Point0454
import SourceMainFramesV1.Point0455
import SourceMainFramesV1.Point0456
import SourceMainFramesV1.Point0457
import SourceMainFramesV1.Point0458
import SourceMainFramesV1.Point0459
import SourceMainFramesV1.Point0460
import SourceMainFramesV1.Point0461
import SourceMainFramesV1.Point0462
import SourceMainFramesV1.Point0463
import SourceMainFramesV1.Point0464
import SourceMainFramesV1.Point0465
import SourceMainFramesV1.Point0466
import SourceMainFramesV1.Point0467
import SourceMainFramesV1.Point0468
import SourceMainFramesV1.Point0469
import SourceMainFramesV1.Point0470
import SourceMainFramesV1.Point0471
import SourceMainFramesV1.Point0472
import SourceMainFramesV1.Point0473
import SourceMainFramesV1.Point0474
import SourceMainFramesV1.Point0475
import SourceMainFramesV1.Point0476
import SourceMainFramesV1.Point0477
import SourceMainFramesV1.Point0478
import SourceMainFramesV1.Point0479
import SourceMainFramesV1.PackOutput
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Block14
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (total : ProofBox) (i : ℕ) (lower : 448 ≤ i) (upper : i < 480) :
 ∃ base input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs base input c d := by
 interval_cases i
 · exact SourceMainFramesV1.pack_output (i:=448) (base:=SynergyHeightC.FullMainFrame.base total 448) (input:=SourceMainFramesV1.Point0448.input) (pair:=SourceMainFramesV1.Point0448.outputs) SourceMainFramesV1.Point0448.input_defined SourceMainFramesV1.Point0448.outputs_defined (SourceMainFramesV1.Point0448.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=449) (base:=SynergyHeightC.FullMainFrame.base total 449) (input:=SourceMainFramesV1.Point0449.input) (pair:=SourceMainFramesV1.Point0449.outputs) SourceMainFramesV1.Point0449.input_defined SourceMainFramesV1.Point0449.outputs_defined (SourceMainFramesV1.Point0449.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=450) (base:=SynergyHeightC.FullMainFrame.base total 450) (input:=SourceMainFramesV1.Point0450.input) (pair:=SourceMainFramesV1.Point0450.outputs) SourceMainFramesV1.Point0450.input_defined SourceMainFramesV1.Point0450.outputs_defined (SourceMainFramesV1.Point0450.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=451) (base:=SynergyHeightC.FullMainFrame.base total 451) (input:=SourceMainFramesV1.Point0451.input) (pair:=SourceMainFramesV1.Point0451.outputs) SourceMainFramesV1.Point0451.input_defined SourceMainFramesV1.Point0451.outputs_defined (SourceMainFramesV1.Point0451.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=452) (base:=SynergyHeightC.FullMainFrame.base total 452) (input:=SourceMainFramesV1.Point0452.input) (pair:=SourceMainFramesV1.Point0452.outputs) SourceMainFramesV1.Point0452.input_defined SourceMainFramesV1.Point0452.outputs_defined (SourceMainFramesV1.Point0452.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=453) (base:=SynergyHeightC.FullMainFrame.base total 453) (input:=SourceMainFramesV1.Point0453.input) (pair:=SourceMainFramesV1.Point0453.outputs) SourceMainFramesV1.Point0453.input_defined SourceMainFramesV1.Point0453.outputs_defined (SourceMainFramesV1.Point0453.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=454) (base:=SynergyHeightC.FullMainFrame.base total 454) (input:=SourceMainFramesV1.Point0454.input) (pair:=SourceMainFramesV1.Point0454.outputs) SourceMainFramesV1.Point0454.input_defined SourceMainFramesV1.Point0454.outputs_defined (SourceMainFramesV1.Point0454.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=455) (base:=SynergyHeightC.FullMainFrame.base total 455) (input:=SourceMainFramesV1.Point0455.input) (pair:=SourceMainFramesV1.Point0455.outputs) SourceMainFramesV1.Point0455.input_defined SourceMainFramesV1.Point0455.outputs_defined (SourceMainFramesV1.Point0455.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=456) (base:=SynergyHeightC.FullMainFrame.base total 456) (input:=SourceMainFramesV1.Point0456.input) (pair:=SourceMainFramesV1.Point0456.outputs) SourceMainFramesV1.Point0456.input_defined SourceMainFramesV1.Point0456.outputs_defined (SourceMainFramesV1.Point0456.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=457) (base:=SynergyHeightC.FullMainFrame.base total 457) (input:=SourceMainFramesV1.Point0457.input) (pair:=SourceMainFramesV1.Point0457.outputs) SourceMainFramesV1.Point0457.input_defined SourceMainFramesV1.Point0457.outputs_defined (SourceMainFramesV1.Point0457.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=458) (base:=SynergyHeightC.FullMainFrame.base total 458) (input:=SourceMainFramesV1.Point0458.input) (pair:=SourceMainFramesV1.Point0458.outputs) SourceMainFramesV1.Point0458.input_defined SourceMainFramesV1.Point0458.outputs_defined (SourceMainFramesV1.Point0458.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=459) (base:=SynergyHeightC.FullMainFrame.base total 459) (input:=SourceMainFramesV1.Point0459.input) (pair:=SourceMainFramesV1.Point0459.outputs) SourceMainFramesV1.Point0459.input_defined SourceMainFramesV1.Point0459.outputs_defined (SourceMainFramesV1.Point0459.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=460) (base:=SynergyHeightC.FullMainFrame.base total 460) (input:=SourceMainFramesV1.Point0460.input) (pair:=SourceMainFramesV1.Point0460.outputs) SourceMainFramesV1.Point0460.input_defined SourceMainFramesV1.Point0460.outputs_defined (SourceMainFramesV1.Point0460.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=461) (base:=SynergyHeightC.FullMainFrame.base total 461) (input:=SourceMainFramesV1.Point0461.input) (pair:=SourceMainFramesV1.Point0461.outputs) SourceMainFramesV1.Point0461.input_defined SourceMainFramesV1.Point0461.outputs_defined (SourceMainFramesV1.Point0461.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=462) (base:=SynergyHeightC.FullMainFrame.base total 462) (input:=SourceMainFramesV1.Point0462.input) (pair:=SourceMainFramesV1.Point0462.outputs) SourceMainFramesV1.Point0462.input_defined SourceMainFramesV1.Point0462.outputs_defined (SourceMainFramesV1.Point0462.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=463) (base:=SynergyHeightC.FullMainFrame.base total 463) (input:=SourceMainFramesV1.Point0463.input) (pair:=SourceMainFramesV1.Point0463.outputs) SourceMainFramesV1.Point0463.input_defined SourceMainFramesV1.Point0463.outputs_defined (SourceMainFramesV1.Point0463.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=464) (base:=SynergyHeightC.FullMainFrame.base total 464) (input:=SourceMainFramesV1.Point0464.input) (pair:=SourceMainFramesV1.Point0464.outputs) SourceMainFramesV1.Point0464.input_defined SourceMainFramesV1.Point0464.outputs_defined (SourceMainFramesV1.Point0464.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=465) (base:=SynergyHeightC.FullMainFrame.base total 465) (input:=SourceMainFramesV1.Point0465.input) (pair:=SourceMainFramesV1.Point0465.outputs) SourceMainFramesV1.Point0465.input_defined SourceMainFramesV1.Point0465.outputs_defined (SourceMainFramesV1.Point0465.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=466) (base:=SynergyHeightC.FullMainFrame.base total 466) (input:=SourceMainFramesV1.Point0466.input) (pair:=SourceMainFramesV1.Point0466.outputs) SourceMainFramesV1.Point0466.input_defined SourceMainFramesV1.Point0466.outputs_defined (SourceMainFramesV1.Point0466.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=467) (base:=SynergyHeightC.FullMainFrame.base total 467) (input:=SourceMainFramesV1.Point0467.input) (pair:=SourceMainFramesV1.Point0467.outputs) SourceMainFramesV1.Point0467.input_defined SourceMainFramesV1.Point0467.outputs_defined (SourceMainFramesV1.Point0467.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=468) (base:=SynergyHeightC.FullMainFrame.base total 468) (input:=SourceMainFramesV1.Point0468.input) (pair:=SourceMainFramesV1.Point0468.outputs) SourceMainFramesV1.Point0468.input_defined SourceMainFramesV1.Point0468.outputs_defined (SourceMainFramesV1.Point0468.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=469) (base:=SynergyHeightC.FullMainFrame.base total 469) (input:=SourceMainFramesV1.Point0469.input) (pair:=SourceMainFramesV1.Point0469.outputs) SourceMainFramesV1.Point0469.input_defined SourceMainFramesV1.Point0469.outputs_defined (SourceMainFramesV1.Point0469.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=470) (base:=SynergyHeightC.FullMainFrame.base total 470) (input:=SourceMainFramesV1.Point0470.input) (pair:=SourceMainFramesV1.Point0470.outputs) SourceMainFramesV1.Point0470.input_defined SourceMainFramesV1.Point0470.outputs_defined (SourceMainFramesV1.Point0470.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=471) (base:=SynergyHeightC.FullMainFrame.base total 471) (input:=SourceMainFramesV1.Point0471.input) (pair:=SourceMainFramesV1.Point0471.outputs) SourceMainFramesV1.Point0471.input_defined SourceMainFramesV1.Point0471.outputs_defined (SourceMainFramesV1.Point0471.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=472) (base:=SynergyHeightC.FullMainFrame.base total 472) (input:=SourceMainFramesV1.Point0472.input) (pair:=SourceMainFramesV1.Point0472.outputs) SourceMainFramesV1.Point0472.input_defined SourceMainFramesV1.Point0472.outputs_defined (SourceMainFramesV1.Point0472.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=473) (base:=SynergyHeightC.FullMainFrame.base total 473) (input:=SourceMainFramesV1.Point0473.input) (pair:=SourceMainFramesV1.Point0473.outputs) SourceMainFramesV1.Point0473.input_defined SourceMainFramesV1.Point0473.outputs_defined (SourceMainFramesV1.Point0473.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=474) (base:=SynergyHeightC.FullMainFrame.base total 474) (input:=SourceMainFramesV1.Point0474.input) (pair:=SourceMainFramesV1.Point0474.outputs) SourceMainFramesV1.Point0474.input_defined SourceMainFramesV1.Point0474.outputs_defined (SourceMainFramesV1.Point0474.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=475) (base:=SynergyHeightC.FullMainFrame.base total 475) (input:=SourceMainFramesV1.Point0475.input) (pair:=SourceMainFramesV1.Point0475.outputs) SourceMainFramesV1.Point0475.input_defined SourceMainFramesV1.Point0475.outputs_defined (SourceMainFramesV1.Point0475.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=476) (base:=SynergyHeightC.FullMainFrame.base total 476) (input:=SourceMainFramesV1.Point0476.input) (pair:=SourceMainFramesV1.Point0476.outputs) SourceMainFramesV1.Point0476.input_defined SourceMainFramesV1.Point0476.outputs_defined (SourceMainFramesV1.Point0476.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=477) (base:=SynergyHeightC.FullMainFrame.base total 477) (input:=SourceMainFramesV1.Point0477.input) (pair:=SourceMainFramesV1.Point0477.outputs) SourceMainFramesV1.Point0477.input_defined SourceMainFramesV1.Point0477.outputs_defined (SourceMainFramesV1.Point0477.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=478) (base:=SynergyHeightC.FullMainFrame.base total 478) (input:=SourceMainFramesV1.Point0478.input) (pair:=SourceMainFramesV1.Point0478.outputs) SourceMainFramesV1.Point0478.input_defined SourceMainFramesV1.Point0478.outputs_defined (SourceMainFramesV1.Point0478.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=479) (base:=SynergyHeightC.FullMainFrame.base total 479) (input:=SourceMainFramesV1.Point0479.input) (pair:=SourceMainFramesV1.Point0479.outputs) SourceMainFramesV1.Point0479.input_defined SourceMainFramesV1.Point0479.outputs_defined (SourceMainFramesV1.Point0479.source_outputs total)
end SourceMainFramesV1.Block14
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Block14.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
