import SourceMainFramesV1.Point0416
import SourceMainFramesV1.Point0417
import SourceMainFramesV1.Point0418
import SourceMainFramesV1.Point0419
import SourceMainFramesV1.Point0420
import SourceMainFramesV1.Point0421
import SourceMainFramesV1.Point0422
import SourceMainFramesV1.Point0423
import SourceMainFramesV1.Point0424
import SourceMainFramesV1.Point0425
import SourceMainFramesV1.Point0426
import SourceMainFramesV1.Point0427
import SourceMainFramesV1.Point0428
import SourceMainFramesV1.Point0429
import SourceMainFramesV1.Point0430
import SourceMainFramesV1.Point0431
import SourceMainFramesV1.Point0432
import SourceMainFramesV1.Point0433
import SourceMainFramesV1.Point0434
import SourceMainFramesV1.Point0435
import SourceMainFramesV1.Point0436
import SourceMainFramesV1.Point0437
import SourceMainFramesV1.Point0438
import SourceMainFramesV1.Point0439
import SourceMainFramesV1.Point0440
import SourceMainFramesV1.Point0441
import SourceMainFramesV1.Point0442
import SourceMainFramesV1.Point0443
import SourceMainFramesV1.Point0444
import SourceMainFramesV1.Point0445
import SourceMainFramesV1.Point0446
import SourceMainFramesV1.Point0447
import SourceMainFramesV1.PackOutput
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Block13
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (total : ProofBox) (i : ℕ) (lower : 416 ≤ i) (upper : i < 448) :
 ∃ base input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs base input c d := by
 interval_cases i
 · exact SourceMainFramesV1.pack_output (i:=416) (base:=SynergyHeightC.FullMainFrame.base total 416) (input:=SourceMainFramesV1.Point0416.input) (pair:=SourceMainFramesV1.Point0416.outputs) SourceMainFramesV1.Point0416.input_defined SourceMainFramesV1.Point0416.outputs_defined (SourceMainFramesV1.Point0416.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=417) (base:=SynergyHeightC.FullMainFrame.base total 417) (input:=SourceMainFramesV1.Point0417.input) (pair:=SourceMainFramesV1.Point0417.outputs) SourceMainFramesV1.Point0417.input_defined SourceMainFramesV1.Point0417.outputs_defined (SourceMainFramesV1.Point0417.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=418) (base:=SynergyHeightC.FullMainFrame.base total 418) (input:=SourceMainFramesV1.Point0418.input) (pair:=SourceMainFramesV1.Point0418.outputs) SourceMainFramesV1.Point0418.input_defined SourceMainFramesV1.Point0418.outputs_defined (SourceMainFramesV1.Point0418.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=419) (base:=SynergyHeightC.FullMainFrame.base total 419) (input:=SourceMainFramesV1.Point0419.input) (pair:=SourceMainFramesV1.Point0419.outputs) SourceMainFramesV1.Point0419.input_defined SourceMainFramesV1.Point0419.outputs_defined (SourceMainFramesV1.Point0419.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=420) (base:=SynergyHeightC.FullMainFrame.base total 420) (input:=SourceMainFramesV1.Point0420.input) (pair:=SourceMainFramesV1.Point0420.outputs) SourceMainFramesV1.Point0420.input_defined SourceMainFramesV1.Point0420.outputs_defined (SourceMainFramesV1.Point0420.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=421) (base:=SynergyHeightC.FullMainFrame.base total 421) (input:=SourceMainFramesV1.Point0421.input) (pair:=SourceMainFramesV1.Point0421.outputs) SourceMainFramesV1.Point0421.input_defined SourceMainFramesV1.Point0421.outputs_defined (SourceMainFramesV1.Point0421.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=422) (base:=SynergyHeightC.FullMainFrame.base total 422) (input:=SourceMainFramesV1.Point0422.input) (pair:=SourceMainFramesV1.Point0422.outputs) SourceMainFramesV1.Point0422.input_defined SourceMainFramesV1.Point0422.outputs_defined (SourceMainFramesV1.Point0422.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=423) (base:=SynergyHeightC.FullMainFrame.base total 423) (input:=SourceMainFramesV1.Point0423.input) (pair:=SourceMainFramesV1.Point0423.outputs) SourceMainFramesV1.Point0423.input_defined SourceMainFramesV1.Point0423.outputs_defined (SourceMainFramesV1.Point0423.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=424) (base:=SynergyHeightC.FullMainFrame.base total 424) (input:=SourceMainFramesV1.Point0424.input) (pair:=SourceMainFramesV1.Point0424.outputs) SourceMainFramesV1.Point0424.input_defined SourceMainFramesV1.Point0424.outputs_defined (SourceMainFramesV1.Point0424.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=425) (base:=SynergyHeightC.FullMainFrame.base total 425) (input:=SourceMainFramesV1.Point0425.input) (pair:=SourceMainFramesV1.Point0425.outputs) SourceMainFramesV1.Point0425.input_defined SourceMainFramesV1.Point0425.outputs_defined (SourceMainFramesV1.Point0425.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=426) (base:=SynergyHeightC.FullMainFrame.base total 426) (input:=SourceMainFramesV1.Point0426.input) (pair:=SourceMainFramesV1.Point0426.outputs) SourceMainFramesV1.Point0426.input_defined SourceMainFramesV1.Point0426.outputs_defined (SourceMainFramesV1.Point0426.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=427) (base:=SynergyHeightC.FullMainFrame.base total 427) (input:=SourceMainFramesV1.Point0427.input) (pair:=SourceMainFramesV1.Point0427.outputs) SourceMainFramesV1.Point0427.input_defined SourceMainFramesV1.Point0427.outputs_defined (SourceMainFramesV1.Point0427.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=428) (base:=SynergyHeightC.FullMainFrame.base total 428) (input:=SourceMainFramesV1.Point0428.input) (pair:=SourceMainFramesV1.Point0428.outputs) SourceMainFramesV1.Point0428.input_defined SourceMainFramesV1.Point0428.outputs_defined (SourceMainFramesV1.Point0428.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=429) (base:=SynergyHeightC.FullMainFrame.base total 429) (input:=SourceMainFramesV1.Point0429.input) (pair:=SourceMainFramesV1.Point0429.outputs) SourceMainFramesV1.Point0429.input_defined SourceMainFramesV1.Point0429.outputs_defined (SourceMainFramesV1.Point0429.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=430) (base:=SynergyHeightC.FullMainFrame.base total 430) (input:=SourceMainFramesV1.Point0430.input) (pair:=SourceMainFramesV1.Point0430.outputs) SourceMainFramesV1.Point0430.input_defined SourceMainFramesV1.Point0430.outputs_defined (SourceMainFramesV1.Point0430.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=431) (base:=SynergyHeightC.FullMainFrame.base total 431) (input:=SourceMainFramesV1.Point0431.input) (pair:=SourceMainFramesV1.Point0431.outputs) SourceMainFramesV1.Point0431.input_defined SourceMainFramesV1.Point0431.outputs_defined (SourceMainFramesV1.Point0431.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=432) (base:=SynergyHeightC.FullMainFrame.base total 432) (input:=SourceMainFramesV1.Point0432.input) (pair:=SourceMainFramesV1.Point0432.outputs) SourceMainFramesV1.Point0432.input_defined SourceMainFramesV1.Point0432.outputs_defined (SourceMainFramesV1.Point0432.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=433) (base:=SynergyHeightC.FullMainFrame.base total 433) (input:=SourceMainFramesV1.Point0433.input) (pair:=SourceMainFramesV1.Point0433.outputs) SourceMainFramesV1.Point0433.input_defined SourceMainFramesV1.Point0433.outputs_defined (SourceMainFramesV1.Point0433.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=434) (base:=SynergyHeightC.FullMainFrame.base total 434) (input:=SourceMainFramesV1.Point0434.input) (pair:=SourceMainFramesV1.Point0434.outputs) SourceMainFramesV1.Point0434.input_defined SourceMainFramesV1.Point0434.outputs_defined (SourceMainFramesV1.Point0434.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=435) (base:=SynergyHeightC.FullMainFrame.base total 435) (input:=SourceMainFramesV1.Point0435.input) (pair:=SourceMainFramesV1.Point0435.outputs) SourceMainFramesV1.Point0435.input_defined SourceMainFramesV1.Point0435.outputs_defined (SourceMainFramesV1.Point0435.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=436) (base:=SynergyHeightC.FullMainFrame.base total 436) (input:=SourceMainFramesV1.Point0436.input) (pair:=SourceMainFramesV1.Point0436.outputs) SourceMainFramesV1.Point0436.input_defined SourceMainFramesV1.Point0436.outputs_defined (SourceMainFramesV1.Point0436.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=437) (base:=SynergyHeightC.FullMainFrame.base total 437) (input:=SourceMainFramesV1.Point0437.input) (pair:=SourceMainFramesV1.Point0437.outputs) SourceMainFramesV1.Point0437.input_defined SourceMainFramesV1.Point0437.outputs_defined (SourceMainFramesV1.Point0437.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=438) (base:=SynergyHeightC.FullMainFrame.base total 438) (input:=SourceMainFramesV1.Point0438.input) (pair:=SourceMainFramesV1.Point0438.outputs) SourceMainFramesV1.Point0438.input_defined SourceMainFramesV1.Point0438.outputs_defined (SourceMainFramesV1.Point0438.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=439) (base:=SynergyHeightC.FullMainFrame.base total 439) (input:=SourceMainFramesV1.Point0439.input) (pair:=SourceMainFramesV1.Point0439.outputs) SourceMainFramesV1.Point0439.input_defined SourceMainFramesV1.Point0439.outputs_defined (SourceMainFramesV1.Point0439.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=440) (base:=SynergyHeightC.FullMainFrame.base total 440) (input:=SourceMainFramesV1.Point0440.input) (pair:=SourceMainFramesV1.Point0440.outputs) SourceMainFramesV1.Point0440.input_defined SourceMainFramesV1.Point0440.outputs_defined (SourceMainFramesV1.Point0440.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=441) (base:=SynergyHeightC.FullMainFrame.base total 441) (input:=SourceMainFramesV1.Point0441.input) (pair:=SourceMainFramesV1.Point0441.outputs) SourceMainFramesV1.Point0441.input_defined SourceMainFramesV1.Point0441.outputs_defined (SourceMainFramesV1.Point0441.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=442) (base:=SynergyHeightC.FullMainFrame.base total 442) (input:=SourceMainFramesV1.Point0442.input) (pair:=SourceMainFramesV1.Point0442.outputs) SourceMainFramesV1.Point0442.input_defined SourceMainFramesV1.Point0442.outputs_defined (SourceMainFramesV1.Point0442.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=443) (base:=SynergyHeightC.FullMainFrame.base total 443) (input:=SourceMainFramesV1.Point0443.input) (pair:=SourceMainFramesV1.Point0443.outputs) SourceMainFramesV1.Point0443.input_defined SourceMainFramesV1.Point0443.outputs_defined (SourceMainFramesV1.Point0443.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=444) (base:=SynergyHeightC.FullMainFrame.base total 444) (input:=SourceMainFramesV1.Point0444.input) (pair:=SourceMainFramesV1.Point0444.outputs) SourceMainFramesV1.Point0444.input_defined SourceMainFramesV1.Point0444.outputs_defined (SourceMainFramesV1.Point0444.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=445) (base:=SynergyHeightC.FullMainFrame.base total 445) (input:=SourceMainFramesV1.Point0445.input) (pair:=SourceMainFramesV1.Point0445.outputs) SourceMainFramesV1.Point0445.input_defined SourceMainFramesV1.Point0445.outputs_defined (SourceMainFramesV1.Point0445.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=446) (base:=SynergyHeightC.FullMainFrame.base total 446) (input:=SourceMainFramesV1.Point0446.input) (pair:=SourceMainFramesV1.Point0446.outputs) SourceMainFramesV1.Point0446.input_defined SourceMainFramesV1.Point0446.outputs_defined (SourceMainFramesV1.Point0446.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=447) (base:=SynergyHeightC.FullMainFrame.base total 447) (input:=SourceMainFramesV1.Point0447.input) (pair:=SourceMainFramesV1.Point0447.outputs) SourceMainFramesV1.Point0447.input_defined SourceMainFramesV1.Point0447.outputs_defined (SourceMainFramesV1.Point0447.source_outputs total)
end SourceMainFramesV1.Block13
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Block13.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
