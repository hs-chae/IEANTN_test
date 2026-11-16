import SourceMainFramesV1.Point0384
import SourceMainFramesV1.Point0385
import SourceMainFramesV1.Point0386
import SourceMainFramesV1.Point0387
import SourceMainFramesV1.Point0388
import SourceMainFramesV1.Point0389
import SourceMainFramesV1.Point0390
import SourceMainFramesV1.Point0391
import SourceMainFramesV1.Point0392
import SourceMainFramesV1.Point0393
import SourceMainFramesV1.Point0394
import SourceMainFramesV1.Point0395
import SourceMainFramesV1.Point0396
import SourceMainFramesV1.Point0397
import SourceMainFramesV1.Point0398
import SourceMainFramesV1.Point0399
import SourceMainFramesV1.Point0400
import SourceMainFramesV1.Point0401
import SourceMainFramesV1.Point0402
import SourceMainFramesV1.Point0403
import SourceMainFramesV1.Point0404
import SourceMainFramesV1.Point0405
import SourceMainFramesV1.Point0406
import SourceMainFramesV1.Point0407
import SourceMainFramesV1.Point0408
import SourceMainFramesV1.Point0409
import SourceMainFramesV1.Point0410
import SourceMainFramesV1.Point0411
import SourceMainFramesV1.Point0412
import SourceMainFramesV1.Point0413
import SourceMainFramesV1.Point0414
import SourceMainFramesV1.Point0415
import SourceMainFramesV1.PackOutput
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Block12
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (total : ProofBox) (i : ℕ) (lower : 384 ≤ i) (upper : i < 416) :
 ∃ base input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs base input c d := by
 interval_cases i
 · exact SourceMainFramesV1.pack_output (i:=384) (base:=SynergyHeightC.FullMainFrame.base total 384) (input:=SourceMainFramesV1.Point0384.input) (pair:=SourceMainFramesV1.Point0384.outputs) SourceMainFramesV1.Point0384.input_defined SourceMainFramesV1.Point0384.outputs_defined (SourceMainFramesV1.Point0384.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=385) (base:=SynergyHeightC.FullMainFrame.base total 385) (input:=SourceMainFramesV1.Point0385.input) (pair:=SourceMainFramesV1.Point0385.outputs) SourceMainFramesV1.Point0385.input_defined SourceMainFramesV1.Point0385.outputs_defined (SourceMainFramesV1.Point0385.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=386) (base:=SynergyHeightC.FullMainFrame.base total 386) (input:=SourceMainFramesV1.Point0386.input) (pair:=SourceMainFramesV1.Point0386.outputs) SourceMainFramesV1.Point0386.input_defined SourceMainFramesV1.Point0386.outputs_defined (SourceMainFramesV1.Point0386.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=387) (base:=SynergyHeightC.FullMainFrame.base total 387) (input:=SourceMainFramesV1.Point0387.input) (pair:=SourceMainFramesV1.Point0387.outputs) SourceMainFramesV1.Point0387.input_defined SourceMainFramesV1.Point0387.outputs_defined (SourceMainFramesV1.Point0387.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=388) (base:=SynergyHeightC.FullMainFrame.base total 388) (input:=SourceMainFramesV1.Point0388.input) (pair:=SourceMainFramesV1.Point0388.outputs) SourceMainFramesV1.Point0388.input_defined SourceMainFramesV1.Point0388.outputs_defined (SourceMainFramesV1.Point0388.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=389) (base:=SynergyHeightC.FullMainFrame.base total 389) (input:=SourceMainFramesV1.Point0389.input) (pair:=SourceMainFramesV1.Point0389.outputs) SourceMainFramesV1.Point0389.input_defined SourceMainFramesV1.Point0389.outputs_defined (SourceMainFramesV1.Point0389.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=390) (base:=SynergyHeightC.FullMainFrame.base total 390) (input:=SourceMainFramesV1.Point0390.input) (pair:=SourceMainFramesV1.Point0390.outputs) SourceMainFramesV1.Point0390.input_defined SourceMainFramesV1.Point0390.outputs_defined (SourceMainFramesV1.Point0390.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=391) (base:=SynergyHeightC.FullMainFrame.base total 391) (input:=SourceMainFramesV1.Point0391.input) (pair:=SourceMainFramesV1.Point0391.outputs) SourceMainFramesV1.Point0391.input_defined SourceMainFramesV1.Point0391.outputs_defined (SourceMainFramesV1.Point0391.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=392) (base:=SynergyHeightC.FullMainFrame.base total 392) (input:=SourceMainFramesV1.Point0392.input) (pair:=SourceMainFramesV1.Point0392.outputs) SourceMainFramesV1.Point0392.input_defined SourceMainFramesV1.Point0392.outputs_defined (SourceMainFramesV1.Point0392.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=393) (base:=SynergyHeightC.FullMainFrame.base total 393) (input:=SourceMainFramesV1.Point0393.input) (pair:=SourceMainFramesV1.Point0393.outputs) SourceMainFramesV1.Point0393.input_defined SourceMainFramesV1.Point0393.outputs_defined (SourceMainFramesV1.Point0393.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=394) (base:=SynergyHeightC.FullMainFrame.base total 394) (input:=SourceMainFramesV1.Point0394.input) (pair:=SourceMainFramesV1.Point0394.outputs) SourceMainFramesV1.Point0394.input_defined SourceMainFramesV1.Point0394.outputs_defined (SourceMainFramesV1.Point0394.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=395) (base:=SynergyHeightC.FullMainFrame.base total 395) (input:=SourceMainFramesV1.Point0395.input) (pair:=SourceMainFramesV1.Point0395.outputs) SourceMainFramesV1.Point0395.input_defined SourceMainFramesV1.Point0395.outputs_defined (SourceMainFramesV1.Point0395.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=396) (base:=SynergyHeightC.FullMainFrame.base total 396) (input:=SourceMainFramesV1.Point0396.input) (pair:=SourceMainFramesV1.Point0396.outputs) SourceMainFramesV1.Point0396.input_defined SourceMainFramesV1.Point0396.outputs_defined (SourceMainFramesV1.Point0396.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=397) (base:=SynergyHeightC.FullMainFrame.base total 397) (input:=SourceMainFramesV1.Point0397.input) (pair:=SourceMainFramesV1.Point0397.outputs) SourceMainFramesV1.Point0397.input_defined SourceMainFramesV1.Point0397.outputs_defined (SourceMainFramesV1.Point0397.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=398) (base:=SynergyHeightC.FullMainFrame.base total 398) (input:=SourceMainFramesV1.Point0398.input) (pair:=SourceMainFramesV1.Point0398.outputs) SourceMainFramesV1.Point0398.input_defined SourceMainFramesV1.Point0398.outputs_defined (SourceMainFramesV1.Point0398.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=399) (base:=SynergyHeightC.FullMainFrame.base total 399) (input:=SourceMainFramesV1.Point0399.input) (pair:=SourceMainFramesV1.Point0399.outputs) SourceMainFramesV1.Point0399.input_defined SourceMainFramesV1.Point0399.outputs_defined (SourceMainFramesV1.Point0399.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=400) (base:=SynergyHeightC.FullMainFrame.base total 400) (input:=SourceMainFramesV1.Point0400.input) (pair:=SourceMainFramesV1.Point0400.outputs) SourceMainFramesV1.Point0400.input_defined SourceMainFramesV1.Point0400.outputs_defined (SourceMainFramesV1.Point0400.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=401) (base:=SynergyHeightC.FullMainFrame.base total 401) (input:=SourceMainFramesV1.Point0401.input) (pair:=SourceMainFramesV1.Point0401.outputs) SourceMainFramesV1.Point0401.input_defined SourceMainFramesV1.Point0401.outputs_defined (SourceMainFramesV1.Point0401.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=402) (base:=SynergyHeightC.FullMainFrame.base total 402) (input:=SourceMainFramesV1.Point0402.input) (pair:=SourceMainFramesV1.Point0402.outputs) SourceMainFramesV1.Point0402.input_defined SourceMainFramesV1.Point0402.outputs_defined (SourceMainFramesV1.Point0402.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=403) (base:=SynergyHeightC.FullMainFrame.base total 403) (input:=SourceMainFramesV1.Point0403.input) (pair:=SourceMainFramesV1.Point0403.outputs) SourceMainFramesV1.Point0403.input_defined SourceMainFramesV1.Point0403.outputs_defined (SourceMainFramesV1.Point0403.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=404) (base:=SynergyHeightC.FullMainFrame.base total 404) (input:=SourceMainFramesV1.Point0404.input) (pair:=SourceMainFramesV1.Point0404.outputs) SourceMainFramesV1.Point0404.input_defined SourceMainFramesV1.Point0404.outputs_defined (SourceMainFramesV1.Point0404.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=405) (base:=SynergyHeightC.FullMainFrame.base total 405) (input:=SourceMainFramesV1.Point0405.input) (pair:=SourceMainFramesV1.Point0405.outputs) SourceMainFramesV1.Point0405.input_defined SourceMainFramesV1.Point0405.outputs_defined (SourceMainFramesV1.Point0405.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=406) (base:=SynergyHeightC.FullMainFrame.base total 406) (input:=SourceMainFramesV1.Point0406.input) (pair:=SourceMainFramesV1.Point0406.outputs) SourceMainFramesV1.Point0406.input_defined SourceMainFramesV1.Point0406.outputs_defined (SourceMainFramesV1.Point0406.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=407) (base:=SynergyHeightC.FullMainFrame.base total 407) (input:=SourceMainFramesV1.Point0407.input) (pair:=SourceMainFramesV1.Point0407.outputs) SourceMainFramesV1.Point0407.input_defined SourceMainFramesV1.Point0407.outputs_defined (SourceMainFramesV1.Point0407.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=408) (base:=SynergyHeightC.FullMainFrame.base total 408) (input:=SourceMainFramesV1.Point0408.input) (pair:=SourceMainFramesV1.Point0408.outputs) SourceMainFramesV1.Point0408.input_defined SourceMainFramesV1.Point0408.outputs_defined (SourceMainFramesV1.Point0408.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=409) (base:=SynergyHeightC.FullMainFrame.base total 409) (input:=SourceMainFramesV1.Point0409.input) (pair:=SourceMainFramesV1.Point0409.outputs) SourceMainFramesV1.Point0409.input_defined SourceMainFramesV1.Point0409.outputs_defined (SourceMainFramesV1.Point0409.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=410) (base:=SynergyHeightC.FullMainFrame.base total 410) (input:=SourceMainFramesV1.Point0410.input) (pair:=SourceMainFramesV1.Point0410.outputs) SourceMainFramesV1.Point0410.input_defined SourceMainFramesV1.Point0410.outputs_defined (SourceMainFramesV1.Point0410.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=411) (base:=SynergyHeightC.FullMainFrame.base total 411) (input:=SourceMainFramesV1.Point0411.input) (pair:=SourceMainFramesV1.Point0411.outputs) SourceMainFramesV1.Point0411.input_defined SourceMainFramesV1.Point0411.outputs_defined (SourceMainFramesV1.Point0411.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=412) (base:=SynergyHeightC.FullMainFrame.base total 412) (input:=SourceMainFramesV1.Point0412.input) (pair:=SourceMainFramesV1.Point0412.outputs) SourceMainFramesV1.Point0412.input_defined SourceMainFramesV1.Point0412.outputs_defined (SourceMainFramesV1.Point0412.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=413) (base:=SynergyHeightC.FullMainFrame.base total 413) (input:=SourceMainFramesV1.Point0413.input) (pair:=SourceMainFramesV1.Point0413.outputs) SourceMainFramesV1.Point0413.input_defined SourceMainFramesV1.Point0413.outputs_defined (SourceMainFramesV1.Point0413.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=414) (base:=SynergyHeightC.FullMainFrame.base total 414) (input:=SourceMainFramesV1.Point0414.input) (pair:=SourceMainFramesV1.Point0414.outputs) SourceMainFramesV1.Point0414.input_defined SourceMainFramesV1.Point0414.outputs_defined (SourceMainFramesV1.Point0414.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=415) (base:=SynergyHeightC.FullMainFrame.base total 415) (input:=SourceMainFramesV1.Point0415.input) (pair:=SourceMainFramesV1.Point0415.outputs) SourceMainFramesV1.Point0415.input_defined SourceMainFramesV1.Point0415.outputs_defined (SourceMainFramesV1.Point0415.source_outputs total)
end SourceMainFramesV1.Block12
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Block12.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
