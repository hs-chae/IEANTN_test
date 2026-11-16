import SourceMainFramesV1.Point0000
import SourceMainFramesV1.Point0001
import SourceMainFramesV1.Point0002
import SourceMainFramesV1.Point0003
import SourceMainFramesV1.Point0004
import SourceMainFramesV1.Point0005
import SourceMainFramesV1.Point0006
import SourceMainFramesV1.Point0007
import SourceMainFramesV1.Point0008
import SourceMainFramesV1.Point0009
import SourceMainFramesV1.Point0010
import SourceMainFramesV1.Point0011
import SourceMainFramesV1.Point0012
import SourceMainFramesV1.Point0013
import SourceMainFramesV1.Point0014
import SourceMainFramesV1.Point0015
import SourceMainFramesV1.Point0016
import SourceMainFramesV1.Point0017
import SourceMainFramesV1.Point0018
import SourceMainFramesV1.Point0019
import SourceMainFramesV1.Point0020
import SourceMainFramesV1.Point0021
import SourceMainFramesV1.Point0022
import SourceMainFramesV1.Point0023
import SourceMainFramesV1.Point0024
import SourceMainFramesV1.Point0025
import SourceMainFramesV1.Point0026
import SourceMainFramesV1.Point0027
import SourceMainFramesV1.Point0028
import SourceMainFramesV1.Point0029
import SourceMainFramesV1.Point0030
import SourceMainFramesV1.Point0031
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Block00
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (total : ProofBox) (i : ℕ) (lower : 0 ≤ i) (upper : i < 32) :
 ∃ base input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs base input c d := by
 interval_cases i
 · exact ⟨SynergyHeightC.FullMainFrame.base total 0,SourceMainFramesV1.Point0000.input,SourceMainFramesV1.Point0000.outputs.1,SourceMainFramesV1.Point0000.outputs.2,SourceMainFramesV1.Point0000.input_defined,SourceMainFramesV1.Point0000.outputs_defined,SourceMainFramesV1.Point0000.source_outputs total⟩
 · exact ⟨SynergyHeightC.FullMainFrame.base total 1,SourceMainFramesV1.Point0001.input,SourceMainFramesV1.Point0001.outputs.1,SourceMainFramesV1.Point0001.outputs.2,SourceMainFramesV1.Point0001.input_defined,SourceMainFramesV1.Point0001.outputs_defined,SourceMainFramesV1.Point0001.source_outputs total⟩
 · exact ⟨SynergyHeightC.FullMainFrame.base total 2,SourceMainFramesV1.Point0002.input,SourceMainFramesV1.Point0002.outputs.1,SourceMainFramesV1.Point0002.outputs.2,SourceMainFramesV1.Point0002.input_defined,SourceMainFramesV1.Point0002.outputs_defined,SourceMainFramesV1.Point0002.source_outputs total⟩
 · exact ⟨SynergyHeightC.FullMainFrame.base total 3,SourceMainFramesV1.Point0003.input,SourceMainFramesV1.Point0003.outputs.1,SourceMainFramesV1.Point0003.outputs.2,SourceMainFramesV1.Point0003.input_defined,SourceMainFramesV1.Point0003.outputs_defined,SourceMainFramesV1.Point0003.source_outputs total⟩
 · exact ⟨SynergyHeightC.FullMainFrame.base total 4,SourceMainFramesV1.Point0004.input,SourceMainFramesV1.Point0004.outputs.1,SourceMainFramesV1.Point0004.outputs.2,SourceMainFramesV1.Point0004.input_defined,SourceMainFramesV1.Point0004.outputs_defined,SourceMainFramesV1.Point0004.source_outputs total⟩
 · exact ⟨SynergyHeightC.FullMainFrame.base total 5,SourceMainFramesV1.Point0005.input,SourceMainFramesV1.Point0005.outputs.1,SourceMainFramesV1.Point0005.outputs.2,SourceMainFramesV1.Point0005.input_defined,SourceMainFramesV1.Point0005.outputs_defined,SourceMainFramesV1.Point0005.source_outputs total⟩
 · exact ⟨SynergyHeightC.FullMainFrame.base total 6,SourceMainFramesV1.Point0006.input,SourceMainFramesV1.Point0006.outputs.1,SourceMainFramesV1.Point0006.outputs.2,SourceMainFramesV1.Point0006.input_defined,SourceMainFramesV1.Point0006.outputs_defined,SourceMainFramesV1.Point0006.source_outputs total⟩
 · exact ⟨SynergyHeightC.FullMainFrame.base total 7,SourceMainFramesV1.Point0007.input,SourceMainFramesV1.Point0007.outputs.1,SourceMainFramesV1.Point0007.outputs.2,SourceMainFramesV1.Point0007.input_defined,SourceMainFramesV1.Point0007.outputs_defined,SourceMainFramesV1.Point0007.source_outputs total⟩
 · exact ⟨SynergyHeightC.FullMainFrame.base total 8,SourceMainFramesV1.Point0008.input,SourceMainFramesV1.Point0008.outputs.1,SourceMainFramesV1.Point0008.outputs.2,SourceMainFramesV1.Point0008.input_defined,SourceMainFramesV1.Point0008.outputs_defined,SourceMainFramesV1.Point0008.source_outputs total⟩
 · exact ⟨SynergyHeightC.FullMainFrame.base total 9,SourceMainFramesV1.Point0009.input,SourceMainFramesV1.Point0009.outputs.1,SourceMainFramesV1.Point0009.outputs.2,SourceMainFramesV1.Point0009.input_defined,SourceMainFramesV1.Point0009.outputs_defined,SourceMainFramesV1.Point0009.source_outputs total⟩
 · exact ⟨SynergyHeightC.FullMainFrame.base total 10,SourceMainFramesV1.Point0010.input,SourceMainFramesV1.Point0010.outputs.1,SourceMainFramesV1.Point0010.outputs.2,SourceMainFramesV1.Point0010.input_defined,SourceMainFramesV1.Point0010.outputs_defined,SourceMainFramesV1.Point0010.source_outputs total⟩
 · exact ⟨SynergyHeightC.FullMainFrame.base total 11,SourceMainFramesV1.Point0011.input,SourceMainFramesV1.Point0011.outputs.1,SourceMainFramesV1.Point0011.outputs.2,SourceMainFramesV1.Point0011.input_defined,SourceMainFramesV1.Point0011.outputs_defined,SourceMainFramesV1.Point0011.source_outputs total⟩
 · exact ⟨SynergyHeightC.FullMainFrame.base total 12,SourceMainFramesV1.Point0012.input,SourceMainFramesV1.Point0012.outputs.1,SourceMainFramesV1.Point0012.outputs.2,SourceMainFramesV1.Point0012.input_defined,SourceMainFramesV1.Point0012.outputs_defined,SourceMainFramesV1.Point0012.source_outputs total⟩
 · exact ⟨SynergyHeightC.FullMainFrame.base total 13,SourceMainFramesV1.Point0013.input,SourceMainFramesV1.Point0013.outputs.1,SourceMainFramesV1.Point0013.outputs.2,SourceMainFramesV1.Point0013.input_defined,SourceMainFramesV1.Point0013.outputs_defined,SourceMainFramesV1.Point0013.source_outputs total⟩
 · exact ⟨SynergyHeightC.FullMainFrame.base total 14,SourceMainFramesV1.Point0014.input,SourceMainFramesV1.Point0014.outputs.1,SourceMainFramesV1.Point0014.outputs.2,SourceMainFramesV1.Point0014.input_defined,SourceMainFramesV1.Point0014.outputs_defined,SourceMainFramesV1.Point0014.source_outputs total⟩
 · exact ⟨SynergyHeightC.FullMainFrame.base total 15,SourceMainFramesV1.Point0015.input,SourceMainFramesV1.Point0015.outputs.1,SourceMainFramesV1.Point0015.outputs.2,SourceMainFramesV1.Point0015.input_defined,SourceMainFramesV1.Point0015.outputs_defined,SourceMainFramesV1.Point0015.source_outputs total⟩
 · exact ⟨SynergyHeightC.FullMainFrame.base total 16,SourceMainFramesV1.Point0016.input,SourceMainFramesV1.Point0016.outputs.1,SourceMainFramesV1.Point0016.outputs.2,SourceMainFramesV1.Point0016.input_defined,SourceMainFramesV1.Point0016.outputs_defined,SourceMainFramesV1.Point0016.source_outputs total⟩
 · exact ⟨SynergyHeightC.FullMainFrame.base total 17,SourceMainFramesV1.Point0017.input,SourceMainFramesV1.Point0017.outputs.1,SourceMainFramesV1.Point0017.outputs.2,SourceMainFramesV1.Point0017.input_defined,SourceMainFramesV1.Point0017.outputs_defined,SourceMainFramesV1.Point0017.source_outputs total⟩
 · exact ⟨SynergyHeightC.FullMainFrame.base total 18,SourceMainFramesV1.Point0018.input,SourceMainFramesV1.Point0018.outputs.1,SourceMainFramesV1.Point0018.outputs.2,SourceMainFramesV1.Point0018.input_defined,SourceMainFramesV1.Point0018.outputs_defined,SourceMainFramesV1.Point0018.source_outputs total⟩
 · exact ⟨SynergyHeightC.FullMainFrame.base total 19,SourceMainFramesV1.Point0019.input,SourceMainFramesV1.Point0019.outputs.1,SourceMainFramesV1.Point0019.outputs.2,SourceMainFramesV1.Point0019.input_defined,SourceMainFramesV1.Point0019.outputs_defined,SourceMainFramesV1.Point0019.source_outputs total⟩
 · exact ⟨SynergyHeightC.FullMainFrame.base total 20,SourceMainFramesV1.Point0020.input,SourceMainFramesV1.Point0020.outputs.1,SourceMainFramesV1.Point0020.outputs.2,SourceMainFramesV1.Point0020.input_defined,SourceMainFramesV1.Point0020.outputs_defined,SourceMainFramesV1.Point0020.source_outputs total⟩
 · exact ⟨SynergyHeightC.FullMainFrame.base total 21,SourceMainFramesV1.Point0021.input,SourceMainFramesV1.Point0021.outputs.1,SourceMainFramesV1.Point0021.outputs.2,SourceMainFramesV1.Point0021.input_defined,SourceMainFramesV1.Point0021.outputs_defined,SourceMainFramesV1.Point0021.source_outputs total⟩
 · exact ⟨SynergyHeightC.FullMainFrame.base total 22,SourceMainFramesV1.Point0022.input,SourceMainFramesV1.Point0022.outputs.1,SourceMainFramesV1.Point0022.outputs.2,SourceMainFramesV1.Point0022.input_defined,SourceMainFramesV1.Point0022.outputs_defined,SourceMainFramesV1.Point0022.source_outputs total⟩
 · exact ⟨SynergyHeightC.FullMainFrame.base total 23,SourceMainFramesV1.Point0023.input,SourceMainFramesV1.Point0023.outputs.1,SourceMainFramesV1.Point0023.outputs.2,SourceMainFramesV1.Point0023.input_defined,SourceMainFramesV1.Point0023.outputs_defined,SourceMainFramesV1.Point0023.source_outputs total⟩
 · exact ⟨SynergyHeightC.FullMainFrame.base total 24,SourceMainFramesV1.Point0024.input,SourceMainFramesV1.Point0024.outputs.1,SourceMainFramesV1.Point0024.outputs.2,SourceMainFramesV1.Point0024.input_defined,SourceMainFramesV1.Point0024.outputs_defined,SourceMainFramesV1.Point0024.source_outputs total⟩
 · exact ⟨SynergyHeightC.FullMainFrame.base total 25,SourceMainFramesV1.Point0025.input,SourceMainFramesV1.Point0025.outputs.1,SourceMainFramesV1.Point0025.outputs.2,SourceMainFramesV1.Point0025.input_defined,SourceMainFramesV1.Point0025.outputs_defined,SourceMainFramesV1.Point0025.source_outputs total⟩
 · exact ⟨SynergyHeightC.FullMainFrame.base total 26,SourceMainFramesV1.Point0026.input,SourceMainFramesV1.Point0026.outputs.1,SourceMainFramesV1.Point0026.outputs.2,SourceMainFramesV1.Point0026.input_defined,SourceMainFramesV1.Point0026.outputs_defined,SourceMainFramesV1.Point0026.source_outputs total⟩
 · exact ⟨SynergyHeightC.FullMainFrame.base total 27,SourceMainFramesV1.Point0027.input,SourceMainFramesV1.Point0027.outputs.1,SourceMainFramesV1.Point0027.outputs.2,SourceMainFramesV1.Point0027.input_defined,SourceMainFramesV1.Point0027.outputs_defined,SourceMainFramesV1.Point0027.source_outputs total⟩
 · exact ⟨SynergyHeightC.FullMainFrame.base total 28,SourceMainFramesV1.Point0028.input,SourceMainFramesV1.Point0028.outputs.1,SourceMainFramesV1.Point0028.outputs.2,SourceMainFramesV1.Point0028.input_defined,SourceMainFramesV1.Point0028.outputs_defined,SourceMainFramesV1.Point0028.source_outputs total⟩
 · exact ⟨SynergyHeightC.FullMainFrame.base total 29,SourceMainFramesV1.Point0029.input,SourceMainFramesV1.Point0029.outputs.1,SourceMainFramesV1.Point0029.outputs.2,SourceMainFramesV1.Point0029.input_defined,SourceMainFramesV1.Point0029.outputs_defined,SourceMainFramesV1.Point0029.source_outputs total⟩
 · exact ⟨SynergyHeightC.FullMainFrame.base total 30,SourceMainFramesV1.Point0030.input,SourceMainFramesV1.Point0030.outputs.1,SourceMainFramesV1.Point0030.outputs.2,SourceMainFramesV1.Point0030.input_defined,SourceMainFramesV1.Point0030.outputs_defined,SourceMainFramesV1.Point0030.source_outputs total⟩
 · exact ⟨SynergyHeightC.FullMainFrame.base total 31,SourceMainFramesV1.Point0031.input,SourceMainFramesV1.Point0031.outputs.1,SourceMainFramesV1.Point0031.outputs.2,SourceMainFramesV1.Point0031.input_defined,SourceMainFramesV1.Point0031.outputs_defined,SourceMainFramesV1.Point0031.source_outputs total⟩
end SourceMainFramesV1.Block00
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Block00.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
