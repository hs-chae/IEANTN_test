import SourceMainFramesV1.Point0032
import SourceMainFramesV1.Point0033
import SourceMainFramesV1.Point0034
import SourceMainFramesV1.Point0035
import SourceMainFramesV1.Point0036
import SourceMainFramesV1.Point0037
import SourceMainFramesV1.Point0038
import SourceMainFramesV1.Point0039
import SourceMainFramesV1.Point0040
import SourceMainFramesV1.Point0041
import SourceMainFramesV1.Point0042
import SourceMainFramesV1.Point0043
import SourceMainFramesV1.Point0044
import SourceMainFramesV1.Point0045
import SourceMainFramesV1.Point0046
import SourceMainFramesV1.Point0047
import SourceMainFramesV1.Point0048
import SourceMainFramesV1.Point0049
import SourceMainFramesV1.Point0050
import SourceMainFramesV1.Point0051
import SourceMainFramesV1.Point0052
import SourceMainFramesV1.Point0053
import SourceMainFramesV1.Point0054
import SourceMainFramesV1.Point0055
import SourceMainFramesV1.Point0056
import SourceMainFramesV1.Point0057
import SourceMainFramesV1.Point0058
import SourceMainFramesV1.Point0059
import SourceMainFramesV1.Point0060
import SourceMainFramesV1.Point0061
import SourceMainFramesV1.Point0062
import SourceMainFramesV1.Point0063
import SourceMainFramesV1.PackOutput
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Block01
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (total : ProofBox) (i : ℕ) (lower : 32 ≤ i) (upper : i < 64) :
 ∃ base input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs base input c d := by
 interval_cases i
 · exact SourceMainFramesV1.pack_output (i:=32) (base:=SynergyHeightC.FullMainFrame.base total 32) (input:=SourceMainFramesV1.Point0032.input) (pair:=SourceMainFramesV1.Point0032.outputs) SourceMainFramesV1.Point0032.input_defined SourceMainFramesV1.Point0032.outputs_defined (SourceMainFramesV1.Point0032.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=33) (base:=SynergyHeightC.FullMainFrame.base total 33) (input:=SourceMainFramesV1.Point0033.input) (pair:=SourceMainFramesV1.Point0033.outputs) SourceMainFramesV1.Point0033.input_defined SourceMainFramesV1.Point0033.outputs_defined (SourceMainFramesV1.Point0033.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=34) (base:=SynergyHeightC.FullMainFrame.base total 34) (input:=SourceMainFramesV1.Point0034.input) (pair:=SourceMainFramesV1.Point0034.outputs) SourceMainFramesV1.Point0034.input_defined SourceMainFramesV1.Point0034.outputs_defined (SourceMainFramesV1.Point0034.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=35) (base:=SynergyHeightC.FullMainFrame.base total 35) (input:=SourceMainFramesV1.Point0035.input) (pair:=SourceMainFramesV1.Point0035.outputs) SourceMainFramesV1.Point0035.input_defined SourceMainFramesV1.Point0035.outputs_defined (SourceMainFramesV1.Point0035.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=36) (base:=SynergyHeightC.FullMainFrame.base total 36) (input:=SourceMainFramesV1.Point0036.input) (pair:=SourceMainFramesV1.Point0036.outputs) SourceMainFramesV1.Point0036.input_defined SourceMainFramesV1.Point0036.outputs_defined (SourceMainFramesV1.Point0036.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=37) (base:=SynergyHeightC.FullMainFrame.base total 37) (input:=SourceMainFramesV1.Point0037.input) (pair:=SourceMainFramesV1.Point0037.outputs) SourceMainFramesV1.Point0037.input_defined SourceMainFramesV1.Point0037.outputs_defined (SourceMainFramesV1.Point0037.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=38) (base:=SynergyHeightC.FullMainFrame.base total 38) (input:=SourceMainFramesV1.Point0038.input) (pair:=SourceMainFramesV1.Point0038.outputs) SourceMainFramesV1.Point0038.input_defined SourceMainFramesV1.Point0038.outputs_defined (SourceMainFramesV1.Point0038.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=39) (base:=SynergyHeightC.FullMainFrame.base total 39) (input:=SourceMainFramesV1.Point0039.input) (pair:=SourceMainFramesV1.Point0039.outputs) SourceMainFramesV1.Point0039.input_defined SourceMainFramesV1.Point0039.outputs_defined (SourceMainFramesV1.Point0039.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=40) (base:=SynergyHeightC.FullMainFrame.base total 40) (input:=SourceMainFramesV1.Point0040.input) (pair:=SourceMainFramesV1.Point0040.outputs) SourceMainFramesV1.Point0040.input_defined SourceMainFramesV1.Point0040.outputs_defined (SourceMainFramesV1.Point0040.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=41) (base:=SynergyHeightC.FullMainFrame.base total 41) (input:=SourceMainFramesV1.Point0041.input) (pair:=SourceMainFramesV1.Point0041.outputs) SourceMainFramesV1.Point0041.input_defined SourceMainFramesV1.Point0041.outputs_defined (SourceMainFramesV1.Point0041.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=42) (base:=SynergyHeightC.FullMainFrame.base total 42) (input:=SourceMainFramesV1.Point0042.input) (pair:=SourceMainFramesV1.Point0042.outputs) SourceMainFramesV1.Point0042.input_defined SourceMainFramesV1.Point0042.outputs_defined (SourceMainFramesV1.Point0042.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=43) (base:=SynergyHeightC.FullMainFrame.base total 43) (input:=SourceMainFramesV1.Point0043.input) (pair:=SourceMainFramesV1.Point0043.outputs) SourceMainFramesV1.Point0043.input_defined SourceMainFramesV1.Point0043.outputs_defined (SourceMainFramesV1.Point0043.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=44) (base:=SynergyHeightC.FullMainFrame.base total 44) (input:=SourceMainFramesV1.Point0044.input) (pair:=SourceMainFramesV1.Point0044.outputs) SourceMainFramesV1.Point0044.input_defined SourceMainFramesV1.Point0044.outputs_defined (SourceMainFramesV1.Point0044.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=45) (base:=SynergyHeightC.FullMainFrame.base total 45) (input:=SourceMainFramesV1.Point0045.input) (pair:=SourceMainFramesV1.Point0045.outputs) SourceMainFramesV1.Point0045.input_defined SourceMainFramesV1.Point0045.outputs_defined (SourceMainFramesV1.Point0045.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=46) (base:=SynergyHeightC.FullMainFrame.base total 46) (input:=SourceMainFramesV1.Point0046.input) (pair:=SourceMainFramesV1.Point0046.outputs) SourceMainFramesV1.Point0046.input_defined SourceMainFramesV1.Point0046.outputs_defined (SourceMainFramesV1.Point0046.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=47) (base:=SynergyHeightC.FullMainFrame.base total 47) (input:=SourceMainFramesV1.Point0047.input) (pair:=SourceMainFramesV1.Point0047.outputs) SourceMainFramesV1.Point0047.input_defined SourceMainFramesV1.Point0047.outputs_defined (SourceMainFramesV1.Point0047.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=48) (base:=SynergyHeightC.FullMainFrame.base total 48) (input:=SourceMainFramesV1.Point0048.input) (pair:=SourceMainFramesV1.Point0048.outputs) SourceMainFramesV1.Point0048.input_defined SourceMainFramesV1.Point0048.outputs_defined (SourceMainFramesV1.Point0048.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=49) (base:=SynergyHeightC.FullMainFrame.base total 49) (input:=SourceMainFramesV1.Point0049.input) (pair:=SourceMainFramesV1.Point0049.outputs) SourceMainFramesV1.Point0049.input_defined SourceMainFramesV1.Point0049.outputs_defined (SourceMainFramesV1.Point0049.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=50) (base:=SynergyHeightC.FullMainFrame.base total 50) (input:=SourceMainFramesV1.Point0050.input) (pair:=SourceMainFramesV1.Point0050.outputs) SourceMainFramesV1.Point0050.input_defined SourceMainFramesV1.Point0050.outputs_defined (SourceMainFramesV1.Point0050.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=51) (base:=SynergyHeightC.FullMainFrame.base total 51) (input:=SourceMainFramesV1.Point0051.input) (pair:=SourceMainFramesV1.Point0051.outputs) SourceMainFramesV1.Point0051.input_defined SourceMainFramesV1.Point0051.outputs_defined (SourceMainFramesV1.Point0051.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=52) (base:=SynergyHeightC.FullMainFrame.base total 52) (input:=SourceMainFramesV1.Point0052.input) (pair:=SourceMainFramesV1.Point0052.outputs) SourceMainFramesV1.Point0052.input_defined SourceMainFramesV1.Point0052.outputs_defined (SourceMainFramesV1.Point0052.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=53) (base:=SynergyHeightC.FullMainFrame.base total 53) (input:=SourceMainFramesV1.Point0053.input) (pair:=SourceMainFramesV1.Point0053.outputs) SourceMainFramesV1.Point0053.input_defined SourceMainFramesV1.Point0053.outputs_defined (SourceMainFramesV1.Point0053.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=54) (base:=SynergyHeightC.FullMainFrame.base total 54) (input:=SourceMainFramesV1.Point0054.input) (pair:=SourceMainFramesV1.Point0054.outputs) SourceMainFramesV1.Point0054.input_defined SourceMainFramesV1.Point0054.outputs_defined (SourceMainFramesV1.Point0054.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=55) (base:=SynergyHeightC.FullMainFrame.base total 55) (input:=SourceMainFramesV1.Point0055.input) (pair:=SourceMainFramesV1.Point0055.outputs) SourceMainFramesV1.Point0055.input_defined SourceMainFramesV1.Point0055.outputs_defined (SourceMainFramesV1.Point0055.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=56) (base:=SynergyHeightC.FullMainFrame.base total 56) (input:=SourceMainFramesV1.Point0056.input) (pair:=SourceMainFramesV1.Point0056.outputs) SourceMainFramesV1.Point0056.input_defined SourceMainFramesV1.Point0056.outputs_defined (SourceMainFramesV1.Point0056.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=57) (base:=SynergyHeightC.FullMainFrame.base total 57) (input:=SourceMainFramesV1.Point0057.input) (pair:=SourceMainFramesV1.Point0057.outputs) SourceMainFramesV1.Point0057.input_defined SourceMainFramesV1.Point0057.outputs_defined (SourceMainFramesV1.Point0057.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=58) (base:=SynergyHeightC.FullMainFrame.base total 58) (input:=SourceMainFramesV1.Point0058.input) (pair:=SourceMainFramesV1.Point0058.outputs) SourceMainFramesV1.Point0058.input_defined SourceMainFramesV1.Point0058.outputs_defined (SourceMainFramesV1.Point0058.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=59) (base:=SynergyHeightC.FullMainFrame.base total 59) (input:=SourceMainFramesV1.Point0059.input) (pair:=SourceMainFramesV1.Point0059.outputs) SourceMainFramesV1.Point0059.input_defined SourceMainFramesV1.Point0059.outputs_defined (SourceMainFramesV1.Point0059.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=60) (base:=SynergyHeightC.FullMainFrame.base total 60) (input:=SourceMainFramesV1.Point0060.input) (pair:=SourceMainFramesV1.Point0060.outputs) SourceMainFramesV1.Point0060.input_defined SourceMainFramesV1.Point0060.outputs_defined (SourceMainFramesV1.Point0060.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=61) (base:=SynergyHeightC.FullMainFrame.base total 61) (input:=SourceMainFramesV1.Point0061.input) (pair:=SourceMainFramesV1.Point0061.outputs) SourceMainFramesV1.Point0061.input_defined SourceMainFramesV1.Point0061.outputs_defined (SourceMainFramesV1.Point0061.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=62) (base:=SynergyHeightC.FullMainFrame.base total 62) (input:=SourceMainFramesV1.Point0062.input) (pair:=SourceMainFramesV1.Point0062.outputs) SourceMainFramesV1.Point0062.input_defined SourceMainFramesV1.Point0062.outputs_defined (SourceMainFramesV1.Point0062.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=63) (base:=SynergyHeightC.FullMainFrame.base total 63) (input:=SourceMainFramesV1.Point0063.input) (pair:=SourceMainFramesV1.Point0063.outputs) SourceMainFramesV1.Point0063.input_defined SourceMainFramesV1.Point0063.outputs_defined (SourceMainFramesV1.Point0063.source_outputs total)
end SourceMainFramesV1.Block01
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Block01.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
