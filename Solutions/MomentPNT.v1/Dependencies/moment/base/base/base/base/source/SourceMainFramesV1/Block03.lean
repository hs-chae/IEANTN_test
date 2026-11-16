import SourceMainFramesV1.Point0096
import SourceMainFramesV1.Point0097
import SourceMainFramesV1.Point0098
import SourceMainFramesV1.Point0099
import SourceMainFramesV1.Point0100
import SourceMainFramesV1.Point0101
import SourceMainFramesV1.Point0102
import SourceMainFramesV1.Point0103
import SourceMainFramesV1.Point0104
import SourceMainFramesV1.Point0105
import SourceMainFramesV1.Point0106
import SourceMainFramesV1.Point0107
import SourceMainFramesV1.Point0108
import SourceMainFramesV1.Point0109
import SourceMainFramesV1.Point0110
import SourceMainFramesV1.Point0111
import SourceMainFramesV1.Point0112
import SourceMainFramesV1.Point0113
import SourceMainFramesV1.Point0114
import SourceMainFramesV1.Point0115
import SourceMainFramesV1.Point0116
import SourceMainFramesV1.Point0117
import SourceMainFramesV1.Point0118
import SourceMainFramesV1.Point0119
import SourceMainFramesV1.Point0120
import SourceMainFramesV1.Point0121
import SourceMainFramesV1.Point0122
import SourceMainFramesV1.Point0123
import SourceMainFramesV1.Point0124
import SourceMainFramesV1.Point0125
import SourceMainFramesV1.Point0126
import SourceMainFramesV1.Point0127
import SourceMainFramesV1.PackOutput
import Mathlib.Tactic.IntervalCases
namespace SourceMainFramesV1.Block03
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- All32 actual same-buffer outputs, with their exact log-grid inputs. -/
theorem outputs (total : ProofBox) (i : ℕ) (lower : 96 ≤ i) (upper : i < 128) :
 ∃ base input c d, logCell (i+1)=some input ∧ modelOutputs input=some (c,d) ∧
 SourcePointOutputs base input c d := by
 interval_cases i
 · exact SourceMainFramesV1.pack_output (i:=96) (base:=SynergyHeightC.FullMainFrame.base total 96) (input:=SourceMainFramesV1.Point0096.input) (pair:=SourceMainFramesV1.Point0096.outputs) SourceMainFramesV1.Point0096.input_defined SourceMainFramesV1.Point0096.outputs_defined (SourceMainFramesV1.Point0096.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=97) (base:=SynergyHeightC.FullMainFrame.base total 97) (input:=SourceMainFramesV1.Point0097.input) (pair:=SourceMainFramesV1.Point0097.outputs) SourceMainFramesV1.Point0097.input_defined SourceMainFramesV1.Point0097.outputs_defined (SourceMainFramesV1.Point0097.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=98) (base:=SynergyHeightC.FullMainFrame.base total 98) (input:=SourceMainFramesV1.Point0098.input) (pair:=SourceMainFramesV1.Point0098.outputs) SourceMainFramesV1.Point0098.input_defined SourceMainFramesV1.Point0098.outputs_defined (SourceMainFramesV1.Point0098.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=99) (base:=SynergyHeightC.FullMainFrame.base total 99) (input:=SourceMainFramesV1.Point0099.input) (pair:=SourceMainFramesV1.Point0099.outputs) SourceMainFramesV1.Point0099.input_defined SourceMainFramesV1.Point0099.outputs_defined (SourceMainFramesV1.Point0099.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=100) (base:=SynergyHeightC.FullMainFrame.base total 100) (input:=SourceMainFramesV1.Point0100.input) (pair:=SourceMainFramesV1.Point0100.outputs) SourceMainFramesV1.Point0100.input_defined SourceMainFramesV1.Point0100.outputs_defined (SourceMainFramesV1.Point0100.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=101) (base:=SynergyHeightC.FullMainFrame.base total 101) (input:=SourceMainFramesV1.Point0101.input) (pair:=SourceMainFramesV1.Point0101.outputs) SourceMainFramesV1.Point0101.input_defined SourceMainFramesV1.Point0101.outputs_defined (SourceMainFramesV1.Point0101.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=102) (base:=SynergyHeightC.FullMainFrame.base total 102) (input:=SourceMainFramesV1.Point0102.input) (pair:=SourceMainFramesV1.Point0102.outputs) SourceMainFramesV1.Point0102.input_defined SourceMainFramesV1.Point0102.outputs_defined (SourceMainFramesV1.Point0102.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=103) (base:=SynergyHeightC.FullMainFrame.base total 103) (input:=SourceMainFramesV1.Point0103.input) (pair:=SourceMainFramesV1.Point0103.outputs) SourceMainFramesV1.Point0103.input_defined SourceMainFramesV1.Point0103.outputs_defined (SourceMainFramesV1.Point0103.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=104) (base:=SynergyHeightC.FullMainFrame.base total 104) (input:=SourceMainFramesV1.Point0104.input) (pair:=SourceMainFramesV1.Point0104.outputs) SourceMainFramesV1.Point0104.input_defined SourceMainFramesV1.Point0104.outputs_defined (SourceMainFramesV1.Point0104.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=105) (base:=SynergyHeightC.FullMainFrame.base total 105) (input:=SourceMainFramesV1.Point0105.input) (pair:=SourceMainFramesV1.Point0105.outputs) SourceMainFramesV1.Point0105.input_defined SourceMainFramesV1.Point0105.outputs_defined (SourceMainFramesV1.Point0105.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=106) (base:=SynergyHeightC.FullMainFrame.base total 106) (input:=SourceMainFramesV1.Point0106.input) (pair:=SourceMainFramesV1.Point0106.outputs) SourceMainFramesV1.Point0106.input_defined SourceMainFramesV1.Point0106.outputs_defined (SourceMainFramesV1.Point0106.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=107) (base:=SynergyHeightC.FullMainFrame.base total 107) (input:=SourceMainFramesV1.Point0107.input) (pair:=SourceMainFramesV1.Point0107.outputs) SourceMainFramesV1.Point0107.input_defined SourceMainFramesV1.Point0107.outputs_defined (SourceMainFramesV1.Point0107.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=108) (base:=SynergyHeightC.FullMainFrame.base total 108) (input:=SourceMainFramesV1.Point0108.input) (pair:=SourceMainFramesV1.Point0108.outputs) SourceMainFramesV1.Point0108.input_defined SourceMainFramesV1.Point0108.outputs_defined (SourceMainFramesV1.Point0108.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=109) (base:=SynergyHeightC.FullMainFrame.base total 109) (input:=SourceMainFramesV1.Point0109.input) (pair:=SourceMainFramesV1.Point0109.outputs) SourceMainFramesV1.Point0109.input_defined SourceMainFramesV1.Point0109.outputs_defined (SourceMainFramesV1.Point0109.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=110) (base:=SynergyHeightC.FullMainFrame.base total 110) (input:=SourceMainFramesV1.Point0110.input) (pair:=SourceMainFramesV1.Point0110.outputs) SourceMainFramesV1.Point0110.input_defined SourceMainFramesV1.Point0110.outputs_defined (SourceMainFramesV1.Point0110.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=111) (base:=SynergyHeightC.FullMainFrame.base total 111) (input:=SourceMainFramesV1.Point0111.input) (pair:=SourceMainFramesV1.Point0111.outputs) SourceMainFramesV1.Point0111.input_defined SourceMainFramesV1.Point0111.outputs_defined (SourceMainFramesV1.Point0111.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=112) (base:=SynergyHeightC.FullMainFrame.base total 112) (input:=SourceMainFramesV1.Point0112.input) (pair:=SourceMainFramesV1.Point0112.outputs) SourceMainFramesV1.Point0112.input_defined SourceMainFramesV1.Point0112.outputs_defined (SourceMainFramesV1.Point0112.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=113) (base:=SynergyHeightC.FullMainFrame.base total 113) (input:=SourceMainFramesV1.Point0113.input) (pair:=SourceMainFramesV1.Point0113.outputs) SourceMainFramesV1.Point0113.input_defined SourceMainFramesV1.Point0113.outputs_defined (SourceMainFramesV1.Point0113.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=114) (base:=SynergyHeightC.FullMainFrame.base total 114) (input:=SourceMainFramesV1.Point0114.input) (pair:=SourceMainFramesV1.Point0114.outputs) SourceMainFramesV1.Point0114.input_defined SourceMainFramesV1.Point0114.outputs_defined (SourceMainFramesV1.Point0114.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=115) (base:=SynergyHeightC.FullMainFrame.base total 115) (input:=SourceMainFramesV1.Point0115.input) (pair:=SourceMainFramesV1.Point0115.outputs) SourceMainFramesV1.Point0115.input_defined SourceMainFramesV1.Point0115.outputs_defined (SourceMainFramesV1.Point0115.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=116) (base:=SynergyHeightC.FullMainFrame.base total 116) (input:=SourceMainFramesV1.Point0116.input) (pair:=SourceMainFramesV1.Point0116.outputs) SourceMainFramesV1.Point0116.input_defined SourceMainFramesV1.Point0116.outputs_defined (SourceMainFramesV1.Point0116.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=117) (base:=SynergyHeightC.FullMainFrame.base total 117) (input:=SourceMainFramesV1.Point0117.input) (pair:=SourceMainFramesV1.Point0117.outputs) SourceMainFramesV1.Point0117.input_defined SourceMainFramesV1.Point0117.outputs_defined (SourceMainFramesV1.Point0117.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=118) (base:=SynergyHeightC.FullMainFrame.base total 118) (input:=SourceMainFramesV1.Point0118.input) (pair:=SourceMainFramesV1.Point0118.outputs) SourceMainFramesV1.Point0118.input_defined SourceMainFramesV1.Point0118.outputs_defined (SourceMainFramesV1.Point0118.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=119) (base:=SynergyHeightC.FullMainFrame.base total 119) (input:=SourceMainFramesV1.Point0119.input) (pair:=SourceMainFramesV1.Point0119.outputs) SourceMainFramesV1.Point0119.input_defined SourceMainFramesV1.Point0119.outputs_defined (SourceMainFramesV1.Point0119.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=120) (base:=SynergyHeightC.FullMainFrame.base total 120) (input:=SourceMainFramesV1.Point0120.input) (pair:=SourceMainFramesV1.Point0120.outputs) SourceMainFramesV1.Point0120.input_defined SourceMainFramesV1.Point0120.outputs_defined (SourceMainFramesV1.Point0120.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=121) (base:=SynergyHeightC.FullMainFrame.base total 121) (input:=SourceMainFramesV1.Point0121.input) (pair:=SourceMainFramesV1.Point0121.outputs) SourceMainFramesV1.Point0121.input_defined SourceMainFramesV1.Point0121.outputs_defined (SourceMainFramesV1.Point0121.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=122) (base:=SynergyHeightC.FullMainFrame.base total 122) (input:=SourceMainFramesV1.Point0122.input) (pair:=SourceMainFramesV1.Point0122.outputs) SourceMainFramesV1.Point0122.input_defined SourceMainFramesV1.Point0122.outputs_defined (SourceMainFramesV1.Point0122.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=123) (base:=SynergyHeightC.FullMainFrame.base total 123) (input:=SourceMainFramesV1.Point0123.input) (pair:=SourceMainFramesV1.Point0123.outputs) SourceMainFramesV1.Point0123.input_defined SourceMainFramesV1.Point0123.outputs_defined (SourceMainFramesV1.Point0123.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=124) (base:=SynergyHeightC.FullMainFrame.base total 124) (input:=SourceMainFramesV1.Point0124.input) (pair:=SourceMainFramesV1.Point0124.outputs) SourceMainFramesV1.Point0124.input_defined SourceMainFramesV1.Point0124.outputs_defined (SourceMainFramesV1.Point0124.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=125) (base:=SynergyHeightC.FullMainFrame.base total 125) (input:=SourceMainFramesV1.Point0125.input) (pair:=SourceMainFramesV1.Point0125.outputs) SourceMainFramesV1.Point0125.input_defined SourceMainFramesV1.Point0125.outputs_defined (SourceMainFramesV1.Point0125.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=126) (base:=SynergyHeightC.FullMainFrame.base total 126) (input:=SourceMainFramesV1.Point0126.input) (pair:=SourceMainFramesV1.Point0126.outputs) SourceMainFramesV1.Point0126.input_defined SourceMainFramesV1.Point0126.outputs_defined (SourceMainFramesV1.Point0126.source_outputs total)
 · exact SourceMainFramesV1.pack_output (i:=127) (base:=SynergyHeightC.FullMainFrame.base total 127) (input:=SourceMainFramesV1.Point0127.input) (pair:=SourceMainFramesV1.Point0127.outputs) SourceMainFramesV1.Point0127.input_defined SourceMainFramesV1.Point0127.outputs_defined (SourceMainFramesV1.Point0127.source_outputs total)
end SourceMainFramesV1.Block03
open Lean Elab
run_elab do
 let n := `SourceMainFramesV1.Block03.outputs
 let env ← getEnv
 let some ci := env.find? n | throwError "missing provider {n}"
 let ax ← Lean.collectAxioms n
 logInfo m!"BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
