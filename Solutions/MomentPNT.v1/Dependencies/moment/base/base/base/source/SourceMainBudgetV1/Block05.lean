import SourceMainBudgetV1.Cell0160
import SourceHeightEdgesV1.Edge0160
import SourceMainBudgetV1.Cell0161
import SourceHeightEdgesV1.Edge0161
import SourceMainBudgetV1.Cell0162
import SourceHeightEdgesV1.Edge0162
import SourceMainBudgetV1.Cell0163
import SourceHeightEdgesV1.Edge0163
import SourceMainBudgetV1.Cell0164
import SourceHeightEdgesV1.Edge0164
import SourceMainBudgetV1.Cell0165
import SourceHeightEdgesV1.Edge0165
import SourceMainBudgetV1.Cell0166
import SourceHeightEdgesV1.Edge0166
import SourceMainBudgetV1.Cell0167
import SourceHeightEdgesV1.Edge0167
import SourceMainBudgetV1.Cell0168
import SourceHeightEdgesV1.Edge0168
import SourceMainBudgetV1.Cell0169
import SourceHeightEdgesV1.Edge0169
import SourceMainBudgetV1.Cell0170
import SourceHeightEdgesV1.Edge0170
import SourceMainBudgetV1.Cell0171
import SourceHeightEdgesV1.Edge0171
import SourceMainBudgetV1.Cell0172
import SourceHeightEdgesV1.Edge0172
import SourceMainBudgetV1.Cell0173
import SourceHeightEdgesV1.Edge0173
import SourceMainBudgetV1.Cell0174
import SourceHeightEdgesV1.Edge0174
import SourceMainBudgetV1.Cell0175
import SourceHeightEdgesV1.Edge0175
import SourceMainBudgetV1.Cell0176
import SourceHeightEdgesV1.Edge0176
import SourceMainBudgetV1.Cell0177
import SourceHeightEdgesV1.Edge0177
import SourceMainBudgetV1.Cell0178
import SourceHeightEdgesV1.Edge0178
import SourceMainBudgetV1.Cell0179
import SourceHeightEdgesV1.Edge0179
import SourceMainBudgetV1.Cell0180
import SourceHeightEdgesV1.Edge0180
import SourceMainBudgetV1.Cell0181
import SourceHeightEdgesV1.Edge0181
import SourceMainBudgetV1.Cell0182
import SourceHeightEdgesV1.Edge0182
import SourceMainBudgetV1.Cell0183
import SourceHeightEdgesV1.Edge0183
import SourceMainBudgetV1.Cell0184
import SourceHeightEdgesV1.Edge0184
import SourceMainBudgetV1.Cell0185
import SourceHeightEdgesV1.Edge0185
import SourceMainBudgetV1.Cell0186
import SourceHeightEdgesV1.Edge0186
import SourceMainBudgetV1.Cell0187
import SourceHeightEdgesV1.Edge0187
import SourceMainBudgetV1.Cell0188
import SourceHeightEdgesV1.Edge0188
import SourceMainBudgetV1.Cell0189
import SourceHeightEdgesV1.Edge0189
import SourceMainBudgetV1.Cell0190
import SourceHeightEdgesV1.Edge0190
import SourceMainBudgetV1.Cell0191
import SourceHeightEdgesV1.Edge0191
import SourceMainBudgetV1.Data
import Mathlib.Tactic.IntervalCases
namespace SourceMainBudgetV1.Block05
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem all (i : Nat) (lower : 160 ≤ i) (upper : i < 192) :
 SourceMainBudgetV1.Data.Cell i := by
 interval_cases i
 · exact SourceMainBudgetV1.Data.pack (i:=160) (input:=SourceMainFramesV1.Point0160.input) (pair:=SourceMainFramesV1.Point0160.outputs) SourceHeightEdgesV1.Edge0160.left_defined SourceMainFramesV1.Point0160.input_defined SourceMainFramesV1.Point0160.outputs_defined SourceMainBudgetV1.Cell0160.execution SourceMainBudgetV1.Cell0160.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=161) (input:=SourceMainFramesV1.Point0161.input) (pair:=SourceMainFramesV1.Point0161.outputs) SourceHeightEdgesV1.Edge0161.left_defined SourceMainFramesV1.Point0161.input_defined SourceMainFramesV1.Point0161.outputs_defined SourceMainBudgetV1.Cell0161.execution SourceMainBudgetV1.Cell0161.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=162) (input:=SourceMainFramesV1.Point0162.input) (pair:=SourceMainFramesV1.Point0162.outputs) SourceHeightEdgesV1.Edge0162.left_defined SourceMainFramesV1.Point0162.input_defined SourceMainFramesV1.Point0162.outputs_defined SourceMainBudgetV1.Cell0162.execution SourceMainBudgetV1.Cell0162.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=163) (input:=SourceMainFramesV1.Point0163.input) (pair:=SourceMainFramesV1.Point0163.outputs) SourceHeightEdgesV1.Edge0163.left_defined SourceMainFramesV1.Point0163.input_defined SourceMainFramesV1.Point0163.outputs_defined SourceMainBudgetV1.Cell0163.execution SourceMainBudgetV1.Cell0163.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=164) (input:=SourceMainFramesV1.Point0164.input) (pair:=SourceMainFramesV1.Point0164.outputs) SourceHeightEdgesV1.Edge0164.left_defined SourceMainFramesV1.Point0164.input_defined SourceMainFramesV1.Point0164.outputs_defined SourceMainBudgetV1.Cell0164.execution SourceMainBudgetV1.Cell0164.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=165) (input:=SourceMainFramesV1.Point0165.input) (pair:=SourceMainFramesV1.Point0165.outputs) SourceHeightEdgesV1.Edge0165.left_defined SourceMainFramesV1.Point0165.input_defined SourceMainFramesV1.Point0165.outputs_defined SourceMainBudgetV1.Cell0165.execution SourceMainBudgetV1.Cell0165.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=166) (input:=SourceMainFramesV1.Point0166.input) (pair:=SourceMainFramesV1.Point0166.outputs) SourceHeightEdgesV1.Edge0166.left_defined SourceMainFramesV1.Point0166.input_defined SourceMainFramesV1.Point0166.outputs_defined SourceMainBudgetV1.Cell0166.execution SourceMainBudgetV1.Cell0166.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=167) (input:=SourceMainFramesV1.Point0167.input) (pair:=SourceMainFramesV1.Point0167.outputs) SourceHeightEdgesV1.Edge0167.left_defined SourceMainFramesV1.Point0167.input_defined SourceMainFramesV1.Point0167.outputs_defined SourceMainBudgetV1.Cell0167.execution SourceMainBudgetV1.Cell0167.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=168) (input:=SourceMainFramesV1.Point0168.input) (pair:=SourceMainFramesV1.Point0168.outputs) SourceHeightEdgesV1.Edge0168.left_defined SourceMainFramesV1.Point0168.input_defined SourceMainFramesV1.Point0168.outputs_defined SourceMainBudgetV1.Cell0168.execution SourceMainBudgetV1.Cell0168.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=169) (input:=SourceMainFramesV1.Point0169.input) (pair:=SourceMainFramesV1.Point0169.outputs) SourceHeightEdgesV1.Edge0169.left_defined SourceMainFramesV1.Point0169.input_defined SourceMainFramesV1.Point0169.outputs_defined SourceMainBudgetV1.Cell0169.execution SourceMainBudgetV1.Cell0169.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=170) (input:=SourceMainFramesV1.Point0170.input) (pair:=SourceMainFramesV1.Point0170.outputs) SourceHeightEdgesV1.Edge0170.left_defined SourceMainFramesV1.Point0170.input_defined SourceMainFramesV1.Point0170.outputs_defined SourceMainBudgetV1.Cell0170.execution SourceMainBudgetV1.Cell0170.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=171) (input:=SourceMainFramesV1.Point0171.input) (pair:=SourceMainFramesV1.Point0171.outputs) SourceHeightEdgesV1.Edge0171.left_defined SourceMainFramesV1.Point0171.input_defined SourceMainFramesV1.Point0171.outputs_defined SourceMainBudgetV1.Cell0171.execution SourceMainBudgetV1.Cell0171.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=172) (input:=SourceMainFramesV1.Point0172.input) (pair:=SourceMainFramesV1.Point0172.outputs) SourceHeightEdgesV1.Edge0172.left_defined SourceMainFramesV1.Point0172.input_defined SourceMainFramesV1.Point0172.outputs_defined SourceMainBudgetV1.Cell0172.execution SourceMainBudgetV1.Cell0172.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=173) (input:=SourceMainFramesV1.Point0173.input) (pair:=SourceMainFramesV1.Point0173.outputs) SourceHeightEdgesV1.Edge0173.left_defined SourceMainFramesV1.Point0173.input_defined SourceMainFramesV1.Point0173.outputs_defined SourceMainBudgetV1.Cell0173.execution SourceMainBudgetV1.Cell0173.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=174) (input:=SourceMainFramesV1.Point0174.input) (pair:=SourceMainFramesV1.Point0174.outputs) SourceHeightEdgesV1.Edge0174.left_defined SourceMainFramesV1.Point0174.input_defined SourceMainFramesV1.Point0174.outputs_defined SourceMainBudgetV1.Cell0174.execution SourceMainBudgetV1.Cell0174.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=175) (input:=SourceMainFramesV1.Point0175.input) (pair:=SourceMainFramesV1.Point0175.outputs) SourceHeightEdgesV1.Edge0175.left_defined SourceMainFramesV1.Point0175.input_defined SourceMainFramesV1.Point0175.outputs_defined SourceMainBudgetV1.Cell0175.execution SourceMainBudgetV1.Cell0175.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=176) (input:=SourceMainFramesV1.Point0176.input) (pair:=SourceMainFramesV1.Point0176.outputs) SourceHeightEdgesV1.Edge0176.left_defined SourceMainFramesV1.Point0176.input_defined SourceMainFramesV1.Point0176.outputs_defined SourceMainBudgetV1.Cell0176.execution SourceMainBudgetV1.Cell0176.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=177) (input:=SourceMainFramesV1.Point0177.input) (pair:=SourceMainFramesV1.Point0177.outputs) SourceHeightEdgesV1.Edge0177.left_defined SourceMainFramesV1.Point0177.input_defined SourceMainFramesV1.Point0177.outputs_defined SourceMainBudgetV1.Cell0177.execution SourceMainBudgetV1.Cell0177.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=178) (input:=SourceMainFramesV1.Point0178.input) (pair:=SourceMainFramesV1.Point0178.outputs) SourceHeightEdgesV1.Edge0178.left_defined SourceMainFramesV1.Point0178.input_defined SourceMainFramesV1.Point0178.outputs_defined SourceMainBudgetV1.Cell0178.execution SourceMainBudgetV1.Cell0178.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=179) (input:=SourceMainFramesV1.Point0179.input) (pair:=SourceMainFramesV1.Point0179.outputs) SourceHeightEdgesV1.Edge0179.left_defined SourceMainFramesV1.Point0179.input_defined SourceMainFramesV1.Point0179.outputs_defined SourceMainBudgetV1.Cell0179.execution SourceMainBudgetV1.Cell0179.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=180) (input:=SourceMainFramesV1.Point0180.input) (pair:=SourceMainFramesV1.Point0180.outputs) SourceHeightEdgesV1.Edge0180.left_defined SourceMainFramesV1.Point0180.input_defined SourceMainFramesV1.Point0180.outputs_defined SourceMainBudgetV1.Cell0180.execution SourceMainBudgetV1.Cell0180.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=181) (input:=SourceMainFramesV1.Point0181.input) (pair:=SourceMainFramesV1.Point0181.outputs) SourceHeightEdgesV1.Edge0181.left_defined SourceMainFramesV1.Point0181.input_defined SourceMainFramesV1.Point0181.outputs_defined SourceMainBudgetV1.Cell0181.execution SourceMainBudgetV1.Cell0181.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=182) (input:=SourceMainFramesV1.Point0182.input) (pair:=SourceMainFramesV1.Point0182.outputs) SourceHeightEdgesV1.Edge0182.left_defined SourceMainFramesV1.Point0182.input_defined SourceMainFramesV1.Point0182.outputs_defined SourceMainBudgetV1.Cell0182.execution SourceMainBudgetV1.Cell0182.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=183) (input:=SourceMainFramesV1.Point0183.input) (pair:=SourceMainFramesV1.Point0183.outputs) SourceHeightEdgesV1.Edge0183.left_defined SourceMainFramesV1.Point0183.input_defined SourceMainFramesV1.Point0183.outputs_defined SourceMainBudgetV1.Cell0183.execution SourceMainBudgetV1.Cell0183.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=184) (input:=SourceMainFramesV1.Point0184.input) (pair:=SourceMainFramesV1.Point0184.outputs) SourceHeightEdgesV1.Edge0184.left_defined SourceMainFramesV1.Point0184.input_defined SourceMainFramesV1.Point0184.outputs_defined SourceMainBudgetV1.Cell0184.execution SourceMainBudgetV1.Cell0184.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=185) (input:=SourceMainFramesV1.Point0185.input) (pair:=SourceMainFramesV1.Point0185.outputs) SourceHeightEdgesV1.Edge0185.left_defined SourceMainFramesV1.Point0185.input_defined SourceMainFramesV1.Point0185.outputs_defined SourceMainBudgetV1.Cell0185.execution SourceMainBudgetV1.Cell0185.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=186) (input:=SourceMainFramesV1.Point0186.input) (pair:=SourceMainFramesV1.Point0186.outputs) SourceHeightEdgesV1.Edge0186.left_defined SourceMainFramesV1.Point0186.input_defined SourceMainFramesV1.Point0186.outputs_defined SourceMainBudgetV1.Cell0186.execution SourceMainBudgetV1.Cell0186.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=187) (input:=SourceMainFramesV1.Point0187.input) (pair:=SourceMainFramesV1.Point0187.outputs) SourceHeightEdgesV1.Edge0187.left_defined SourceMainFramesV1.Point0187.input_defined SourceMainFramesV1.Point0187.outputs_defined SourceMainBudgetV1.Cell0187.execution SourceMainBudgetV1.Cell0187.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=188) (input:=SourceMainFramesV1.Point0188.input) (pair:=SourceMainFramesV1.Point0188.outputs) SourceHeightEdgesV1.Edge0188.left_defined SourceMainFramesV1.Point0188.input_defined SourceMainFramesV1.Point0188.outputs_defined SourceMainBudgetV1.Cell0188.execution SourceMainBudgetV1.Cell0188.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=189) (input:=SourceMainFramesV1.Point0189.input) (pair:=SourceMainFramesV1.Point0189.outputs) SourceHeightEdgesV1.Edge0189.left_defined SourceMainFramesV1.Point0189.input_defined SourceMainFramesV1.Point0189.outputs_defined SourceMainBudgetV1.Cell0189.execution SourceMainBudgetV1.Cell0189.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=190) (input:=SourceMainFramesV1.Point0190.input) (pair:=SourceMainFramesV1.Point0190.outputs) SourceHeightEdgesV1.Edge0190.left_defined SourceMainFramesV1.Point0190.input_defined SourceMainFramesV1.Point0190.outputs_defined SourceMainBudgetV1.Cell0190.execution SourceMainBudgetV1.Cell0190.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=191) (input:=SourceMainFramesV1.Point0191.input) (pair:=SourceMainFramesV1.Point0191.outputs) SourceHeightEdgesV1.Edge0191.left_defined SourceMainFramesV1.Point0191.input_defined SourceMainFramesV1.Point0191.outputs_defined SourceMainBudgetV1.Cell0191.execution SourceMainBudgetV1.Cell0191.next_total
end SourceMainBudgetV1.Block05
open Lean Elab
run_elab do
 let n := `SourceMainBudgetV1.Block05.all
 let env ← getEnv
 let some ci := env.find? n | throwError "missing actual source cell block"
 let ax ← Lean.collectAxioms n
 logInfo m!"BUDGET_BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
