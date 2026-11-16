import SourceMainBudgetV1.Cell0096
import SourceHeightEdgesV1.Edge0096
import SourceMainBudgetV1.Cell0097
import SourceHeightEdgesV1.Edge0097
import SourceMainBudgetV1.Cell0098
import SourceHeightEdgesV1.Edge0098
import SourceMainBudgetV1.Cell0099
import SourceHeightEdgesV1.Edge0099
import SourceMainBudgetV1.Cell0100
import SourceHeightEdgesV1.Edge0100
import SourceMainBudgetV1.Cell0101
import SourceHeightEdgesV1.Edge0101
import SourceMainBudgetV1.Cell0102
import SourceHeightEdgesV1.Edge0102
import SourceMainBudgetV1.Cell0103
import SourceHeightEdgesV1.Edge0103
import SourceMainBudgetV1.Cell0104
import SourceHeightEdgesV1.Edge0104
import SourceMainBudgetV1.Cell0105
import SourceHeightEdgesV1.Edge0105
import SourceMainBudgetV1.Cell0106
import SourceHeightEdgesV1.Edge0106
import SourceMainBudgetV1.Cell0107
import SourceHeightEdgesV1.Edge0107
import SourceMainBudgetV1.Cell0108
import SourceHeightEdgesV1.Edge0108
import SourceMainBudgetV1.Cell0109
import SourceHeightEdgesV1.Edge0109
import SourceMainBudgetV1.Cell0110
import SourceHeightEdgesV1.Edge0110
import SourceMainBudgetV1.Cell0111
import SourceHeightEdgesV1.Edge0111
import SourceMainBudgetV1.Cell0112
import SourceHeightEdgesV1.Edge0112
import SourceMainBudgetV1.Cell0113
import SourceHeightEdgesV1.Edge0113
import SourceMainBudgetV1.Cell0114
import SourceHeightEdgesV1.Edge0114
import SourceMainBudgetV1.Cell0115
import SourceHeightEdgesV1.Edge0115
import SourceMainBudgetV1.Cell0116
import SourceHeightEdgesV1.Edge0116
import SourceMainBudgetV1.Cell0117
import SourceHeightEdgesV1.Edge0117
import SourceMainBudgetV1.Cell0118
import SourceHeightEdgesV1.Edge0118
import SourceMainBudgetV1.Cell0119
import SourceHeightEdgesV1.Edge0119
import SourceMainBudgetV1.Cell0120
import SourceHeightEdgesV1.Edge0120
import SourceMainBudgetV1.Cell0121
import SourceHeightEdgesV1.Edge0121
import SourceMainBudgetV1.Cell0122
import SourceHeightEdgesV1.Edge0122
import SourceMainBudgetV1.Cell0123
import SourceHeightEdgesV1.Edge0123
import SourceMainBudgetV1.Cell0124
import SourceHeightEdgesV1.Edge0124
import SourceMainBudgetV1.Cell0125
import SourceHeightEdgesV1.Edge0125
import SourceMainBudgetV1.Cell0126
import SourceHeightEdgesV1.Edge0126
import SourceMainBudgetV1.Cell0127
import SourceHeightEdgesV1.Edge0127
import SourceMainBudgetV1.Data
import Mathlib.Tactic.IntervalCases
namespace SourceMainBudgetV1.Block03
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem all (i : Nat) (lower : 96 ≤ i) (upper : i < 128) :
 SourceMainBudgetV1.Data.Cell i := by
 interval_cases i
 · exact SourceMainBudgetV1.Data.pack (i:=96) (input:=SourceMainFramesV1.Point0096.input) (pair:=SourceMainFramesV1.Point0096.outputs) SourceHeightEdgesV1.Edge0096.left_defined SourceMainFramesV1.Point0096.input_defined SourceMainFramesV1.Point0096.outputs_defined SourceMainBudgetV1.Cell0096.execution SourceMainBudgetV1.Cell0096.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=97) (input:=SourceMainFramesV1.Point0097.input) (pair:=SourceMainFramesV1.Point0097.outputs) SourceHeightEdgesV1.Edge0097.left_defined SourceMainFramesV1.Point0097.input_defined SourceMainFramesV1.Point0097.outputs_defined SourceMainBudgetV1.Cell0097.execution SourceMainBudgetV1.Cell0097.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=98) (input:=SourceMainFramesV1.Point0098.input) (pair:=SourceMainFramesV1.Point0098.outputs) SourceHeightEdgesV1.Edge0098.left_defined SourceMainFramesV1.Point0098.input_defined SourceMainFramesV1.Point0098.outputs_defined SourceMainBudgetV1.Cell0098.execution SourceMainBudgetV1.Cell0098.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=99) (input:=SourceMainFramesV1.Point0099.input) (pair:=SourceMainFramesV1.Point0099.outputs) SourceHeightEdgesV1.Edge0099.left_defined SourceMainFramesV1.Point0099.input_defined SourceMainFramesV1.Point0099.outputs_defined SourceMainBudgetV1.Cell0099.execution SourceMainBudgetV1.Cell0099.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=100) (input:=SourceMainFramesV1.Point0100.input) (pair:=SourceMainFramesV1.Point0100.outputs) SourceHeightEdgesV1.Edge0100.left_defined SourceMainFramesV1.Point0100.input_defined SourceMainFramesV1.Point0100.outputs_defined SourceMainBudgetV1.Cell0100.execution SourceMainBudgetV1.Cell0100.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=101) (input:=SourceMainFramesV1.Point0101.input) (pair:=SourceMainFramesV1.Point0101.outputs) SourceHeightEdgesV1.Edge0101.left_defined SourceMainFramesV1.Point0101.input_defined SourceMainFramesV1.Point0101.outputs_defined SourceMainBudgetV1.Cell0101.execution SourceMainBudgetV1.Cell0101.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=102) (input:=SourceMainFramesV1.Point0102.input) (pair:=SourceMainFramesV1.Point0102.outputs) SourceHeightEdgesV1.Edge0102.left_defined SourceMainFramesV1.Point0102.input_defined SourceMainFramesV1.Point0102.outputs_defined SourceMainBudgetV1.Cell0102.execution SourceMainBudgetV1.Cell0102.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=103) (input:=SourceMainFramesV1.Point0103.input) (pair:=SourceMainFramesV1.Point0103.outputs) SourceHeightEdgesV1.Edge0103.left_defined SourceMainFramesV1.Point0103.input_defined SourceMainFramesV1.Point0103.outputs_defined SourceMainBudgetV1.Cell0103.execution SourceMainBudgetV1.Cell0103.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=104) (input:=SourceMainFramesV1.Point0104.input) (pair:=SourceMainFramesV1.Point0104.outputs) SourceHeightEdgesV1.Edge0104.left_defined SourceMainFramesV1.Point0104.input_defined SourceMainFramesV1.Point0104.outputs_defined SourceMainBudgetV1.Cell0104.execution SourceMainBudgetV1.Cell0104.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=105) (input:=SourceMainFramesV1.Point0105.input) (pair:=SourceMainFramesV1.Point0105.outputs) SourceHeightEdgesV1.Edge0105.left_defined SourceMainFramesV1.Point0105.input_defined SourceMainFramesV1.Point0105.outputs_defined SourceMainBudgetV1.Cell0105.execution SourceMainBudgetV1.Cell0105.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=106) (input:=SourceMainFramesV1.Point0106.input) (pair:=SourceMainFramesV1.Point0106.outputs) SourceHeightEdgesV1.Edge0106.left_defined SourceMainFramesV1.Point0106.input_defined SourceMainFramesV1.Point0106.outputs_defined SourceMainBudgetV1.Cell0106.execution SourceMainBudgetV1.Cell0106.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=107) (input:=SourceMainFramesV1.Point0107.input) (pair:=SourceMainFramesV1.Point0107.outputs) SourceHeightEdgesV1.Edge0107.left_defined SourceMainFramesV1.Point0107.input_defined SourceMainFramesV1.Point0107.outputs_defined SourceMainBudgetV1.Cell0107.execution SourceMainBudgetV1.Cell0107.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=108) (input:=SourceMainFramesV1.Point0108.input) (pair:=SourceMainFramesV1.Point0108.outputs) SourceHeightEdgesV1.Edge0108.left_defined SourceMainFramesV1.Point0108.input_defined SourceMainFramesV1.Point0108.outputs_defined SourceMainBudgetV1.Cell0108.execution SourceMainBudgetV1.Cell0108.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=109) (input:=SourceMainFramesV1.Point0109.input) (pair:=SourceMainFramesV1.Point0109.outputs) SourceHeightEdgesV1.Edge0109.left_defined SourceMainFramesV1.Point0109.input_defined SourceMainFramesV1.Point0109.outputs_defined SourceMainBudgetV1.Cell0109.execution SourceMainBudgetV1.Cell0109.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=110) (input:=SourceMainFramesV1.Point0110.input) (pair:=SourceMainFramesV1.Point0110.outputs) SourceHeightEdgesV1.Edge0110.left_defined SourceMainFramesV1.Point0110.input_defined SourceMainFramesV1.Point0110.outputs_defined SourceMainBudgetV1.Cell0110.execution SourceMainBudgetV1.Cell0110.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=111) (input:=SourceMainFramesV1.Point0111.input) (pair:=SourceMainFramesV1.Point0111.outputs) SourceHeightEdgesV1.Edge0111.left_defined SourceMainFramesV1.Point0111.input_defined SourceMainFramesV1.Point0111.outputs_defined SourceMainBudgetV1.Cell0111.execution SourceMainBudgetV1.Cell0111.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=112) (input:=SourceMainFramesV1.Point0112.input) (pair:=SourceMainFramesV1.Point0112.outputs) SourceHeightEdgesV1.Edge0112.left_defined SourceMainFramesV1.Point0112.input_defined SourceMainFramesV1.Point0112.outputs_defined SourceMainBudgetV1.Cell0112.execution SourceMainBudgetV1.Cell0112.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=113) (input:=SourceMainFramesV1.Point0113.input) (pair:=SourceMainFramesV1.Point0113.outputs) SourceHeightEdgesV1.Edge0113.left_defined SourceMainFramesV1.Point0113.input_defined SourceMainFramesV1.Point0113.outputs_defined SourceMainBudgetV1.Cell0113.execution SourceMainBudgetV1.Cell0113.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=114) (input:=SourceMainFramesV1.Point0114.input) (pair:=SourceMainFramesV1.Point0114.outputs) SourceHeightEdgesV1.Edge0114.left_defined SourceMainFramesV1.Point0114.input_defined SourceMainFramesV1.Point0114.outputs_defined SourceMainBudgetV1.Cell0114.execution SourceMainBudgetV1.Cell0114.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=115) (input:=SourceMainFramesV1.Point0115.input) (pair:=SourceMainFramesV1.Point0115.outputs) SourceHeightEdgesV1.Edge0115.left_defined SourceMainFramesV1.Point0115.input_defined SourceMainFramesV1.Point0115.outputs_defined SourceMainBudgetV1.Cell0115.execution SourceMainBudgetV1.Cell0115.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=116) (input:=SourceMainFramesV1.Point0116.input) (pair:=SourceMainFramesV1.Point0116.outputs) SourceHeightEdgesV1.Edge0116.left_defined SourceMainFramesV1.Point0116.input_defined SourceMainFramesV1.Point0116.outputs_defined SourceMainBudgetV1.Cell0116.execution SourceMainBudgetV1.Cell0116.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=117) (input:=SourceMainFramesV1.Point0117.input) (pair:=SourceMainFramesV1.Point0117.outputs) SourceHeightEdgesV1.Edge0117.left_defined SourceMainFramesV1.Point0117.input_defined SourceMainFramesV1.Point0117.outputs_defined SourceMainBudgetV1.Cell0117.execution SourceMainBudgetV1.Cell0117.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=118) (input:=SourceMainFramesV1.Point0118.input) (pair:=SourceMainFramesV1.Point0118.outputs) SourceHeightEdgesV1.Edge0118.left_defined SourceMainFramesV1.Point0118.input_defined SourceMainFramesV1.Point0118.outputs_defined SourceMainBudgetV1.Cell0118.execution SourceMainBudgetV1.Cell0118.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=119) (input:=SourceMainFramesV1.Point0119.input) (pair:=SourceMainFramesV1.Point0119.outputs) SourceHeightEdgesV1.Edge0119.left_defined SourceMainFramesV1.Point0119.input_defined SourceMainFramesV1.Point0119.outputs_defined SourceMainBudgetV1.Cell0119.execution SourceMainBudgetV1.Cell0119.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=120) (input:=SourceMainFramesV1.Point0120.input) (pair:=SourceMainFramesV1.Point0120.outputs) SourceHeightEdgesV1.Edge0120.left_defined SourceMainFramesV1.Point0120.input_defined SourceMainFramesV1.Point0120.outputs_defined SourceMainBudgetV1.Cell0120.execution SourceMainBudgetV1.Cell0120.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=121) (input:=SourceMainFramesV1.Point0121.input) (pair:=SourceMainFramesV1.Point0121.outputs) SourceHeightEdgesV1.Edge0121.left_defined SourceMainFramesV1.Point0121.input_defined SourceMainFramesV1.Point0121.outputs_defined SourceMainBudgetV1.Cell0121.execution SourceMainBudgetV1.Cell0121.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=122) (input:=SourceMainFramesV1.Point0122.input) (pair:=SourceMainFramesV1.Point0122.outputs) SourceHeightEdgesV1.Edge0122.left_defined SourceMainFramesV1.Point0122.input_defined SourceMainFramesV1.Point0122.outputs_defined SourceMainBudgetV1.Cell0122.execution SourceMainBudgetV1.Cell0122.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=123) (input:=SourceMainFramesV1.Point0123.input) (pair:=SourceMainFramesV1.Point0123.outputs) SourceHeightEdgesV1.Edge0123.left_defined SourceMainFramesV1.Point0123.input_defined SourceMainFramesV1.Point0123.outputs_defined SourceMainBudgetV1.Cell0123.execution SourceMainBudgetV1.Cell0123.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=124) (input:=SourceMainFramesV1.Point0124.input) (pair:=SourceMainFramesV1.Point0124.outputs) SourceHeightEdgesV1.Edge0124.left_defined SourceMainFramesV1.Point0124.input_defined SourceMainFramesV1.Point0124.outputs_defined SourceMainBudgetV1.Cell0124.execution SourceMainBudgetV1.Cell0124.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=125) (input:=SourceMainFramesV1.Point0125.input) (pair:=SourceMainFramesV1.Point0125.outputs) SourceHeightEdgesV1.Edge0125.left_defined SourceMainFramesV1.Point0125.input_defined SourceMainFramesV1.Point0125.outputs_defined SourceMainBudgetV1.Cell0125.execution SourceMainBudgetV1.Cell0125.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=126) (input:=SourceMainFramesV1.Point0126.input) (pair:=SourceMainFramesV1.Point0126.outputs) SourceHeightEdgesV1.Edge0126.left_defined SourceMainFramesV1.Point0126.input_defined SourceMainFramesV1.Point0126.outputs_defined SourceMainBudgetV1.Cell0126.execution SourceMainBudgetV1.Cell0126.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=127) (input:=SourceMainFramesV1.Point0127.input) (pair:=SourceMainFramesV1.Point0127.outputs) SourceHeightEdgesV1.Edge0127.left_defined SourceMainFramesV1.Point0127.input_defined SourceMainFramesV1.Point0127.outputs_defined SourceMainBudgetV1.Cell0127.execution SourceMainBudgetV1.Cell0127.next_total
end SourceMainBudgetV1.Block03
open Lean Elab
run_elab do
 let n := `SourceMainBudgetV1.Block03.all
 let env ← getEnv
 let some ci := env.find? n | throwError "missing actual source cell block"
 let ax ← Lean.collectAxioms n
 logInfo m!"BUDGET_BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
