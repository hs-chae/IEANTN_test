import SourceMainBudgetV1.Cell0064
import SourceHeightEdgesV1.Edge0064
import SourceMainBudgetV1.Cell0065
import SourceHeightEdgesV1.Edge0065
import SourceMainBudgetV1.Cell0066
import SourceHeightEdgesV1.Edge0066
import SourceMainBudgetV1.Cell0067
import SourceHeightEdgesV1.Edge0067
import SourceMainBudgetV1.Cell0068
import SourceHeightEdgesV1.Edge0068
import SourceMainBudgetV1.Cell0069
import SourceHeightEdgesV1.Edge0069
import SourceMainBudgetV1.Cell0070
import SourceHeightEdgesV1.Edge0070
import SourceMainBudgetV1.Cell0071
import SourceHeightEdgesV1.Edge0071
import SourceMainBudgetV1.Cell0072
import SourceHeightEdgesV1.Edge0072
import SourceMainBudgetV1.Cell0073
import SourceHeightEdgesV1.Edge0073
import SourceMainBudgetV1.Cell0074
import SourceHeightEdgesV1.Edge0074
import SourceMainBudgetV1.Cell0075
import SourceHeightEdgesV1.Edge0075
import SourceMainBudgetV1.Cell0076
import SourceHeightEdgesV1.Edge0076
import SourceMainBudgetV1.Cell0077
import SourceHeightEdgesV1.Edge0077
import SourceMainBudgetV1.Cell0078
import SourceHeightEdgesV1.Edge0078
import SourceMainBudgetV1.Cell0079
import SourceHeightEdgesV1.Edge0079
import SourceMainBudgetV1.Cell0080
import SourceHeightEdgesV1.Edge0080
import SourceMainBudgetV1.Cell0081
import SourceHeightEdgesV1.Edge0081
import SourceMainBudgetV1.Cell0082
import SourceHeightEdgesV1.Edge0082
import SourceMainBudgetV1.Cell0083
import SourceHeightEdgesV1.Edge0083
import SourceMainBudgetV1.Cell0084
import SourceHeightEdgesV1.Edge0084
import SourceMainBudgetV1.Cell0085
import SourceHeightEdgesV1.Edge0085
import SourceMainBudgetV1.Cell0086
import SourceHeightEdgesV1.Edge0086
import SourceMainBudgetV1.Cell0087
import SourceHeightEdgesV1.Edge0087
import SourceMainBudgetV1.Cell0088
import SourceHeightEdgesV1.Edge0088
import SourceMainBudgetV1.Cell0089
import SourceHeightEdgesV1.Edge0089
import SourceMainBudgetV1.Cell0090
import SourceHeightEdgesV1.Edge0090
import SourceMainBudgetV1.Cell0091
import SourceHeightEdgesV1.Edge0091
import SourceMainBudgetV1.Cell0092
import SourceHeightEdgesV1.Edge0092
import SourceMainBudgetV1.Cell0093
import SourceHeightEdgesV1.Edge0093
import SourceMainBudgetV1.Cell0094
import SourceHeightEdgesV1.Edge0094
import SourceMainBudgetV1.Cell0095
import SourceHeightEdgesV1.Edge0095
import SourceMainBudgetV1.Data
import Mathlib.Tactic.IntervalCases
namespace SourceMainBudgetV1.Block02
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem all (i : Nat) (lower : 64 ≤ i) (upper : i < 96) :
 SourceMainBudgetV1.Data.Cell i := by
 interval_cases i
 · exact SourceMainBudgetV1.Data.pack (i:=64) (input:=SourceMainFramesV1.Point0064.input) (pair:=SourceMainFramesV1.Point0064.outputs) SourceHeightEdgesV1.Edge0064.left_defined SourceMainFramesV1.Point0064.input_defined SourceMainFramesV1.Point0064.outputs_defined SourceMainBudgetV1.Cell0064.execution SourceMainBudgetV1.Cell0064.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=65) (input:=SourceMainFramesV1.Point0065.input) (pair:=SourceMainFramesV1.Point0065.outputs) SourceHeightEdgesV1.Edge0065.left_defined SourceMainFramesV1.Point0065.input_defined SourceMainFramesV1.Point0065.outputs_defined SourceMainBudgetV1.Cell0065.execution SourceMainBudgetV1.Cell0065.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=66) (input:=SourceMainFramesV1.Point0066.input) (pair:=SourceMainFramesV1.Point0066.outputs) SourceHeightEdgesV1.Edge0066.left_defined SourceMainFramesV1.Point0066.input_defined SourceMainFramesV1.Point0066.outputs_defined SourceMainBudgetV1.Cell0066.execution SourceMainBudgetV1.Cell0066.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=67) (input:=SourceMainFramesV1.Point0067.input) (pair:=SourceMainFramesV1.Point0067.outputs) SourceHeightEdgesV1.Edge0067.left_defined SourceMainFramesV1.Point0067.input_defined SourceMainFramesV1.Point0067.outputs_defined SourceMainBudgetV1.Cell0067.execution SourceMainBudgetV1.Cell0067.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=68) (input:=SourceMainFramesV1.Point0068.input) (pair:=SourceMainFramesV1.Point0068.outputs) SourceHeightEdgesV1.Edge0068.left_defined SourceMainFramesV1.Point0068.input_defined SourceMainFramesV1.Point0068.outputs_defined SourceMainBudgetV1.Cell0068.execution SourceMainBudgetV1.Cell0068.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=69) (input:=SourceMainFramesV1.Point0069.input) (pair:=SourceMainFramesV1.Point0069.outputs) SourceHeightEdgesV1.Edge0069.left_defined SourceMainFramesV1.Point0069.input_defined SourceMainFramesV1.Point0069.outputs_defined SourceMainBudgetV1.Cell0069.execution SourceMainBudgetV1.Cell0069.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=70) (input:=SourceMainFramesV1.Point0070.input) (pair:=SourceMainFramesV1.Point0070.outputs) SourceHeightEdgesV1.Edge0070.left_defined SourceMainFramesV1.Point0070.input_defined SourceMainFramesV1.Point0070.outputs_defined SourceMainBudgetV1.Cell0070.execution SourceMainBudgetV1.Cell0070.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=71) (input:=SourceMainFramesV1.Point0071.input) (pair:=SourceMainFramesV1.Point0071.outputs) SourceHeightEdgesV1.Edge0071.left_defined SourceMainFramesV1.Point0071.input_defined SourceMainFramesV1.Point0071.outputs_defined SourceMainBudgetV1.Cell0071.execution SourceMainBudgetV1.Cell0071.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=72) (input:=SourceMainFramesV1.Point0072.input) (pair:=SourceMainFramesV1.Point0072.outputs) SourceHeightEdgesV1.Edge0072.left_defined SourceMainFramesV1.Point0072.input_defined SourceMainFramesV1.Point0072.outputs_defined SourceMainBudgetV1.Cell0072.execution SourceMainBudgetV1.Cell0072.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=73) (input:=SourceMainFramesV1.Point0073.input) (pair:=SourceMainFramesV1.Point0073.outputs) SourceHeightEdgesV1.Edge0073.left_defined SourceMainFramesV1.Point0073.input_defined SourceMainFramesV1.Point0073.outputs_defined SourceMainBudgetV1.Cell0073.execution SourceMainBudgetV1.Cell0073.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=74) (input:=SourceMainFramesV1.Point0074.input) (pair:=SourceMainFramesV1.Point0074.outputs) SourceHeightEdgesV1.Edge0074.left_defined SourceMainFramesV1.Point0074.input_defined SourceMainFramesV1.Point0074.outputs_defined SourceMainBudgetV1.Cell0074.execution SourceMainBudgetV1.Cell0074.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=75) (input:=SourceMainFramesV1.Point0075.input) (pair:=SourceMainFramesV1.Point0075.outputs) SourceHeightEdgesV1.Edge0075.left_defined SourceMainFramesV1.Point0075.input_defined SourceMainFramesV1.Point0075.outputs_defined SourceMainBudgetV1.Cell0075.execution SourceMainBudgetV1.Cell0075.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=76) (input:=SourceMainFramesV1.Point0076.input) (pair:=SourceMainFramesV1.Point0076.outputs) SourceHeightEdgesV1.Edge0076.left_defined SourceMainFramesV1.Point0076.input_defined SourceMainFramesV1.Point0076.outputs_defined SourceMainBudgetV1.Cell0076.execution SourceMainBudgetV1.Cell0076.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=77) (input:=SourceMainFramesV1.Point0077.input) (pair:=SourceMainFramesV1.Point0077.outputs) SourceHeightEdgesV1.Edge0077.left_defined SourceMainFramesV1.Point0077.input_defined SourceMainFramesV1.Point0077.outputs_defined SourceMainBudgetV1.Cell0077.execution SourceMainBudgetV1.Cell0077.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=78) (input:=SourceMainFramesV1.Point0078.input) (pair:=SourceMainFramesV1.Point0078.outputs) SourceHeightEdgesV1.Edge0078.left_defined SourceMainFramesV1.Point0078.input_defined SourceMainFramesV1.Point0078.outputs_defined SourceMainBudgetV1.Cell0078.execution SourceMainBudgetV1.Cell0078.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=79) (input:=SourceMainFramesV1.Point0079.input) (pair:=SourceMainFramesV1.Point0079.outputs) SourceHeightEdgesV1.Edge0079.left_defined SourceMainFramesV1.Point0079.input_defined SourceMainFramesV1.Point0079.outputs_defined SourceMainBudgetV1.Cell0079.execution SourceMainBudgetV1.Cell0079.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=80) (input:=SourceMainFramesV1.Point0080.input) (pair:=SourceMainFramesV1.Point0080.outputs) SourceHeightEdgesV1.Edge0080.left_defined SourceMainFramesV1.Point0080.input_defined SourceMainFramesV1.Point0080.outputs_defined SourceMainBudgetV1.Cell0080.execution SourceMainBudgetV1.Cell0080.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=81) (input:=SourceMainFramesV1.Point0081.input) (pair:=SourceMainFramesV1.Point0081.outputs) SourceHeightEdgesV1.Edge0081.left_defined SourceMainFramesV1.Point0081.input_defined SourceMainFramesV1.Point0081.outputs_defined SourceMainBudgetV1.Cell0081.execution SourceMainBudgetV1.Cell0081.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=82) (input:=SourceMainFramesV1.Point0082.input) (pair:=SourceMainFramesV1.Point0082.outputs) SourceHeightEdgesV1.Edge0082.left_defined SourceMainFramesV1.Point0082.input_defined SourceMainFramesV1.Point0082.outputs_defined SourceMainBudgetV1.Cell0082.execution SourceMainBudgetV1.Cell0082.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=83) (input:=SourceMainFramesV1.Point0083.input) (pair:=SourceMainFramesV1.Point0083.outputs) SourceHeightEdgesV1.Edge0083.left_defined SourceMainFramesV1.Point0083.input_defined SourceMainFramesV1.Point0083.outputs_defined SourceMainBudgetV1.Cell0083.execution SourceMainBudgetV1.Cell0083.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=84) (input:=SourceMainFramesV1.Point0084.input) (pair:=SourceMainFramesV1.Point0084.outputs) SourceHeightEdgesV1.Edge0084.left_defined SourceMainFramesV1.Point0084.input_defined SourceMainFramesV1.Point0084.outputs_defined SourceMainBudgetV1.Cell0084.execution SourceMainBudgetV1.Cell0084.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=85) (input:=SourceMainFramesV1.Point0085.input) (pair:=SourceMainFramesV1.Point0085.outputs) SourceHeightEdgesV1.Edge0085.left_defined SourceMainFramesV1.Point0085.input_defined SourceMainFramesV1.Point0085.outputs_defined SourceMainBudgetV1.Cell0085.execution SourceMainBudgetV1.Cell0085.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=86) (input:=SourceMainFramesV1.Point0086.input) (pair:=SourceMainFramesV1.Point0086.outputs) SourceHeightEdgesV1.Edge0086.left_defined SourceMainFramesV1.Point0086.input_defined SourceMainFramesV1.Point0086.outputs_defined SourceMainBudgetV1.Cell0086.execution SourceMainBudgetV1.Cell0086.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=87) (input:=SourceMainFramesV1.Point0087.input) (pair:=SourceMainFramesV1.Point0087.outputs) SourceHeightEdgesV1.Edge0087.left_defined SourceMainFramesV1.Point0087.input_defined SourceMainFramesV1.Point0087.outputs_defined SourceMainBudgetV1.Cell0087.execution SourceMainBudgetV1.Cell0087.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=88) (input:=SourceMainFramesV1.Point0088.input) (pair:=SourceMainFramesV1.Point0088.outputs) SourceHeightEdgesV1.Edge0088.left_defined SourceMainFramesV1.Point0088.input_defined SourceMainFramesV1.Point0088.outputs_defined SourceMainBudgetV1.Cell0088.execution SourceMainBudgetV1.Cell0088.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=89) (input:=SourceMainFramesV1.Point0089.input) (pair:=SourceMainFramesV1.Point0089.outputs) SourceHeightEdgesV1.Edge0089.left_defined SourceMainFramesV1.Point0089.input_defined SourceMainFramesV1.Point0089.outputs_defined SourceMainBudgetV1.Cell0089.execution SourceMainBudgetV1.Cell0089.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=90) (input:=SourceMainFramesV1.Point0090.input) (pair:=SourceMainFramesV1.Point0090.outputs) SourceHeightEdgesV1.Edge0090.left_defined SourceMainFramesV1.Point0090.input_defined SourceMainFramesV1.Point0090.outputs_defined SourceMainBudgetV1.Cell0090.execution SourceMainBudgetV1.Cell0090.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=91) (input:=SourceMainFramesV1.Point0091.input) (pair:=SourceMainFramesV1.Point0091.outputs) SourceHeightEdgesV1.Edge0091.left_defined SourceMainFramesV1.Point0091.input_defined SourceMainFramesV1.Point0091.outputs_defined SourceMainBudgetV1.Cell0091.execution SourceMainBudgetV1.Cell0091.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=92) (input:=SourceMainFramesV1.Point0092.input) (pair:=SourceMainFramesV1.Point0092.outputs) SourceHeightEdgesV1.Edge0092.left_defined SourceMainFramesV1.Point0092.input_defined SourceMainFramesV1.Point0092.outputs_defined SourceMainBudgetV1.Cell0092.execution SourceMainBudgetV1.Cell0092.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=93) (input:=SourceMainFramesV1.Point0093.input) (pair:=SourceMainFramesV1.Point0093.outputs) SourceHeightEdgesV1.Edge0093.left_defined SourceMainFramesV1.Point0093.input_defined SourceMainFramesV1.Point0093.outputs_defined SourceMainBudgetV1.Cell0093.execution SourceMainBudgetV1.Cell0093.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=94) (input:=SourceMainFramesV1.Point0094.input) (pair:=SourceMainFramesV1.Point0094.outputs) SourceHeightEdgesV1.Edge0094.left_defined SourceMainFramesV1.Point0094.input_defined SourceMainFramesV1.Point0094.outputs_defined SourceMainBudgetV1.Cell0094.execution SourceMainBudgetV1.Cell0094.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=95) (input:=SourceMainFramesV1.Point0095.input) (pair:=SourceMainFramesV1.Point0095.outputs) SourceHeightEdgesV1.Edge0095.left_defined SourceMainFramesV1.Point0095.input_defined SourceMainFramesV1.Point0095.outputs_defined SourceMainBudgetV1.Cell0095.execution SourceMainBudgetV1.Cell0095.next_total
end SourceMainBudgetV1.Block02
open Lean Elab
run_elab do
 let n := `SourceMainBudgetV1.Block02.all
 let env ← getEnv
 let some ci := env.find? n | throwError "missing actual source cell block"
 let ax ← Lean.collectAxioms n
 logInfo m!"BUDGET_BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
