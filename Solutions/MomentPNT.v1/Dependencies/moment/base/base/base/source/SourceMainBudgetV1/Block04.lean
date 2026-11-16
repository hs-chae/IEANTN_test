import SourceMainBudgetV1.Cell0128
import SourceHeightEdgesV1.Edge0128
import SourceMainBudgetV1.Cell0129
import SourceHeightEdgesV1.Edge0129
import SourceMainBudgetV1.Cell0130
import SourceHeightEdgesV1.Edge0130
import SourceMainBudgetV1.Cell0131
import SourceHeightEdgesV1.Edge0131
import SourceMainBudgetV1.Cell0132
import SourceHeightEdgesV1.Edge0132
import SourceMainBudgetV1.Cell0133
import SourceHeightEdgesV1.Edge0133
import SourceMainBudgetV1.Cell0134
import SourceHeightEdgesV1.Edge0134
import SourceMainBudgetV1.Cell0135
import SourceHeightEdgesV1.Edge0135
import SourceMainBudgetV1.Cell0136
import SourceHeightEdgesV1.Edge0136
import SourceMainBudgetV1.Cell0137
import SourceHeightEdgesV1.Edge0137
import SourceMainBudgetV1.Cell0138
import SourceHeightEdgesV1.Edge0138
import SourceMainBudgetV1.Cell0139
import SourceHeightEdgesV1.Edge0139
import SourceMainBudgetV1.Cell0140
import SourceHeightEdgesV1.Edge0140
import SourceMainBudgetV1.Cell0141
import SourceHeightEdgesV1.Edge0141
import SourceMainBudgetV1.Cell0142
import SourceHeightEdgesV1.Edge0142
import SourceMainBudgetV1.Cell0143
import SourceHeightEdgesV1.Edge0143
import SourceMainBudgetV1.Cell0144
import SourceHeightEdgesV1.Edge0144
import SourceMainBudgetV1.Cell0145
import SourceHeightEdgesV1.Edge0145
import SourceMainBudgetV1.Cell0146
import SourceHeightEdgesV1.Edge0146
import SourceMainBudgetV1.Cell0147
import SourceHeightEdgesV1.Edge0147
import SourceMainBudgetV1.Cell0148
import SourceHeightEdgesV1.Edge0148
import SourceMainBudgetV1.Cell0149
import SourceHeightEdgesV1.Edge0149
import SourceMainBudgetV1.Cell0150
import SourceHeightEdgesV1.Edge0150
import SourceMainBudgetV1.Cell0151
import SourceHeightEdgesV1.Edge0151
import SourceMainBudgetV1.Cell0152
import SourceHeightEdgesV1.Edge0152
import SourceMainBudgetV1.Cell0153
import SourceHeightEdgesV1.Edge0153
import SourceMainBudgetV1.Cell0154
import SourceHeightEdgesV1.Edge0154
import SourceMainBudgetV1.Cell0155
import SourceHeightEdgesV1.Edge0155
import SourceMainBudgetV1.Cell0156
import SourceHeightEdgesV1.Edge0156
import SourceMainBudgetV1.Cell0157
import SourceHeightEdgesV1.Edge0157
import SourceMainBudgetV1.Cell0158
import SourceHeightEdgesV1.Edge0158
import SourceMainBudgetV1.Cell0159
import SourceHeightEdgesV1.Edge0159
import SourceMainBudgetV1.Data
import Mathlib.Tactic.IntervalCases
namespace SourceMainBudgetV1.Block04
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem all (i : Nat) (lower : 128 ≤ i) (upper : i < 160) :
 SourceMainBudgetV1.Data.Cell i := by
 interval_cases i
 · exact SourceMainBudgetV1.Data.pack (i:=128) (input:=SourceMainFramesV1.Point0128.input) (pair:=SourceMainFramesV1.Point0128.outputs) SourceHeightEdgesV1.Edge0128.left_defined SourceMainFramesV1.Point0128.input_defined SourceMainFramesV1.Point0128.outputs_defined SourceMainBudgetV1.Cell0128.execution SourceMainBudgetV1.Cell0128.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=129) (input:=SourceMainFramesV1.Point0129.input) (pair:=SourceMainFramesV1.Point0129.outputs) SourceHeightEdgesV1.Edge0129.left_defined SourceMainFramesV1.Point0129.input_defined SourceMainFramesV1.Point0129.outputs_defined SourceMainBudgetV1.Cell0129.execution SourceMainBudgetV1.Cell0129.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=130) (input:=SourceMainFramesV1.Point0130.input) (pair:=SourceMainFramesV1.Point0130.outputs) SourceHeightEdgesV1.Edge0130.left_defined SourceMainFramesV1.Point0130.input_defined SourceMainFramesV1.Point0130.outputs_defined SourceMainBudgetV1.Cell0130.execution SourceMainBudgetV1.Cell0130.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=131) (input:=SourceMainFramesV1.Point0131.input) (pair:=SourceMainFramesV1.Point0131.outputs) SourceHeightEdgesV1.Edge0131.left_defined SourceMainFramesV1.Point0131.input_defined SourceMainFramesV1.Point0131.outputs_defined SourceMainBudgetV1.Cell0131.execution SourceMainBudgetV1.Cell0131.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=132) (input:=SourceMainFramesV1.Point0132.input) (pair:=SourceMainFramesV1.Point0132.outputs) SourceHeightEdgesV1.Edge0132.left_defined SourceMainFramesV1.Point0132.input_defined SourceMainFramesV1.Point0132.outputs_defined SourceMainBudgetV1.Cell0132.execution SourceMainBudgetV1.Cell0132.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=133) (input:=SourceMainFramesV1.Point0133.input) (pair:=SourceMainFramesV1.Point0133.outputs) SourceHeightEdgesV1.Edge0133.left_defined SourceMainFramesV1.Point0133.input_defined SourceMainFramesV1.Point0133.outputs_defined SourceMainBudgetV1.Cell0133.execution SourceMainBudgetV1.Cell0133.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=134) (input:=SourceMainFramesV1.Point0134.input) (pair:=SourceMainFramesV1.Point0134.outputs) SourceHeightEdgesV1.Edge0134.left_defined SourceMainFramesV1.Point0134.input_defined SourceMainFramesV1.Point0134.outputs_defined SourceMainBudgetV1.Cell0134.execution SourceMainBudgetV1.Cell0134.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=135) (input:=SourceMainFramesV1.Point0135.input) (pair:=SourceMainFramesV1.Point0135.outputs) SourceHeightEdgesV1.Edge0135.left_defined SourceMainFramesV1.Point0135.input_defined SourceMainFramesV1.Point0135.outputs_defined SourceMainBudgetV1.Cell0135.execution SourceMainBudgetV1.Cell0135.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=136) (input:=SourceMainFramesV1.Point0136.input) (pair:=SourceMainFramesV1.Point0136.outputs) SourceHeightEdgesV1.Edge0136.left_defined SourceMainFramesV1.Point0136.input_defined SourceMainFramesV1.Point0136.outputs_defined SourceMainBudgetV1.Cell0136.execution SourceMainBudgetV1.Cell0136.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=137) (input:=SourceMainFramesV1.Point0137.input) (pair:=SourceMainFramesV1.Point0137.outputs) SourceHeightEdgesV1.Edge0137.left_defined SourceMainFramesV1.Point0137.input_defined SourceMainFramesV1.Point0137.outputs_defined SourceMainBudgetV1.Cell0137.execution SourceMainBudgetV1.Cell0137.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=138) (input:=SourceMainFramesV1.Point0138.input) (pair:=SourceMainFramesV1.Point0138.outputs) SourceHeightEdgesV1.Edge0138.left_defined SourceMainFramesV1.Point0138.input_defined SourceMainFramesV1.Point0138.outputs_defined SourceMainBudgetV1.Cell0138.execution SourceMainBudgetV1.Cell0138.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=139) (input:=SourceMainFramesV1.Point0139.input) (pair:=SourceMainFramesV1.Point0139.outputs) SourceHeightEdgesV1.Edge0139.left_defined SourceMainFramesV1.Point0139.input_defined SourceMainFramesV1.Point0139.outputs_defined SourceMainBudgetV1.Cell0139.execution SourceMainBudgetV1.Cell0139.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=140) (input:=SourceMainFramesV1.Point0140.input) (pair:=SourceMainFramesV1.Point0140.outputs) SourceHeightEdgesV1.Edge0140.left_defined SourceMainFramesV1.Point0140.input_defined SourceMainFramesV1.Point0140.outputs_defined SourceMainBudgetV1.Cell0140.execution SourceMainBudgetV1.Cell0140.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=141) (input:=SourceMainFramesV1.Point0141.input) (pair:=SourceMainFramesV1.Point0141.outputs) SourceHeightEdgesV1.Edge0141.left_defined SourceMainFramesV1.Point0141.input_defined SourceMainFramesV1.Point0141.outputs_defined SourceMainBudgetV1.Cell0141.execution SourceMainBudgetV1.Cell0141.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=142) (input:=SourceMainFramesV1.Point0142.input) (pair:=SourceMainFramesV1.Point0142.outputs) SourceHeightEdgesV1.Edge0142.left_defined SourceMainFramesV1.Point0142.input_defined SourceMainFramesV1.Point0142.outputs_defined SourceMainBudgetV1.Cell0142.execution SourceMainBudgetV1.Cell0142.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=143) (input:=SourceMainFramesV1.Point0143.input) (pair:=SourceMainFramesV1.Point0143.outputs) SourceHeightEdgesV1.Edge0143.left_defined SourceMainFramesV1.Point0143.input_defined SourceMainFramesV1.Point0143.outputs_defined SourceMainBudgetV1.Cell0143.execution SourceMainBudgetV1.Cell0143.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=144) (input:=SourceMainFramesV1.Point0144.input) (pair:=SourceMainFramesV1.Point0144.outputs) SourceHeightEdgesV1.Edge0144.left_defined SourceMainFramesV1.Point0144.input_defined SourceMainFramesV1.Point0144.outputs_defined SourceMainBudgetV1.Cell0144.execution SourceMainBudgetV1.Cell0144.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=145) (input:=SourceMainFramesV1.Point0145.input) (pair:=SourceMainFramesV1.Point0145.outputs) SourceHeightEdgesV1.Edge0145.left_defined SourceMainFramesV1.Point0145.input_defined SourceMainFramesV1.Point0145.outputs_defined SourceMainBudgetV1.Cell0145.execution SourceMainBudgetV1.Cell0145.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=146) (input:=SourceMainFramesV1.Point0146.input) (pair:=SourceMainFramesV1.Point0146.outputs) SourceHeightEdgesV1.Edge0146.left_defined SourceMainFramesV1.Point0146.input_defined SourceMainFramesV1.Point0146.outputs_defined SourceMainBudgetV1.Cell0146.execution SourceMainBudgetV1.Cell0146.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=147) (input:=SourceMainFramesV1.Point0147.input) (pair:=SourceMainFramesV1.Point0147.outputs) SourceHeightEdgesV1.Edge0147.left_defined SourceMainFramesV1.Point0147.input_defined SourceMainFramesV1.Point0147.outputs_defined SourceMainBudgetV1.Cell0147.execution SourceMainBudgetV1.Cell0147.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=148) (input:=SourceMainFramesV1.Point0148.input) (pair:=SourceMainFramesV1.Point0148.outputs) SourceHeightEdgesV1.Edge0148.left_defined SourceMainFramesV1.Point0148.input_defined SourceMainFramesV1.Point0148.outputs_defined SourceMainBudgetV1.Cell0148.execution SourceMainBudgetV1.Cell0148.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=149) (input:=SourceMainFramesV1.Point0149.input) (pair:=SourceMainFramesV1.Point0149.outputs) SourceHeightEdgesV1.Edge0149.left_defined SourceMainFramesV1.Point0149.input_defined SourceMainFramesV1.Point0149.outputs_defined SourceMainBudgetV1.Cell0149.execution SourceMainBudgetV1.Cell0149.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=150) (input:=SourceMainFramesV1.Point0150.input) (pair:=SourceMainFramesV1.Point0150.outputs) SourceHeightEdgesV1.Edge0150.left_defined SourceMainFramesV1.Point0150.input_defined SourceMainFramesV1.Point0150.outputs_defined SourceMainBudgetV1.Cell0150.execution SourceMainBudgetV1.Cell0150.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=151) (input:=SourceMainFramesV1.Point0151.input) (pair:=SourceMainFramesV1.Point0151.outputs) SourceHeightEdgesV1.Edge0151.left_defined SourceMainFramesV1.Point0151.input_defined SourceMainFramesV1.Point0151.outputs_defined SourceMainBudgetV1.Cell0151.execution SourceMainBudgetV1.Cell0151.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=152) (input:=SourceMainFramesV1.Point0152.input) (pair:=SourceMainFramesV1.Point0152.outputs) SourceHeightEdgesV1.Edge0152.left_defined SourceMainFramesV1.Point0152.input_defined SourceMainFramesV1.Point0152.outputs_defined SourceMainBudgetV1.Cell0152.execution SourceMainBudgetV1.Cell0152.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=153) (input:=SourceMainFramesV1.Point0153.input) (pair:=SourceMainFramesV1.Point0153.outputs) SourceHeightEdgesV1.Edge0153.left_defined SourceMainFramesV1.Point0153.input_defined SourceMainFramesV1.Point0153.outputs_defined SourceMainBudgetV1.Cell0153.execution SourceMainBudgetV1.Cell0153.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=154) (input:=SourceMainFramesV1.Point0154.input) (pair:=SourceMainFramesV1.Point0154.outputs) SourceHeightEdgesV1.Edge0154.left_defined SourceMainFramesV1.Point0154.input_defined SourceMainFramesV1.Point0154.outputs_defined SourceMainBudgetV1.Cell0154.execution SourceMainBudgetV1.Cell0154.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=155) (input:=SourceMainFramesV1.Point0155.input) (pair:=SourceMainFramesV1.Point0155.outputs) SourceHeightEdgesV1.Edge0155.left_defined SourceMainFramesV1.Point0155.input_defined SourceMainFramesV1.Point0155.outputs_defined SourceMainBudgetV1.Cell0155.execution SourceMainBudgetV1.Cell0155.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=156) (input:=SourceMainFramesV1.Point0156.input) (pair:=SourceMainFramesV1.Point0156.outputs) SourceHeightEdgesV1.Edge0156.left_defined SourceMainFramesV1.Point0156.input_defined SourceMainFramesV1.Point0156.outputs_defined SourceMainBudgetV1.Cell0156.execution SourceMainBudgetV1.Cell0156.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=157) (input:=SourceMainFramesV1.Point0157.input) (pair:=SourceMainFramesV1.Point0157.outputs) SourceHeightEdgesV1.Edge0157.left_defined SourceMainFramesV1.Point0157.input_defined SourceMainFramesV1.Point0157.outputs_defined SourceMainBudgetV1.Cell0157.execution SourceMainBudgetV1.Cell0157.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=158) (input:=SourceMainFramesV1.Point0158.input) (pair:=SourceMainFramesV1.Point0158.outputs) SourceHeightEdgesV1.Edge0158.left_defined SourceMainFramesV1.Point0158.input_defined SourceMainFramesV1.Point0158.outputs_defined SourceMainBudgetV1.Cell0158.execution SourceMainBudgetV1.Cell0158.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=159) (input:=SourceMainFramesV1.Point0159.input) (pair:=SourceMainFramesV1.Point0159.outputs) SourceHeightEdgesV1.Edge0159.left_defined SourceMainFramesV1.Point0159.input_defined SourceMainFramesV1.Point0159.outputs_defined SourceMainBudgetV1.Cell0159.execution SourceMainBudgetV1.Cell0159.next_total
end SourceMainBudgetV1.Block04
open Lean Elab
run_elab do
 let n := `SourceMainBudgetV1.Block04.all
 let env ← getEnv
 let some ci := env.find? n | throwError "missing actual source cell block"
 let ax ← Lean.collectAxioms n
 logInfo m!"BUDGET_BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
