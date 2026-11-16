import SourceMainBudgetV1.Cell0224
import SourceHeightEdgesV1.Edge0224
import SourceMainBudgetV1.Cell0225
import SourceHeightEdgesV1.Edge0225
import SourceMainBudgetV1.Cell0226
import SourceHeightEdgesV1.Edge0226
import SourceMainBudgetV1.Cell0227
import SourceHeightEdgesV1.Edge0227
import SourceMainBudgetV1.Cell0228
import SourceHeightEdgesV1.Edge0228
import SourceMainBudgetV1.Cell0229
import SourceHeightEdgesV1.Edge0229
import SourceMainBudgetV1.Cell0230
import SourceHeightEdgesV1.Edge0230
import SourceMainBudgetV1.Cell0231
import SourceHeightEdgesV1.Edge0231
import SourceMainBudgetV1.Cell0232
import SourceHeightEdgesV1.Edge0232
import SourceMainBudgetV1.Cell0233
import SourceHeightEdgesV1.Edge0233
import SourceMainBudgetV1.Cell0234
import SourceHeightEdgesV1.Edge0234
import SourceMainBudgetV1.Cell0235
import SourceHeightEdgesV1.Edge0235
import SourceMainBudgetV1.Cell0236
import SourceHeightEdgesV1.Edge0236
import SourceMainBudgetV1.Cell0237
import SourceHeightEdgesV1.Edge0237
import SourceMainBudgetV1.Cell0238
import SourceHeightEdgesV1.Edge0238
import SourceMainBudgetV1.Cell0239
import SourceHeightEdgesV1.Edge0239
import SourceMainBudgetV1.Cell0240
import SourceHeightEdgesV1.Edge0240
import SourceMainBudgetV1.Cell0241
import SourceHeightEdgesV1.Edge0241
import SourceMainBudgetV1.Cell0242
import SourceHeightEdgesV1.Edge0242
import SourceMainBudgetV1.Cell0243
import SourceHeightEdgesV1.Edge0243
import SourceMainBudgetV1.Cell0244
import SourceHeightEdgesV1.Edge0244
import SourceMainBudgetV1.Cell0245
import SourceHeightEdgesV1.Edge0245
import SourceMainBudgetV1.Cell0246
import SourceHeightEdgesV1.Edge0246
import SourceMainBudgetV1.Cell0247
import SourceHeightEdgesV1.Edge0247
import SourceMainBudgetV1.Cell0248
import SourceHeightEdgesV1.Edge0248
import SourceMainBudgetV1.Cell0249
import SourceHeightEdgesV1.Edge0249
import SourceMainBudgetV1.Cell0250
import SourceHeightEdgesV1.Edge0250
import SourceMainBudgetV1.Cell0251
import SourceHeightEdgesV1.Edge0251
import SourceMainBudgetV1.Cell0252
import SourceHeightEdgesV1.Edge0252
import SourceMainBudgetV1.Cell0253
import SourceHeightEdgesV1.Edge0253
import SourceMainBudgetV1.Cell0254
import SourceHeightEdgesV1.Edge0254
import SourceMainBudgetV1.Cell0255
import SourceHeightEdgesV1.Edge0255
import SourceMainBudgetV1.Data
import Mathlib.Tactic.IntervalCases
namespace SourceMainBudgetV1.Block07
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem all (i : Nat) (lower : 224 ≤ i) (upper : i < 256) :
 SourceMainBudgetV1.Data.Cell i := by
 interval_cases i
 · exact SourceMainBudgetV1.Data.pack (i:=224) (input:=SourceMainFramesV1.Point0224.input) (pair:=SourceMainFramesV1.Point0224.outputs) SourceHeightEdgesV1.Edge0224.left_defined SourceMainFramesV1.Point0224.input_defined SourceMainFramesV1.Point0224.outputs_defined SourceMainBudgetV1.Cell0224.execution SourceMainBudgetV1.Cell0224.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=225) (input:=SourceMainFramesV1.Point0225.input) (pair:=SourceMainFramesV1.Point0225.outputs) SourceHeightEdgesV1.Edge0225.left_defined SourceMainFramesV1.Point0225.input_defined SourceMainFramesV1.Point0225.outputs_defined SourceMainBudgetV1.Cell0225.execution SourceMainBudgetV1.Cell0225.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=226) (input:=SourceMainFramesV1.Point0226.input) (pair:=SourceMainFramesV1.Point0226.outputs) SourceHeightEdgesV1.Edge0226.left_defined SourceMainFramesV1.Point0226.input_defined SourceMainFramesV1.Point0226.outputs_defined SourceMainBudgetV1.Cell0226.execution SourceMainBudgetV1.Cell0226.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=227) (input:=SourceMainFramesV1.Point0227.input) (pair:=SourceMainFramesV1.Point0227.outputs) SourceHeightEdgesV1.Edge0227.left_defined SourceMainFramesV1.Point0227.input_defined SourceMainFramesV1.Point0227.outputs_defined SourceMainBudgetV1.Cell0227.execution SourceMainBudgetV1.Cell0227.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=228) (input:=SourceMainFramesV1.Point0228.input) (pair:=SourceMainFramesV1.Point0228.outputs) SourceHeightEdgesV1.Edge0228.left_defined SourceMainFramesV1.Point0228.input_defined SourceMainFramesV1.Point0228.outputs_defined SourceMainBudgetV1.Cell0228.execution SourceMainBudgetV1.Cell0228.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=229) (input:=SourceMainFramesV1.Point0229.input) (pair:=SourceMainFramesV1.Point0229.outputs) SourceHeightEdgesV1.Edge0229.left_defined SourceMainFramesV1.Point0229.input_defined SourceMainFramesV1.Point0229.outputs_defined SourceMainBudgetV1.Cell0229.execution SourceMainBudgetV1.Cell0229.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=230) (input:=SourceMainFramesV1.Point0230.input) (pair:=SourceMainFramesV1.Point0230.outputs) SourceHeightEdgesV1.Edge0230.left_defined SourceMainFramesV1.Point0230.input_defined SourceMainFramesV1.Point0230.outputs_defined SourceMainBudgetV1.Cell0230.execution SourceMainBudgetV1.Cell0230.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=231) (input:=SourceMainFramesV1.Point0231.input) (pair:=SourceMainFramesV1.Point0231.outputs) SourceHeightEdgesV1.Edge0231.left_defined SourceMainFramesV1.Point0231.input_defined SourceMainFramesV1.Point0231.outputs_defined SourceMainBudgetV1.Cell0231.execution SourceMainBudgetV1.Cell0231.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=232) (input:=SourceMainFramesV1.Point0232.input) (pair:=SourceMainFramesV1.Point0232.outputs) SourceHeightEdgesV1.Edge0232.left_defined SourceMainFramesV1.Point0232.input_defined SourceMainFramesV1.Point0232.outputs_defined SourceMainBudgetV1.Cell0232.execution SourceMainBudgetV1.Cell0232.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=233) (input:=SourceMainFramesV1.Point0233.input) (pair:=SourceMainFramesV1.Point0233.outputs) SourceHeightEdgesV1.Edge0233.left_defined SourceMainFramesV1.Point0233.input_defined SourceMainFramesV1.Point0233.outputs_defined SourceMainBudgetV1.Cell0233.execution SourceMainBudgetV1.Cell0233.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=234) (input:=SourceMainFramesV1.Point0234.input) (pair:=SourceMainFramesV1.Point0234.outputs) SourceHeightEdgesV1.Edge0234.left_defined SourceMainFramesV1.Point0234.input_defined SourceMainFramesV1.Point0234.outputs_defined SourceMainBudgetV1.Cell0234.execution SourceMainBudgetV1.Cell0234.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=235) (input:=SourceMainFramesV1.Point0235.input) (pair:=SourceMainFramesV1.Point0235.outputs) SourceHeightEdgesV1.Edge0235.left_defined SourceMainFramesV1.Point0235.input_defined SourceMainFramesV1.Point0235.outputs_defined SourceMainBudgetV1.Cell0235.execution SourceMainBudgetV1.Cell0235.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=236) (input:=SourceMainFramesV1.Point0236.input) (pair:=SourceMainFramesV1.Point0236.outputs) SourceHeightEdgesV1.Edge0236.left_defined SourceMainFramesV1.Point0236.input_defined SourceMainFramesV1.Point0236.outputs_defined SourceMainBudgetV1.Cell0236.execution SourceMainBudgetV1.Cell0236.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=237) (input:=SourceMainFramesV1.Point0237.input) (pair:=SourceMainFramesV1.Point0237.outputs) SourceHeightEdgesV1.Edge0237.left_defined SourceMainFramesV1.Point0237.input_defined SourceMainFramesV1.Point0237.outputs_defined SourceMainBudgetV1.Cell0237.execution SourceMainBudgetV1.Cell0237.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=238) (input:=SourceMainFramesV1.Point0238.input) (pair:=SourceMainFramesV1.Point0238.outputs) SourceHeightEdgesV1.Edge0238.left_defined SourceMainFramesV1.Point0238.input_defined SourceMainFramesV1.Point0238.outputs_defined SourceMainBudgetV1.Cell0238.execution SourceMainBudgetV1.Cell0238.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=239) (input:=SourceMainFramesV1.Point0239.input) (pair:=SourceMainFramesV1.Point0239.outputs) SourceHeightEdgesV1.Edge0239.left_defined SourceMainFramesV1.Point0239.input_defined SourceMainFramesV1.Point0239.outputs_defined SourceMainBudgetV1.Cell0239.execution SourceMainBudgetV1.Cell0239.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=240) (input:=SourceMainFramesV1.Point0240.input) (pair:=SourceMainFramesV1.Point0240.outputs) SourceHeightEdgesV1.Edge0240.left_defined SourceMainFramesV1.Point0240.input_defined SourceMainFramesV1.Point0240.outputs_defined SourceMainBudgetV1.Cell0240.execution SourceMainBudgetV1.Cell0240.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=241) (input:=SourceMainFramesV1.Point0241.input) (pair:=SourceMainFramesV1.Point0241.outputs) SourceHeightEdgesV1.Edge0241.left_defined SourceMainFramesV1.Point0241.input_defined SourceMainFramesV1.Point0241.outputs_defined SourceMainBudgetV1.Cell0241.execution SourceMainBudgetV1.Cell0241.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=242) (input:=SourceMainFramesV1.Point0242.input) (pair:=SourceMainFramesV1.Point0242.outputs) SourceHeightEdgesV1.Edge0242.left_defined SourceMainFramesV1.Point0242.input_defined SourceMainFramesV1.Point0242.outputs_defined SourceMainBudgetV1.Cell0242.execution SourceMainBudgetV1.Cell0242.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=243) (input:=SourceMainFramesV1.Point0243.input) (pair:=SourceMainFramesV1.Point0243.outputs) SourceHeightEdgesV1.Edge0243.left_defined SourceMainFramesV1.Point0243.input_defined SourceMainFramesV1.Point0243.outputs_defined SourceMainBudgetV1.Cell0243.execution SourceMainBudgetV1.Cell0243.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=244) (input:=SourceMainFramesV1.Point0244.input) (pair:=SourceMainFramesV1.Point0244.outputs) SourceHeightEdgesV1.Edge0244.left_defined SourceMainFramesV1.Point0244.input_defined SourceMainFramesV1.Point0244.outputs_defined SourceMainBudgetV1.Cell0244.execution SourceMainBudgetV1.Cell0244.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=245) (input:=SourceMainFramesV1.Point0245.input) (pair:=SourceMainFramesV1.Point0245.outputs) SourceHeightEdgesV1.Edge0245.left_defined SourceMainFramesV1.Point0245.input_defined SourceMainFramesV1.Point0245.outputs_defined SourceMainBudgetV1.Cell0245.execution SourceMainBudgetV1.Cell0245.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=246) (input:=SourceMainFramesV1.Point0246.input) (pair:=SourceMainFramesV1.Point0246.outputs) SourceHeightEdgesV1.Edge0246.left_defined SourceMainFramesV1.Point0246.input_defined SourceMainFramesV1.Point0246.outputs_defined SourceMainBudgetV1.Cell0246.execution SourceMainBudgetV1.Cell0246.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=247) (input:=SourceMainFramesV1.Point0247.input) (pair:=SourceMainFramesV1.Point0247.outputs) SourceHeightEdgesV1.Edge0247.left_defined SourceMainFramesV1.Point0247.input_defined SourceMainFramesV1.Point0247.outputs_defined SourceMainBudgetV1.Cell0247.execution SourceMainBudgetV1.Cell0247.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=248) (input:=SourceMainFramesV1.Point0248.input) (pair:=SourceMainFramesV1.Point0248.outputs) SourceHeightEdgesV1.Edge0248.left_defined SourceMainFramesV1.Point0248.input_defined SourceMainFramesV1.Point0248.outputs_defined SourceMainBudgetV1.Cell0248.execution SourceMainBudgetV1.Cell0248.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=249) (input:=SourceMainFramesV1.Point0249.input) (pair:=SourceMainFramesV1.Point0249.outputs) SourceHeightEdgesV1.Edge0249.left_defined SourceMainFramesV1.Point0249.input_defined SourceMainFramesV1.Point0249.outputs_defined SourceMainBudgetV1.Cell0249.execution SourceMainBudgetV1.Cell0249.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=250) (input:=SourceMainFramesV1.Point0250.input) (pair:=SourceMainFramesV1.Point0250.outputs) SourceHeightEdgesV1.Edge0250.left_defined SourceMainFramesV1.Point0250.input_defined SourceMainFramesV1.Point0250.outputs_defined SourceMainBudgetV1.Cell0250.execution SourceMainBudgetV1.Cell0250.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=251) (input:=SourceMainFramesV1.Point0251.input) (pair:=SourceMainFramesV1.Point0251.outputs) SourceHeightEdgesV1.Edge0251.left_defined SourceMainFramesV1.Point0251.input_defined SourceMainFramesV1.Point0251.outputs_defined SourceMainBudgetV1.Cell0251.execution SourceMainBudgetV1.Cell0251.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=252) (input:=SourceMainFramesV1.Point0252.input) (pair:=SourceMainFramesV1.Point0252.outputs) SourceHeightEdgesV1.Edge0252.left_defined SourceMainFramesV1.Point0252.input_defined SourceMainFramesV1.Point0252.outputs_defined SourceMainBudgetV1.Cell0252.execution SourceMainBudgetV1.Cell0252.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=253) (input:=SourceMainFramesV1.Point0253.input) (pair:=SourceMainFramesV1.Point0253.outputs) SourceHeightEdgesV1.Edge0253.left_defined SourceMainFramesV1.Point0253.input_defined SourceMainFramesV1.Point0253.outputs_defined SourceMainBudgetV1.Cell0253.execution SourceMainBudgetV1.Cell0253.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=254) (input:=SourceMainFramesV1.Point0254.input) (pair:=SourceMainFramesV1.Point0254.outputs) SourceHeightEdgesV1.Edge0254.left_defined SourceMainFramesV1.Point0254.input_defined SourceMainFramesV1.Point0254.outputs_defined SourceMainBudgetV1.Cell0254.execution SourceMainBudgetV1.Cell0254.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=255) (input:=SourceMainFramesV1.Point0255.input) (pair:=SourceMainFramesV1.Point0255.outputs) SourceHeightEdgesV1.Edge0255.left_defined SourceMainFramesV1.Point0255.input_defined SourceMainFramesV1.Point0255.outputs_defined SourceMainBudgetV1.Cell0255.execution SourceMainBudgetV1.Cell0255.next_total
end SourceMainBudgetV1.Block07
open Lean Elab
run_elab do
 let n := `SourceMainBudgetV1.Block07.all
 let env ← getEnv
 let some ci := env.find? n | throwError "missing actual source cell block"
 let ax ← Lean.collectAxioms n
 logInfo m!"BUDGET_BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
