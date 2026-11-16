import SourceMainBudgetV1.Cell0512
import SourceHeightEdgesV1.Edge0512
import SourceMainBudgetV1.Cell0513
import SourceHeightEdgesV1.Edge0513
import SourceMainBudgetV1.Cell0514
import SourceHeightEdgesV1.Edge0514
import SourceMainBudgetV1.Cell0515
import SourceHeightEdgesV1.Edge0515
import SourceMainBudgetV1.Cell0516
import SourceHeightEdgesV1.Edge0516
import SourceMainBudgetV1.Cell0517
import SourceHeightEdgesV1.Edge0517
import SourceMainBudgetV1.Cell0518
import SourceHeightEdgesV1.Edge0518
import SourceMainBudgetV1.Cell0519
import SourceHeightEdgesV1.Edge0519
import SourceMainBudgetV1.Cell0520
import SourceHeightEdgesV1.Edge0520
import SourceMainBudgetV1.Cell0521
import SourceHeightEdgesV1.Edge0521
import SourceMainBudgetV1.Cell0522
import SourceHeightEdgesV1.Edge0522
import SourceMainBudgetV1.Cell0523
import SourceHeightEdgesV1.Edge0523
import SourceMainBudgetV1.Cell0524
import SourceHeightEdgesV1.Edge0524
import SourceMainBudgetV1.Cell0525
import SourceHeightEdgesV1.Edge0525
import SourceMainBudgetV1.Cell0526
import SourceHeightEdgesV1.Edge0526
import SourceMainBudgetV1.Cell0527
import SourceHeightEdgesV1.Edge0527
import SourceMainBudgetV1.Cell0528
import SourceHeightEdgesV1.Edge0528
import SourceMainBudgetV1.Cell0529
import SourceHeightEdgesV1.Edge0529
import SourceMainBudgetV1.Cell0530
import SourceHeightEdgesV1.Edge0530
import SourceMainBudgetV1.Cell0531
import SourceHeightEdgesV1.Edge0531
import SourceMainBudgetV1.Cell0532
import SourceHeightEdgesV1.Edge0532
import SourceMainBudgetV1.Cell0533
import SourceHeightEdgesV1.Edge0533
import SourceMainBudgetV1.Cell0534
import SourceHeightEdgesV1.Edge0534
import SourceMainBudgetV1.Cell0535
import SourceHeightEdgesV1.Edge0535
import SourceMainBudgetV1.Cell0536
import SourceHeightEdgesV1.Edge0536
import SourceMainBudgetV1.Cell0537
import SourceHeightEdgesV1.Edge0537
import SourceMainBudgetV1.Cell0538
import SourceHeightEdgesV1.Edge0538
import SourceMainBudgetV1.Cell0539
import SourceHeightEdgesV1.Edge0539
import SourceMainBudgetV1.Cell0540
import SourceHeightEdgesV1.Edge0540
import SourceMainBudgetV1.Cell0541
import SourceHeightEdgesV1.Edge0541
import SourceMainBudgetV1.Cell0542
import SourceHeightEdgesV1.Edge0542
import SourceMainBudgetV1.Cell0543
import SourceHeightEdgesV1.Edge0543
import SourceMainBudgetV1.Data
import Mathlib.Tactic.IntervalCases
namespace SourceMainBudgetV1.Block16
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem all (i : Nat) (lower : 512 ≤ i) (upper : i < 544) :
 SourceMainBudgetV1.Data.Cell i := by
 interval_cases i
 · exact SourceMainBudgetV1.Data.pack (i:=512) (input:=SourceMainFramesV1.Point0512.input) (pair:=SourceMainFramesV1.Point0512.outputs) SourceHeightEdgesV1.Edge0512.left_defined SourceMainFramesV1.Point0512.input_defined SourceMainFramesV1.Point0512.outputs_defined SourceMainBudgetV1.Cell0512.execution SourceMainBudgetV1.Cell0512.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=513) (input:=SourceMainFramesV1.Point0513.input) (pair:=SourceMainFramesV1.Point0513.outputs) SourceHeightEdgesV1.Edge0513.left_defined SourceMainFramesV1.Point0513.input_defined SourceMainFramesV1.Point0513.outputs_defined SourceMainBudgetV1.Cell0513.execution SourceMainBudgetV1.Cell0513.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=514) (input:=SourceMainFramesV1.Point0514.input) (pair:=SourceMainFramesV1.Point0514.outputs) SourceHeightEdgesV1.Edge0514.left_defined SourceMainFramesV1.Point0514.input_defined SourceMainFramesV1.Point0514.outputs_defined SourceMainBudgetV1.Cell0514.execution SourceMainBudgetV1.Cell0514.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=515) (input:=SourceMainFramesV1.Point0515.input) (pair:=SourceMainFramesV1.Point0515.outputs) SourceHeightEdgesV1.Edge0515.left_defined SourceMainFramesV1.Point0515.input_defined SourceMainFramesV1.Point0515.outputs_defined SourceMainBudgetV1.Cell0515.execution SourceMainBudgetV1.Cell0515.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=516) (input:=SourceMainFramesV1.Point0516.input) (pair:=SourceMainFramesV1.Point0516.outputs) SourceHeightEdgesV1.Edge0516.left_defined SourceMainFramesV1.Point0516.input_defined SourceMainFramesV1.Point0516.outputs_defined SourceMainBudgetV1.Cell0516.execution SourceMainBudgetV1.Cell0516.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=517) (input:=SourceMainFramesV1.Point0517.input) (pair:=SourceMainFramesV1.Point0517.outputs) SourceHeightEdgesV1.Edge0517.left_defined SourceMainFramesV1.Point0517.input_defined SourceMainFramesV1.Point0517.outputs_defined SourceMainBudgetV1.Cell0517.execution SourceMainBudgetV1.Cell0517.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=518) (input:=SourceMainFramesV1.Point0518.input) (pair:=SourceMainFramesV1.Point0518.outputs) SourceHeightEdgesV1.Edge0518.left_defined SourceMainFramesV1.Point0518.input_defined SourceMainFramesV1.Point0518.outputs_defined SourceMainBudgetV1.Cell0518.execution SourceMainBudgetV1.Cell0518.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=519) (input:=SourceMainFramesV1.Point0519.input) (pair:=SourceMainFramesV1.Point0519.outputs) SourceHeightEdgesV1.Edge0519.left_defined SourceMainFramesV1.Point0519.input_defined SourceMainFramesV1.Point0519.outputs_defined SourceMainBudgetV1.Cell0519.execution SourceMainBudgetV1.Cell0519.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=520) (input:=SourceMainFramesV1.Point0520.input) (pair:=SourceMainFramesV1.Point0520.outputs) SourceHeightEdgesV1.Edge0520.left_defined SourceMainFramesV1.Point0520.input_defined SourceMainFramesV1.Point0520.outputs_defined SourceMainBudgetV1.Cell0520.execution SourceMainBudgetV1.Cell0520.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=521) (input:=SourceMainFramesV1.Point0521.input) (pair:=SourceMainFramesV1.Point0521.outputs) SourceHeightEdgesV1.Edge0521.left_defined SourceMainFramesV1.Point0521.input_defined SourceMainFramesV1.Point0521.outputs_defined SourceMainBudgetV1.Cell0521.execution SourceMainBudgetV1.Cell0521.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=522) (input:=SourceMainFramesV1.Point0522.input) (pair:=SourceMainFramesV1.Point0522.outputs) SourceHeightEdgesV1.Edge0522.left_defined SourceMainFramesV1.Point0522.input_defined SourceMainFramesV1.Point0522.outputs_defined SourceMainBudgetV1.Cell0522.execution SourceMainBudgetV1.Cell0522.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=523) (input:=SourceMainFramesV1.Point0523.input) (pair:=SourceMainFramesV1.Point0523.outputs) SourceHeightEdgesV1.Edge0523.left_defined SourceMainFramesV1.Point0523.input_defined SourceMainFramesV1.Point0523.outputs_defined SourceMainBudgetV1.Cell0523.execution SourceMainBudgetV1.Cell0523.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=524) (input:=SourceMainFramesV1.Point0524.input) (pair:=SourceMainFramesV1.Point0524.outputs) SourceHeightEdgesV1.Edge0524.left_defined SourceMainFramesV1.Point0524.input_defined SourceMainFramesV1.Point0524.outputs_defined SourceMainBudgetV1.Cell0524.execution SourceMainBudgetV1.Cell0524.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=525) (input:=SourceMainFramesV1.Point0525.input) (pair:=SourceMainFramesV1.Point0525.outputs) SourceHeightEdgesV1.Edge0525.left_defined SourceMainFramesV1.Point0525.input_defined SourceMainFramesV1.Point0525.outputs_defined SourceMainBudgetV1.Cell0525.execution SourceMainBudgetV1.Cell0525.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=526) (input:=SourceMainFramesV1.Point0526.input) (pair:=SourceMainFramesV1.Point0526.outputs) SourceHeightEdgesV1.Edge0526.left_defined SourceMainFramesV1.Point0526.input_defined SourceMainFramesV1.Point0526.outputs_defined SourceMainBudgetV1.Cell0526.execution SourceMainBudgetV1.Cell0526.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=527) (input:=SourceMainFramesV1.Point0527.input) (pair:=SourceMainFramesV1.Point0527.outputs) SourceHeightEdgesV1.Edge0527.left_defined SourceMainFramesV1.Point0527.input_defined SourceMainFramesV1.Point0527.outputs_defined SourceMainBudgetV1.Cell0527.execution SourceMainBudgetV1.Cell0527.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=528) (input:=SourceMainFramesV1.Point0528.input) (pair:=SourceMainFramesV1.Point0528.outputs) SourceHeightEdgesV1.Edge0528.left_defined SourceMainFramesV1.Point0528.input_defined SourceMainFramesV1.Point0528.outputs_defined SourceMainBudgetV1.Cell0528.execution SourceMainBudgetV1.Cell0528.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=529) (input:=SourceMainFramesV1.Point0529.input) (pair:=SourceMainFramesV1.Point0529.outputs) SourceHeightEdgesV1.Edge0529.left_defined SourceMainFramesV1.Point0529.input_defined SourceMainFramesV1.Point0529.outputs_defined SourceMainBudgetV1.Cell0529.execution SourceMainBudgetV1.Cell0529.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=530) (input:=SourceMainFramesV1.Point0530.input) (pair:=SourceMainFramesV1.Point0530.outputs) SourceHeightEdgesV1.Edge0530.left_defined SourceMainFramesV1.Point0530.input_defined SourceMainFramesV1.Point0530.outputs_defined SourceMainBudgetV1.Cell0530.execution SourceMainBudgetV1.Cell0530.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=531) (input:=SourceMainFramesV1.Point0531.input) (pair:=SourceMainFramesV1.Point0531.outputs) SourceHeightEdgesV1.Edge0531.left_defined SourceMainFramesV1.Point0531.input_defined SourceMainFramesV1.Point0531.outputs_defined SourceMainBudgetV1.Cell0531.execution SourceMainBudgetV1.Cell0531.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=532) (input:=SourceMainFramesV1.Point0532.input) (pair:=SourceMainFramesV1.Point0532.outputs) SourceHeightEdgesV1.Edge0532.left_defined SourceMainFramesV1.Point0532.input_defined SourceMainFramesV1.Point0532.outputs_defined SourceMainBudgetV1.Cell0532.execution SourceMainBudgetV1.Cell0532.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=533) (input:=SourceMainFramesV1.Point0533.input) (pair:=SourceMainFramesV1.Point0533.outputs) SourceHeightEdgesV1.Edge0533.left_defined SourceMainFramesV1.Point0533.input_defined SourceMainFramesV1.Point0533.outputs_defined SourceMainBudgetV1.Cell0533.execution SourceMainBudgetV1.Cell0533.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=534) (input:=SourceMainFramesV1.Point0534.input) (pair:=SourceMainFramesV1.Point0534.outputs) SourceHeightEdgesV1.Edge0534.left_defined SourceMainFramesV1.Point0534.input_defined SourceMainFramesV1.Point0534.outputs_defined SourceMainBudgetV1.Cell0534.execution SourceMainBudgetV1.Cell0534.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=535) (input:=SourceMainFramesV1.Point0535.input) (pair:=SourceMainFramesV1.Point0535.outputs) SourceHeightEdgesV1.Edge0535.left_defined SourceMainFramesV1.Point0535.input_defined SourceMainFramesV1.Point0535.outputs_defined SourceMainBudgetV1.Cell0535.execution SourceMainBudgetV1.Cell0535.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=536) (input:=SourceMainFramesV1.Point0536.input) (pair:=SourceMainFramesV1.Point0536.outputs) SourceHeightEdgesV1.Edge0536.left_defined SourceMainFramesV1.Point0536.input_defined SourceMainFramesV1.Point0536.outputs_defined SourceMainBudgetV1.Cell0536.execution SourceMainBudgetV1.Cell0536.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=537) (input:=SourceMainFramesV1.Point0537.input) (pair:=SourceMainFramesV1.Point0537.outputs) SourceHeightEdgesV1.Edge0537.left_defined SourceMainFramesV1.Point0537.input_defined SourceMainFramesV1.Point0537.outputs_defined SourceMainBudgetV1.Cell0537.execution SourceMainBudgetV1.Cell0537.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=538) (input:=SourceMainFramesV1.Point0538.input) (pair:=SourceMainFramesV1.Point0538.outputs) SourceHeightEdgesV1.Edge0538.left_defined SourceMainFramesV1.Point0538.input_defined SourceMainFramesV1.Point0538.outputs_defined SourceMainBudgetV1.Cell0538.execution SourceMainBudgetV1.Cell0538.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=539) (input:=SourceMainFramesV1.Point0539.input) (pair:=SourceMainFramesV1.Point0539.outputs) SourceHeightEdgesV1.Edge0539.left_defined SourceMainFramesV1.Point0539.input_defined SourceMainFramesV1.Point0539.outputs_defined SourceMainBudgetV1.Cell0539.execution SourceMainBudgetV1.Cell0539.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=540) (input:=SourceMainFramesV1.Point0540.input) (pair:=SourceMainFramesV1.Point0540.outputs) SourceHeightEdgesV1.Edge0540.left_defined SourceMainFramesV1.Point0540.input_defined SourceMainFramesV1.Point0540.outputs_defined SourceMainBudgetV1.Cell0540.execution SourceMainBudgetV1.Cell0540.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=541) (input:=SourceMainFramesV1.Point0541.input) (pair:=SourceMainFramesV1.Point0541.outputs) SourceHeightEdgesV1.Edge0541.left_defined SourceMainFramesV1.Point0541.input_defined SourceMainFramesV1.Point0541.outputs_defined SourceMainBudgetV1.Cell0541.execution SourceMainBudgetV1.Cell0541.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=542) (input:=SourceMainFramesV1.Point0542.input) (pair:=SourceMainFramesV1.Point0542.outputs) SourceHeightEdgesV1.Edge0542.left_defined SourceMainFramesV1.Point0542.input_defined SourceMainFramesV1.Point0542.outputs_defined SourceMainBudgetV1.Cell0542.execution SourceMainBudgetV1.Cell0542.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=543) (input:=SourceMainFramesV1.Point0543.input) (pair:=SourceMainFramesV1.Point0543.outputs) SourceHeightEdgesV1.Edge0543.left_defined SourceMainFramesV1.Point0543.input_defined SourceMainFramesV1.Point0543.outputs_defined SourceMainBudgetV1.Cell0543.execution SourceMainBudgetV1.Cell0543.next_total
end SourceMainBudgetV1.Block16
open Lean Elab
run_elab do
 let n := `SourceMainBudgetV1.Block16.all
 let env ← getEnv
 let some ci := env.find? n | throwError "missing actual source cell block"
 let ax ← Lean.collectAxioms n
 logInfo m!"BUDGET_BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
