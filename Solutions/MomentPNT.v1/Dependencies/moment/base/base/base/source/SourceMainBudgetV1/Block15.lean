import SourceMainBudgetV1.Cell0480
import SourceHeightEdgesV1.Edge0480
import SourceMainBudgetV1.Cell0481
import SourceHeightEdgesV1.Edge0481
import SourceMainBudgetV1.Cell0482
import SourceHeightEdgesV1.Edge0482
import SourceMainBudgetV1.Cell0483
import SourceHeightEdgesV1.Edge0483
import SourceMainBudgetV1.Cell0484
import SourceHeightEdgesV1.Edge0484
import SourceMainBudgetV1.Cell0485
import SourceHeightEdgesV1.Edge0485
import SourceMainBudgetV1.Cell0486
import SourceHeightEdgesV1.Edge0486
import SourceMainBudgetV1.Cell0487
import SourceHeightEdgesV1.Edge0487
import SourceMainBudgetV1.Cell0488
import SourceHeightEdgesV1.Edge0488
import SourceMainBudgetV1.Cell0489
import SourceHeightEdgesV1.Edge0489
import SourceMainBudgetV1.Cell0490
import SourceHeightEdgesV1.Edge0490
import SourceMainBudgetV1.Cell0491
import SourceHeightEdgesV1.Edge0491
import SourceMainBudgetV1.Cell0492
import SourceHeightEdgesV1.Edge0492
import SourceMainBudgetV1.Cell0493
import SourceHeightEdgesV1.Edge0493
import SourceMainBudgetV1.Cell0494
import SourceHeightEdgesV1.Edge0494
import SourceMainBudgetV1.Cell0495
import SourceHeightEdgesV1.Edge0495
import SourceMainBudgetV1.Cell0496
import SourceHeightEdgesV1.Edge0496
import SourceMainBudgetV1.Cell0497
import SourceHeightEdgesV1.Edge0497
import SourceMainBudgetV1.Cell0498
import SourceHeightEdgesV1.Edge0498
import SourceMainBudgetV1.Cell0499
import SourceHeightEdgesV1.Edge0499
import SourceMainBudgetV1.Cell0500
import SourceHeightEdgesV1.Edge0500
import SourceMainBudgetV1.Cell0501
import SourceHeightEdgesV1.Edge0501
import SourceMainBudgetV1.Cell0502
import SourceHeightEdgesV1.Edge0502
import SourceMainBudgetV1.Cell0503
import SourceHeightEdgesV1.Edge0503
import SourceMainBudgetV1.Cell0504
import SourceHeightEdgesV1.Edge0504
import SourceMainBudgetV1.Cell0505
import SourceHeightEdgesV1.Edge0505
import SourceMainBudgetV1.Cell0506
import SourceHeightEdgesV1.Edge0506
import SourceMainBudgetV1.Cell0507
import SourceHeightEdgesV1.Edge0507
import SourceMainBudgetV1.Cell0508
import SourceHeightEdgesV1.Edge0508
import SourceMainBudgetV1.Cell0509
import SourceHeightEdgesV1.Edge0509
import SourceMainBudgetV1.Cell0510
import SourceHeightEdgesV1.Edge0510
import SourceMainBudgetV1.Cell0511
import SourceHeightEdgesV1.Edge0511
import SourceMainBudgetV1.Data
import Mathlib.Tactic.IntervalCases
namespace SourceMainBudgetV1.Block15
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem all (i : Nat) (lower : 480 ≤ i) (upper : i < 512) :
 SourceMainBudgetV1.Data.Cell i := by
 interval_cases i
 · exact SourceMainBudgetV1.Data.pack (i:=480) (input:=SourceMainFramesV1.Point0480.input) (pair:=SourceMainFramesV1.Point0480.outputs) SourceHeightEdgesV1.Edge0480.left_defined SourceMainFramesV1.Point0480.input_defined SourceMainFramesV1.Point0480.outputs_defined SourceMainBudgetV1.Cell0480.execution SourceMainBudgetV1.Cell0480.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=481) (input:=SourceMainFramesV1.Point0481.input) (pair:=SourceMainFramesV1.Point0481.outputs) SourceHeightEdgesV1.Edge0481.left_defined SourceMainFramesV1.Point0481.input_defined SourceMainFramesV1.Point0481.outputs_defined SourceMainBudgetV1.Cell0481.execution SourceMainBudgetV1.Cell0481.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=482) (input:=SourceMainFramesV1.Point0482.input) (pair:=SourceMainFramesV1.Point0482.outputs) SourceHeightEdgesV1.Edge0482.left_defined SourceMainFramesV1.Point0482.input_defined SourceMainFramesV1.Point0482.outputs_defined SourceMainBudgetV1.Cell0482.execution SourceMainBudgetV1.Cell0482.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=483) (input:=SourceMainFramesV1.Point0483.input) (pair:=SourceMainFramesV1.Point0483.outputs) SourceHeightEdgesV1.Edge0483.left_defined SourceMainFramesV1.Point0483.input_defined SourceMainFramesV1.Point0483.outputs_defined SourceMainBudgetV1.Cell0483.execution SourceMainBudgetV1.Cell0483.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=484) (input:=SourceMainFramesV1.Point0484.input) (pair:=SourceMainFramesV1.Point0484.outputs) SourceHeightEdgesV1.Edge0484.left_defined SourceMainFramesV1.Point0484.input_defined SourceMainFramesV1.Point0484.outputs_defined SourceMainBudgetV1.Cell0484.execution SourceMainBudgetV1.Cell0484.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=485) (input:=SourceMainFramesV1.Point0485.input) (pair:=SourceMainFramesV1.Point0485.outputs) SourceHeightEdgesV1.Edge0485.left_defined SourceMainFramesV1.Point0485.input_defined SourceMainFramesV1.Point0485.outputs_defined SourceMainBudgetV1.Cell0485.execution SourceMainBudgetV1.Cell0485.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=486) (input:=SourceMainFramesV1.Point0486.input) (pair:=SourceMainFramesV1.Point0486.outputs) SourceHeightEdgesV1.Edge0486.left_defined SourceMainFramesV1.Point0486.input_defined SourceMainFramesV1.Point0486.outputs_defined SourceMainBudgetV1.Cell0486.execution SourceMainBudgetV1.Cell0486.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=487) (input:=SourceMainFramesV1.Point0487.input) (pair:=SourceMainFramesV1.Point0487.outputs) SourceHeightEdgesV1.Edge0487.left_defined SourceMainFramesV1.Point0487.input_defined SourceMainFramesV1.Point0487.outputs_defined SourceMainBudgetV1.Cell0487.execution SourceMainBudgetV1.Cell0487.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=488) (input:=SourceMainFramesV1.Point0488.input) (pair:=SourceMainFramesV1.Point0488.outputs) SourceHeightEdgesV1.Edge0488.left_defined SourceMainFramesV1.Point0488.input_defined SourceMainFramesV1.Point0488.outputs_defined SourceMainBudgetV1.Cell0488.execution SourceMainBudgetV1.Cell0488.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=489) (input:=SourceMainFramesV1.Point0489.input) (pair:=SourceMainFramesV1.Point0489.outputs) SourceHeightEdgesV1.Edge0489.left_defined SourceMainFramesV1.Point0489.input_defined SourceMainFramesV1.Point0489.outputs_defined SourceMainBudgetV1.Cell0489.execution SourceMainBudgetV1.Cell0489.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=490) (input:=SourceMainFramesV1.Point0490.input) (pair:=SourceMainFramesV1.Point0490.outputs) SourceHeightEdgesV1.Edge0490.left_defined SourceMainFramesV1.Point0490.input_defined SourceMainFramesV1.Point0490.outputs_defined SourceMainBudgetV1.Cell0490.execution SourceMainBudgetV1.Cell0490.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=491) (input:=SourceMainFramesV1.Point0491.input) (pair:=SourceMainFramesV1.Point0491.outputs) SourceHeightEdgesV1.Edge0491.left_defined SourceMainFramesV1.Point0491.input_defined SourceMainFramesV1.Point0491.outputs_defined SourceMainBudgetV1.Cell0491.execution SourceMainBudgetV1.Cell0491.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=492) (input:=SourceMainFramesV1.Point0492.input) (pair:=SourceMainFramesV1.Point0492.outputs) SourceHeightEdgesV1.Edge0492.left_defined SourceMainFramesV1.Point0492.input_defined SourceMainFramesV1.Point0492.outputs_defined SourceMainBudgetV1.Cell0492.execution SourceMainBudgetV1.Cell0492.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=493) (input:=SourceMainFramesV1.Point0493.input) (pair:=SourceMainFramesV1.Point0493.outputs) SourceHeightEdgesV1.Edge0493.left_defined SourceMainFramesV1.Point0493.input_defined SourceMainFramesV1.Point0493.outputs_defined SourceMainBudgetV1.Cell0493.execution SourceMainBudgetV1.Cell0493.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=494) (input:=SourceMainFramesV1.Point0494.input) (pair:=SourceMainFramesV1.Point0494.outputs) SourceHeightEdgesV1.Edge0494.left_defined SourceMainFramesV1.Point0494.input_defined SourceMainFramesV1.Point0494.outputs_defined SourceMainBudgetV1.Cell0494.execution SourceMainBudgetV1.Cell0494.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=495) (input:=SourceMainFramesV1.Point0495.input) (pair:=SourceMainFramesV1.Point0495.outputs) SourceHeightEdgesV1.Edge0495.left_defined SourceMainFramesV1.Point0495.input_defined SourceMainFramesV1.Point0495.outputs_defined SourceMainBudgetV1.Cell0495.execution SourceMainBudgetV1.Cell0495.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=496) (input:=SourceMainFramesV1.Point0496.input) (pair:=SourceMainFramesV1.Point0496.outputs) SourceHeightEdgesV1.Edge0496.left_defined SourceMainFramesV1.Point0496.input_defined SourceMainFramesV1.Point0496.outputs_defined SourceMainBudgetV1.Cell0496.execution SourceMainBudgetV1.Cell0496.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=497) (input:=SourceMainFramesV1.Point0497.input) (pair:=SourceMainFramesV1.Point0497.outputs) SourceHeightEdgesV1.Edge0497.left_defined SourceMainFramesV1.Point0497.input_defined SourceMainFramesV1.Point0497.outputs_defined SourceMainBudgetV1.Cell0497.execution SourceMainBudgetV1.Cell0497.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=498) (input:=SourceMainFramesV1.Point0498.input) (pair:=SourceMainFramesV1.Point0498.outputs) SourceHeightEdgesV1.Edge0498.left_defined SourceMainFramesV1.Point0498.input_defined SourceMainFramesV1.Point0498.outputs_defined SourceMainBudgetV1.Cell0498.execution SourceMainBudgetV1.Cell0498.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=499) (input:=SourceMainFramesV1.Point0499.input) (pair:=SourceMainFramesV1.Point0499.outputs) SourceHeightEdgesV1.Edge0499.left_defined SourceMainFramesV1.Point0499.input_defined SourceMainFramesV1.Point0499.outputs_defined SourceMainBudgetV1.Cell0499.execution SourceMainBudgetV1.Cell0499.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=500) (input:=SourceMainFramesV1.Point0500.input) (pair:=SourceMainFramesV1.Point0500.outputs) SourceHeightEdgesV1.Edge0500.left_defined SourceMainFramesV1.Point0500.input_defined SourceMainFramesV1.Point0500.outputs_defined SourceMainBudgetV1.Cell0500.execution SourceMainBudgetV1.Cell0500.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=501) (input:=SourceMainFramesV1.Point0501.input) (pair:=SourceMainFramesV1.Point0501.outputs) SourceHeightEdgesV1.Edge0501.left_defined SourceMainFramesV1.Point0501.input_defined SourceMainFramesV1.Point0501.outputs_defined SourceMainBudgetV1.Cell0501.execution SourceMainBudgetV1.Cell0501.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=502) (input:=SourceMainFramesV1.Point0502.input) (pair:=SourceMainFramesV1.Point0502.outputs) SourceHeightEdgesV1.Edge0502.left_defined SourceMainFramesV1.Point0502.input_defined SourceMainFramesV1.Point0502.outputs_defined SourceMainBudgetV1.Cell0502.execution SourceMainBudgetV1.Cell0502.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=503) (input:=SourceMainFramesV1.Point0503.input) (pair:=SourceMainFramesV1.Point0503.outputs) SourceHeightEdgesV1.Edge0503.left_defined SourceMainFramesV1.Point0503.input_defined SourceMainFramesV1.Point0503.outputs_defined SourceMainBudgetV1.Cell0503.execution SourceMainBudgetV1.Cell0503.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=504) (input:=SourceMainFramesV1.Point0504.input) (pair:=SourceMainFramesV1.Point0504.outputs) SourceHeightEdgesV1.Edge0504.left_defined SourceMainFramesV1.Point0504.input_defined SourceMainFramesV1.Point0504.outputs_defined SourceMainBudgetV1.Cell0504.execution SourceMainBudgetV1.Cell0504.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=505) (input:=SourceMainFramesV1.Point0505.input) (pair:=SourceMainFramesV1.Point0505.outputs) SourceHeightEdgesV1.Edge0505.left_defined SourceMainFramesV1.Point0505.input_defined SourceMainFramesV1.Point0505.outputs_defined SourceMainBudgetV1.Cell0505.execution SourceMainBudgetV1.Cell0505.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=506) (input:=SourceMainFramesV1.Point0506.input) (pair:=SourceMainFramesV1.Point0506.outputs) SourceHeightEdgesV1.Edge0506.left_defined SourceMainFramesV1.Point0506.input_defined SourceMainFramesV1.Point0506.outputs_defined SourceMainBudgetV1.Cell0506.execution SourceMainBudgetV1.Cell0506.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=507) (input:=SourceMainFramesV1.Point0507.input) (pair:=SourceMainFramesV1.Point0507.outputs) SourceHeightEdgesV1.Edge0507.left_defined SourceMainFramesV1.Point0507.input_defined SourceMainFramesV1.Point0507.outputs_defined SourceMainBudgetV1.Cell0507.execution SourceMainBudgetV1.Cell0507.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=508) (input:=SourceMainFramesV1.Point0508.input) (pair:=SourceMainFramesV1.Point0508.outputs) SourceHeightEdgesV1.Edge0508.left_defined SourceMainFramesV1.Point0508.input_defined SourceMainFramesV1.Point0508.outputs_defined SourceMainBudgetV1.Cell0508.execution SourceMainBudgetV1.Cell0508.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=509) (input:=SourceMainFramesV1.Point0509.input) (pair:=SourceMainFramesV1.Point0509.outputs) SourceHeightEdgesV1.Edge0509.left_defined SourceMainFramesV1.Point0509.input_defined SourceMainFramesV1.Point0509.outputs_defined SourceMainBudgetV1.Cell0509.execution SourceMainBudgetV1.Cell0509.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=510) (input:=SourceMainFramesV1.Point0510.input) (pair:=SourceMainFramesV1.Point0510.outputs) SourceHeightEdgesV1.Edge0510.left_defined SourceMainFramesV1.Point0510.input_defined SourceMainFramesV1.Point0510.outputs_defined SourceMainBudgetV1.Cell0510.execution SourceMainBudgetV1.Cell0510.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=511) (input:=SourceMainFramesV1.Point0511.input) (pair:=SourceMainFramesV1.Point0511.outputs) SourceHeightEdgesV1.Edge0511.left_defined SourceMainFramesV1.Point0511.input_defined SourceMainFramesV1.Point0511.outputs_defined SourceMainBudgetV1.Cell0511.execution SourceMainBudgetV1.Cell0511.next_total
end SourceMainBudgetV1.Block15
open Lean Elab
run_elab do
 let n := `SourceMainBudgetV1.Block15.all
 let env ← getEnv
 let some ci := env.find? n | throwError "missing actual source cell block"
 let ax ← Lean.collectAxioms n
 logInfo m!"BUDGET_BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
