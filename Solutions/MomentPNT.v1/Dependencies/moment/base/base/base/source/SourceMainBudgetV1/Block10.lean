import SourceMainBudgetV1.Cell0320
import SourceHeightEdgesV1.Edge0320
import SourceMainBudgetV1.Cell0321
import SourceHeightEdgesV1.Edge0321
import SourceMainBudgetV1.Cell0322
import SourceHeightEdgesV1.Edge0322
import SourceMainBudgetV1.Cell0323
import SourceHeightEdgesV1.Edge0323
import SourceMainBudgetV1.Cell0324
import SourceHeightEdgesV1.Edge0324
import SourceMainBudgetV1.Cell0325
import SourceHeightEdgesV1.Edge0325
import SourceMainBudgetV1.Cell0326
import SourceHeightEdgesV1.Edge0326
import SourceMainBudgetV1.Cell0327
import SourceHeightEdgesV1.Edge0327
import SourceMainBudgetV1.Cell0328
import SourceHeightEdgesV1.Edge0328
import SourceMainBudgetV1.Cell0329
import SourceHeightEdgesV1.Edge0329
import SourceMainBudgetV1.Cell0330
import SourceHeightEdgesV1.Edge0330
import SourceMainBudgetV1.Cell0331
import SourceHeightEdgesV1.Edge0331
import SourceMainBudgetV1.Cell0332
import SourceHeightEdgesV1.Edge0332
import SourceMainBudgetV1.Cell0333
import SourceHeightEdgesV1.Edge0333
import SourceMainBudgetV1.Cell0334
import SourceHeightEdgesV1.Edge0334
import SourceMainBudgetV1.Cell0335
import SourceHeightEdgesV1.Edge0335
import SourceMainBudgetV1.Cell0336
import SourceHeightEdgesV1.Edge0336
import SourceMainBudgetV1.Cell0337
import SourceHeightEdgesV1.Edge0337
import SourceMainBudgetV1.Cell0338
import SourceHeightEdgesV1.Edge0338
import SourceMainBudgetV1.Cell0339
import SourceHeightEdgesV1.Edge0339
import SourceMainBudgetV1.Cell0340
import SourceHeightEdgesV1.Edge0340
import SourceMainBudgetV1.Cell0341
import SourceHeightEdgesV1.Edge0341
import SourceMainBudgetV1.Cell0342
import SourceHeightEdgesV1.Edge0342
import SourceMainBudgetV1.Cell0343
import SourceHeightEdgesV1.Edge0343
import SourceMainBudgetV1.Cell0344
import SourceHeightEdgesV1.Edge0344
import SourceMainBudgetV1.Cell0345
import SourceHeightEdgesV1.Edge0345
import SourceMainBudgetV1.Cell0346
import SourceHeightEdgesV1.Edge0346
import SourceMainBudgetV1.Cell0347
import SourceHeightEdgesV1.Edge0347
import SourceMainBudgetV1.Cell0348
import SourceHeightEdgesV1.Edge0348
import SourceMainBudgetV1.Cell0349
import SourceHeightEdgesV1.Edge0349
import SourceMainBudgetV1.Cell0350
import SourceHeightEdgesV1.Edge0350
import SourceMainBudgetV1.Cell0351
import SourceHeightEdgesV1.Edge0351
import SourceMainBudgetV1.Data
import Mathlib.Tactic.IntervalCases
namespace SourceMainBudgetV1.Block10
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem all (i : Nat) (lower : 320 ≤ i) (upper : i < 352) :
 SourceMainBudgetV1.Data.Cell i := by
 interval_cases i
 · exact SourceMainBudgetV1.Data.pack (i:=320) (input:=SourceMainFramesV1.Point0320.input) (pair:=SourceMainFramesV1.Point0320.outputs) SourceHeightEdgesV1.Edge0320.left_defined SourceMainFramesV1.Point0320.input_defined SourceMainFramesV1.Point0320.outputs_defined SourceMainBudgetV1.Cell0320.execution SourceMainBudgetV1.Cell0320.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=321) (input:=SourceMainFramesV1.Point0321.input) (pair:=SourceMainFramesV1.Point0321.outputs) SourceHeightEdgesV1.Edge0321.left_defined SourceMainFramesV1.Point0321.input_defined SourceMainFramesV1.Point0321.outputs_defined SourceMainBudgetV1.Cell0321.execution SourceMainBudgetV1.Cell0321.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=322) (input:=SourceMainFramesV1.Point0322.input) (pair:=SourceMainFramesV1.Point0322.outputs) SourceHeightEdgesV1.Edge0322.left_defined SourceMainFramesV1.Point0322.input_defined SourceMainFramesV1.Point0322.outputs_defined SourceMainBudgetV1.Cell0322.execution SourceMainBudgetV1.Cell0322.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=323) (input:=SourceMainFramesV1.Point0323.input) (pair:=SourceMainFramesV1.Point0323.outputs) SourceHeightEdgesV1.Edge0323.left_defined SourceMainFramesV1.Point0323.input_defined SourceMainFramesV1.Point0323.outputs_defined SourceMainBudgetV1.Cell0323.execution SourceMainBudgetV1.Cell0323.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=324) (input:=SourceMainFramesV1.Point0324.input) (pair:=SourceMainFramesV1.Point0324.outputs) SourceHeightEdgesV1.Edge0324.left_defined SourceMainFramesV1.Point0324.input_defined SourceMainFramesV1.Point0324.outputs_defined SourceMainBudgetV1.Cell0324.execution SourceMainBudgetV1.Cell0324.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=325) (input:=SourceMainFramesV1.Point0325.input) (pair:=SourceMainFramesV1.Point0325.outputs) SourceHeightEdgesV1.Edge0325.left_defined SourceMainFramesV1.Point0325.input_defined SourceMainFramesV1.Point0325.outputs_defined SourceMainBudgetV1.Cell0325.execution SourceMainBudgetV1.Cell0325.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=326) (input:=SourceMainFramesV1.Point0326.input) (pair:=SourceMainFramesV1.Point0326.outputs) SourceHeightEdgesV1.Edge0326.left_defined SourceMainFramesV1.Point0326.input_defined SourceMainFramesV1.Point0326.outputs_defined SourceMainBudgetV1.Cell0326.execution SourceMainBudgetV1.Cell0326.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=327) (input:=SourceMainFramesV1.Point0327.input) (pair:=SourceMainFramesV1.Point0327.outputs) SourceHeightEdgesV1.Edge0327.left_defined SourceMainFramesV1.Point0327.input_defined SourceMainFramesV1.Point0327.outputs_defined SourceMainBudgetV1.Cell0327.execution SourceMainBudgetV1.Cell0327.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=328) (input:=SourceMainFramesV1.Point0328.input) (pair:=SourceMainFramesV1.Point0328.outputs) SourceHeightEdgesV1.Edge0328.left_defined SourceMainFramesV1.Point0328.input_defined SourceMainFramesV1.Point0328.outputs_defined SourceMainBudgetV1.Cell0328.execution SourceMainBudgetV1.Cell0328.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=329) (input:=SourceMainFramesV1.Point0329.input) (pair:=SourceMainFramesV1.Point0329.outputs) SourceHeightEdgesV1.Edge0329.left_defined SourceMainFramesV1.Point0329.input_defined SourceMainFramesV1.Point0329.outputs_defined SourceMainBudgetV1.Cell0329.execution SourceMainBudgetV1.Cell0329.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=330) (input:=SourceMainFramesV1.Point0330.input) (pair:=SourceMainFramesV1.Point0330.outputs) SourceHeightEdgesV1.Edge0330.left_defined SourceMainFramesV1.Point0330.input_defined SourceMainFramesV1.Point0330.outputs_defined SourceMainBudgetV1.Cell0330.execution SourceMainBudgetV1.Cell0330.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=331) (input:=SourceMainFramesV1.Point0331.input) (pair:=SourceMainFramesV1.Point0331.outputs) SourceHeightEdgesV1.Edge0331.left_defined SourceMainFramesV1.Point0331.input_defined SourceMainFramesV1.Point0331.outputs_defined SourceMainBudgetV1.Cell0331.execution SourceMainBudgetV1.Cell0331.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=332) (input:=SourceMainFramesV1.Point0332.input) (pair:=SourceMainFramesV1.Point0332.outputs) SourceHeightEdgesV1.Edge0332.left_defined SourceMainFramesV1.Point0332.input_defined SourceMainFramesV1.Point0332.outputs_defined SourceMainBudgetV1.Cell0332.execution SourceMainBudgetV1.Cell0332.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=333) (input:=SourceMainFramesV1.Point0333.input) (pair:=SourceMainFramesV1.Point0333.outputs) SourceHeightEdgesV1.Edge0333.left_defined SourceMainFramesV1.Point0333.input_defined SourceMainFramesV1.Point0333.outputs_defined SourceMainBudgetV1.Cell0333.execution SourceMainBudgetV1.Cell0333.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=334) (input:=SourceMainFramesV1.Point0334.input) (pair:=SourceMainFramesV1.Point0334.outputs) SourceHeightEdgesV1.Edge0334.left_defined SourceMainFramesV1.Point0334.input_defined SourceMainFramesV1.Point0334.outputs_defined SourceMainBudgetV1.Cell0334.execution SourceMainBudgetV1.Cell0334.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=335) (input:=SourceMainFramesV1.Point0335.input) (pair:=SourceMainFramesV1.Point0335.outputs) SourceHeightEdgesV1.Edge0335.left_defined SourceMainFramesV1.Point0335.input_defined SourceMainFramesV1.Point0335.outputs_defined SourceMainBudgetV1.Cell0335.execution SourceMainBudgetV1.Cell0335.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=336) (input:=SourceMainFramesV1.Point0336.input) (pair:=SourceMainFramesV1.Point0336.outputs) SourceHeightEdgesV1.Edge0336.left_defined SourceMainFramesV1.Point0336.input_defined SourceMainFramesV1.Point0336.outputs_defined SourceMainBudgetV1.Cell0336.execution SourceMainBudgetV1.Cell0336.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=337) (input:=SourceMainFramesV1.Point0337.input) (pair:=SourceMainFramesV1.Point0337.outputs) SourceHeightEdgesV1.Edge0337.left_defined SourceMainFramesV1.Point0337.input_defined SourceMainFramesV1.Point0337.outputs_defined SourceMainBudgetV1.Cell0337.execution SourceMainBudgetV1.Cell0337.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=338) (input:=SourceMainFramesV1.Point0338.input) (pair:=SourceMainFramesV1.Point0338.outputs) SourceHeightEdgesV1.Edge0338.left_defined SourceMainFramesV1.Point0338.input_defined SourceMainFramesV1.Point0338.outputs_defined SourceMainBudgetV1.Cell0338.execution SourceMainBudgetV1.Cell0338.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=339) (input:=SourceMainFramesV1.Point0339.input) (pair:=SourceMainFramesV1.Point0339.outputs) SourceHeightEdgesV1.Edge0339.left_defined SourceMainFramesV1.Point0339.input_defined SourceMainFramesV1.Point0339.outputs_defined SourceMainBudgetV1.Cell0339.execution SourceMainBudgetV1.Cell0339.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=340) (input:=SourceMainFramesV1.Point0340.input) (pair:=SourceMainFramesV1.Point0340.outputs) SourceHeightEdgesV1.Edge0340.left_defined SourceMainFramesV1.Point0340.input_defined SourceMainFramesV1.Point0340.outputs_defined SourceMainBudgetV1.Cell0340.execution SourceMainBudgetV1.Cell0340.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=341) (input:=SourceMainFramesV1.Point0341.input) (pair:=SourceMainFramesV1.Point0341.outputs) SourceHeightEdgesV1.Edge0341.left_defined SourceMainFramesV1.Point0341.input_defined SourceMainFramesV1.Point0341.outputs_defined SourceMainBudgetV1.Cell0341.execution SourceMainBudgetV1.Cell0341.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=342) (input:=SourceMainFramesV1.Point0342.input) (pair:=SourceMainFramesV1.Point0342.outputs) SourceHeightEdgesV1.Edge0342.left_defined SourceMainFramesV1.Point0342.input_defined SourceMainFramesV1.Point0342.outputs_defined SourceMainBudgetV1.Cell0342.execution SourceMainBudgetV1.Cell0342.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=343) (input:=SourceMainFramesV1.Point0343.input) (pair:=SourceMainFramesV1.Point0343.outputs) SourceHeightEdgesV1.Edge0343.left_defined SourceMainFramesV1.Point0343.input_defined SourceMainFramesV1.Point0343.outputs_defined SourceMainBudgetV1.Cell0343.execution SourceMainBudgetV1.Cell0343.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=344) (input:=SourceMainFramesV1.Point0344.input) (pair:=SourceMainFramesV1.Point0344.outputs) SourceHeightEdgesV1.Edge0344.left_defined SourceMainFramesV1.Point0344.input_defined SourceMainFramesV1.Point0344.outputs_defined SourceMainBudgetV1.Cell0344.execution SourceMainBudgetV1.Cell0344.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=345) (input:=SourceMainFramesV1.Point0345.input) (pair:=SourceMainFramesV1.Point0345.outputs) SourceHeightEdgesV1.Edge0345.left_defined SourceMainFramesV1.Point0345.input_defined SourceMainFramesV1.Point0345.outputs_defined SourceMainBudgetV1.Cell0345.execution SourceMainBudgetV1.Cell0345.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=346) (input:=SourceMainFramesV1.Point0346.input) (pair:=SourceMainFramesV1.Point0346.outputs) SourceHeightEdgesV1.Edge0346.left_defined SourceMainFramesV1.Point0346.input_defined SourceMainFramesV1.Point0346.outputs_defined SourceMainBudgetV1.Cell0346.execution SourceMainBudgetV1.Cell0346.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=347) (input:=SourceMainFramesV1.Point0347.input) (pair:=SourceMainFramesV1.Point0347.outputs) SourceHeightEdgesV1.Edge0347.left_defined SourceMainFramesV1.Point0347.input_defined SourceMainFramesV1.Point0347.outputs_defined SourceMainBudgetV1.Cell0347.execution SourceMainBudgetV1.Cell0347.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=348) (input:=SourceMainFramesV1.Point0348.input) (pair:=SourceMainFramesV1.Point0348.outputs) SourceHeightEdgesV1.Edge0348.left_defined SourceMainFramesV1.Point0348.input_defined SourceMainFramesV1.Point0348.outputs_defined SourceMainBudgetV1.Cell0348.execution SourceMainBudgetV1.Cell0348.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=349) (input:=SourceMainFramesV1.Point0349.input) (pair:=SourceMainFramesV1.Point0349.outputs) SourceHeightEdgesV1.Edge0349.left_defined SourceMainFramesV1.Point0349.input_defined SourceMainFramesV1.Point0349.outputs_defined SourceMainBudgetV1.Cell0349.execution SourceMainBudgetV1.Cell0349.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=350) (input:=SourceMainFramesV1.Point0350.input) (pair:=SourceMainFramesV1.Point0350.outputs) SourceHeightEdgesV1.Edge0350.left_defined SourceMainFramesV1.Point0350.input_defined SourceMainFramesV1.Point0350.outputs_defined SourceMainBudgetV1.Cell0350.execution SourceMainBudgetV1.Cell0350.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=351) (input:=SourceMainFramesV1.Point0351.input) (pair:=SourceMainFramesV1.Point0351.outputs) SourceHeightEdgesV1.Edge0351.left_defined SourceMainFramesV1.Point0351.input_defined SourceMainFramesV1.Point0351.outputs_defined SourceMainBudgetV1.Cell0351.execution SourceMainBudgetV1.Cell0351.next_total
end SourceMainBudgetV1.Block10
open Lean Elab
run_elab do
 let n := `SourceMainBudgetV1.Block10.all
 let env ← getEnv
 let some ci := env.find? n | throwError "missing actual source cell block"
 let ax ← Lean.collectAxioms n
 logInfo m!"BUDGET_BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
