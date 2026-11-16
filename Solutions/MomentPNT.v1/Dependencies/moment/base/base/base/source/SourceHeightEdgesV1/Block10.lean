import SourceHeightEdgesV1.Edge0320
import SourceHeightEdgesV1.Edge0321
import SourceHeightEdgesV1.Edge0322
import SourceHeightEdgesV1.Edge0323
import SourceHeightEdgesV1.Edge0324
import SourceHeightEdgesV1.Edge0325
import SourceHeightEdgesV1.Edge0326
import SourceHeightEdgesV1.Edge0327
import SourceHeightEdgesV1.Edge0328
import SourceHeightEdgesV1.Edge0329
import SourceHeightEdgesV1.Edge0330
import SourceHeightEdgesV1.Edge0331
import SourceHeightEdgesV1.Edge0332
import SourceHeightEdgesV1.Edge0333
import SourceHeightEdgesV1.Edge0334
import SourceHeightEdgesV1.Edge0335
import SourceHeightEdgesV1.Edge0336
import SourceHeightEdgesV1.Edge0337
import SourceHeightEdgesV1.Edge0338
import SourceHeightEdgesV1.Edge0339
import SourceHeightEdgesV1.Edge0340
import SourceHeightEdgesV1.Edge0341
import SourceHeightEdgesV1.Edge0342
import SourceHeightEdgesV1.Edge0343
import SourceHeightEdgesV1.Edge0344
import SourceHeightEdgesV1.Edge0345
import SourceHeightEdgesV1.Edge0346
import SourceHeightEdgesV1.Edge0347
import SourceHeightEdgesV1.Edge0348
import SourceHeightEdgesV1.Edge0349
import SourceHeightEdgesV1.Edge0350
import SourceHeightEdgesV1.Edge0351
namespace SourceHeightEdgesV1.Block10
open ScopedC ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem all (j : Nat) (hj : j<32) : SynergyHeightC.FullMainEdges.ExactEdges (32*10+j) := by
 interval_cases j <;> first
  | exact SourceHeightEdgesV1.Edge0320.actual_execution
  | exact SourceHeightEdgesV1.Edge0321.actual_execution
  | exact SourceHeightEdgesV1.Edge0322.actual_execution
  | exact SourceHeightEdgesV1.Edge0323.actual_execution
  | exact SourceHeightEdgesV1.Edge0324.actual_execution
  | exact SourceHeightEdgesV1.Edge0325.actual_execution
  | exact SourceHeightEdgesV1.Edge0326.actual_execution
  | exact SourceHeightEdgesV1.Edge0327.actual_execution
  | exact SourceHeightEdgesV1.Edge0328.actual_execution
  | exact SourceHeightEdgesV1.Edge0329.actual_execution
  | exact SourceHeightEdgesV1.Edge0330.actual_execution
  | exact SourceHeightEdgesV1.Edge0331.actual_execution
  | exact SourceHeightEdgesV1.Edge0332.actual_execution
  | exact SourceHeightEdgesV1.Edge0333.actual_execution
  | exact SourceHeightEdgesV1.Edge0334.actual_execution
  | exact SourceHeightEdgesV1.Edge0335.actual_execution
  | exact SourceHeightEdgesV1.Edge0336.actual_execution
  | exact SourceHeightEdgesV1.Edge0337.actual_execution
  | exact SourceHeightEdgesV1.Edge0338.actual_execution
  | exact SourceHeightEdgesV1.Edge0339.actual_execution
  | exact SourceHeightEdgesV1.Edge0340.actual_execution
  | exact SourceHeightEdgesV1.Edge0341.actual_execution
  | exact SourceHeightEdgesV1.Edge0342.actual_execution
  | exact SourceHeightEdgesV1.Edge0343.actual_execution
  | exact SourceHeightEdgesV1.Edge0344.actual_execution
  | exact SourceHeightEdgesV1.Edge0345.actual_execution
  | exact SourceHeightEdgesV1.Edge0346.actual_execution
  | exact SourceHeightEdgesV1.Edge0347.actual_execution
  | exact SourceHeightEdgesV1.Edge0348.actual_execution
  | exact SourceHeightEdgesV1.Edge0349.actual_execution
  | exact SourceHeightEdgesV1.Edge0350.actual_execution
  | exact SourceHeightEdgesV1.Edge0351.actual_execution
end SourceHeightEdgesV1.Block10
#print axioms SourceHeightEdgesV1.Block10.all
