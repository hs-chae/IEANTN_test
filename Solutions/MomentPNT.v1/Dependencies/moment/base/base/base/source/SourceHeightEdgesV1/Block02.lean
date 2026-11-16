import SourceHeightEdgesV1.Edge0064
import SourceHeightEdgesV1.Edge0065
import SourceHeightEdgesV1.Edge0066
import SourceHeightEdgesV1.Edge0067
import SourceHeightEdgesV1.Edge0068
import SourceHeightEdgesV1.Edge0069
import SourceHeightEdgesV1.Edge0070
import SourceHeightEdgesV1.Edge0071
import SourceHeightEdgesV1.Edge0072
import SourceHeightEdgesV1.Edge0073
import SourceHeightEdgesV1.Edge0074
import SourceHeightEdgesV1.Edge0075
import SourceHeightEdgesV1.Edge0076
import SourceHeightEdgesV1.Edge0077
import SourceHeightEdgesV1.Edge0078
import SourceHeightEdgesV1.Edge0079
import SourceHeightEdgesV1.Edge0080
import SourceHeightEdgesV1.Edge0081
import SourceHeightEdgesV1.Edge0082
import SourceHeightEdgesV1.Edge0083
import SourceHeightEdgesV1.Edge0084
import SourceHeightEdgesV1.Edge0085
import SourceHeightEdgesV1.Edge0086
import SourceHeightEdgesV1.Edge0087
import SourceHeightEdgesV1.Edge0088
import SourceHeightEdgesV1.Edge0089
import SourceHeightEdgesV1.Edge0090
import SourceHeightEdgesV1.Edge0091
import SourceHeightEdgesV1.Edge0092
import SourceHeightEdgesV1.Edge0093
import SourceHeightEdgesV1.Edge0094
import SourceHeightEdgesV1.Edge0095
namespace SourceHeightEdgesV1.Block02
open ScopedC ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem all (j : Nat) (hj : j<32) : SynergyHeightC.FullMainEdges.ExactEdges (32*2+j) := by
 interval_cases j <;> first
  | exact SourceHeightEdgesV1.Edge0064.actual_execution
  | exact SourceHeightEdgesV1.Edge0065.actual_execution
  | exact SourceHeightEdgesV1.Edge0066.actual_execution
  | exact SourceHeightEdgesV1.Edge0067.actual_execution
  | exact SourceHeightEdgesV1.Edge0068.actual_execution
  | exact SourceHeightEdgesV1.Edge0069.actual_execution
  | exact SourceHeightEdgesV1.Edge0070.actual_execution
  | exact SourceHeightEdgesV1.Edge0071.actual_execution
  | exact SourceHeightEdgesV1.Edge0072.actual_execution
  | exact SourceHeightEdgesV1.Edge0073.actual_execution
  | exact SourceHeightEdgesV1.Edge0074.actual_execution
  | exact SourceHeightEdgesV1.Edge0075.actual_execution
  | exact SourceHeightEdgesV1.Edge0076.actual_execution
  | exact SourceHeightEdgesV1.Edge0077.actual_execution
  | exact SourceHeightEdgesV1.Edge0078.actual_execution
  | exact SourceHeightEdgesV1.Edge0079.actual_execution
  | exact SourceHeightEdgesV1.Edge0080.actual_execution
  | exact SourceHeightEdgesV1.Edge0081.actual_execution
  | exact SourceHeightEdgesV1.Edge0082.actual_execution
  | exact SourceHeightEdgesV1.Edge0083.actual_execution
  | exact SourceHeightEdgesV1.Edge0084.actual_execution
  | exact SourceHeightEdgesV1.Edge0085.actual_execution
  | exact SourceHeightEdgesV1.Edge0086.actual_execution
  | exact SourceHeightEdgesV1.Edge0087.actual_execution
  | exact SourceHeightEdgesV1.Edge0088.actual_execution
  | exact SourceHeightEdgesV1.Edge0089.actual_execution
  | exact SourceHeightEdgesV1.Edge0090.actual_execution
  | exact SourceHeightEdgesV1.Edge0091.actual_execution
  | exact SourceHeightEdgesV1.Edge0092.actual_execution
  | exact SourceHeightEdgesV1.Edge0093.actual_execution
  | exact SourceHeightEdgesV1.Edge0094.actual_execution
  | exact SourceHeightEdgesV1.Edge0095.actual_execution
end SourceHeightEdgesV1.Block02
#print axioms SourceHeightEdgesV1.Block02.all
