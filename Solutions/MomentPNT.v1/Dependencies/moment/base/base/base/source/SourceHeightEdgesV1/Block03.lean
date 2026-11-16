import SourceHeightEdgesV1.Edge0096
import SourceHeightEdgesV1.Edge0097
import SourceHeightEdgesV1.Edge0098
import SourceHeightEdgesV1.Edge0099
import SourceHeightEdgesV1.Edge0100
import SourceHeightEdgesV1.Edge0101
import SourceHeightEdgesV1.Edge0102
import SourceHeightEdgesV1.Edge0103
import SourceHeightEdgesV1.Edge0104
import SourceHeightEdgesV1.Edge0105
import SourceHeightEdgesV1.Edge0106
import SourceHeightEdgesV1.Edge0107
import SourceHeightEdgesV1.Edge0108
import SourceHeightEdgesV1.Edge0109
import SourceHeightEdgesV1.Edge0110
import SourceHeightEdgesV1.Edge0111
import SourceHeightEdgesV1.Edge0112
import SourceHeightEdgesV1.Edge0113
import SourceHeightEdgesV1.Edge0114
import SourceHeightEdgesV1.Edge0115
import SourceHeightEdgesV1.Edge0116
import SourceHeightEdgesV1.Edge0117
import SourceHeightEdgesV1.Edge0118
import SourceHeightEdgesV1.Edge0119
import SourceHeightEdgesV1.Edge0120
import SourceHeightEdgesV1.Edge0121
import SourceHeightEdgesV1.Edge0122
import SourceHeightEdgesV1.Edge0123
import SourceHeightEdgesV1.Edge0124
import SourceHeightEdgesV1.Edge0125
import SourceHeightEdgesV1.Edge0126
import SourceHeightEdgesV1.Edge0127
namespace SourceHeightEdgesV1.Block03
open ScopedC ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem all (j : Nat) (hj : j<32) : SynergyHeightC.FullMainEdges.ExactEdges (32*3+j) := by
 interval_cases j <;> first
  | exact SourceHeightEdgesV1.Edge0096.actual_execution
  | exact SourceHeightEdgesV1.Edge0097.actual_execution
  | exact SourceHeightEdgesV1.Edge0098.actual_execution
  | exact SourceHeightEdgesV1.Edge0099.actual_execution
  | exact SourceHeightEdgesV1.Edge0100.actual_execution
  | exact SourceHeightEdgesV1.Edge0101.actual_execution
  | exact SourceHeightEdgesV1.Edge0102.actual_execution
  | exact SourceHeightEdgesV1.Edge0103.actual_execution
  | exact SourceHeightEdgesV1.Edge0104.actual_execution
  | exact SourceHeightEdgesV1.Edge0105.actual_execution
  | exact SourceHeightEdgesV1.Edge0106.actual_execution
  | exact SourceHeightEdgesV1.Edge0107.actual_execution
  | exact SourceHeightEdgesV1.Edge0108.actual_execution
  | exact SourceHeightEdgesV1.Edge0109.actual_execution
  | exact SourceHeightEdgesV1.Edge0110.actual_execution
  | exact SourceHeightEdgesV1.Edge0111.actual_execution
  | exact SourceHeightEdgesV1.Edge0112.actual_execution
  | exact SourceHeightEdgesV1.Edge0113.actual_execution
  | exact SourceHeightEdgesV1.Edge0114.actual_execution
  | exact SourceHeightEdgesV1.Edge0115.actual_execution
  | exact SourceHeightEdgesV1.Edge0116.actual_execution
  | exact SourceHeightEdgesV1.Edge0117.actual_execution
  | exact SourceHeightEdgesV1.Edge0118.actual_execution
  | exact SourceHeightEdgesV1.Edge0119.actual_execution
  | exact SourceHeightEdgesV1.Edge0120.actual_execution
  | exact SourceHeightEdgesV1.Edge0121.actual_execution
  | exact SourceHeightEdgesV1.Edge0122.actual_execution
  | exact SourceHeightEdgesV1.Edge0123.actual_execution
  | exact SourceHeightEdgesV1.Edge0124.actual_execution
  | exact SourceHeightEdgesV1.Edge0125.actual_execution
  | exact SourceHeightEdgesV1.Edge0126.actual_execution
  | exact SourceHeightEdgesV1.Edge0127.actual_execution
end SourceHeightEdgesV1.Block03
#print axioms SourceHeightEdgesV1.Block03.all
