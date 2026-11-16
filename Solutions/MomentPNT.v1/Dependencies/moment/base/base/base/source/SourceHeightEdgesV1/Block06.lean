import SourceHeightEdgesV1.Edge0192
import SourceHeightEdgesV1.Edge0193
import SourceHeightEdgesV1.Edge0194
import SourceHeightEdgesV1.Edge0195
import SourceHeightEdgesV1.Edge0196
import SourceHeightEdgesV1.Edge0197
import SourceHeightEdgesV1.Edge0198
import SourceHeightEdgesV1.Edge0199
import SourceHeightEdgesV1.Edge0200
import SourceHeightEdgesV1.Edge0201
import SourceHeightEdgesV1.Edge0202
import SourceHeightEdgesV1.Edge0203
import SourceHeightEdgesV1.Edge0204
import SourceHeightEdgesV1.Edge0205
import SourceHeightEdgesV1.Edge0206
import SourceHeightEdgesV1.Edge0207
import SourceHeightEdgesV1.Edge0208
import SourceHeightEdgesV1.Edge0209
import SourceHeightEdgesV1.Edge0210
import SourceHeightEdgesV1.Edge0211
import SourceHeightEdgesV1.Edge0212
import SourceHeightEdgesV1.Edge0213
import SourceHeightEdgesV1.Edge0214
import SourceHeightEdgesV1.Edge0215
import SourceHeightEdgesV1.Edge0216
import SourceHeightEdgesV1.Edge0217
import SourceHeightEdgesV1.Edge0218
import SourceHeightEdgesV1.Edge0219
import SourceHeightEdgesV1.Edge0220
import SourceHeightEdgesV1.Edge0221
import SourceHeightEdgesV1.Edge0222
import SourceHeightEdgesV1.Edge0223
namespace SourceHeightEdgesV1.Block06
open ScopedC ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem all (j : Nat) (hj : j<32) : SynergyHeightC.FullMainEdges.ExactEdges (32*6+j) := by
 interval_cases j <;> first
  | exact SourceHeightEdgesV1.Edge0192.actual_execution
  | exact SourceHeightEdgesV1.Edge0193.actual_execution
  | exact SourceHeightEdgesV1.Edge0194.actual_execution
  | exact SourceHeightEdgesV1.Edge0195.actual_execution
  | exact SourceHeightEdgesV1.Edge0196.actual_execution
  | exact SourceHeightEdgesV1.Edge0197.actual_execution
  | exact SourceHeightEdgesV1.Edge0198.actual_execution
  | exact SourceHeightEdgesV1.Edge0199.actual_execution
  | exact SourceHeightEdgesV1.Edge0200.actual_execution
  | exact SourceHeightEdgesV1.Edge0201.actual_execution
  | exact SourceHeightEdgesV1.Edge0202.actual_execution
  | exact SourceHeightEdgesV1.Edge0203.actual_execution
  | exact SourceHeightEdgesV1.Edge0204.actual_execution
  | exact SourceHeightEdgesV1.Edge0205.actual_execution
  | exact SourceHeightEdgesV1.Edge0206.actual_execution
  | exact SourceHeightEdgesV1.Edge0207.actual_execution
  | exact SourceHeightEdgesV1.Edge0208.actual_execution
  | exact SourceHeightEdgesV1.Edge0209.actual_execution
  | exact SourceHeightEdgesV1.Edge0210.actual_execution
  | exact SourceHeightEdgesV1.Edge0211.actual_execution
  | exact SourceHeightEdgesV1.Edge0212.actual_execution
  | exact SourceHeightEdgesV1.Edge0213.actual_execution
  | exact SourceHeightEdgesV1.Edge0214.actual_execution
  | exact SourceHeightEdgesV1.Edge0215.actual_execution
  | exact SourceHeightEdgesV1.Edge0216.actual_execution
  | exact SourceHeightEdgesV1.Edge0217.actual_execution
  | exact SourceHeightEdgesV1.Edge0218.actual_execution
  | exact SourceHeightEdgesV1.Edge0219.actual_execution
  | exact SourceHeightEdgesV1.Edge0220.actual_execution
  | exact SourceHeightEdgesV1.Edge0221.actual_execution
  | exact SourceHeightEdgesV1.Edge0222.actual_execution
  | exact SourceHeightEdgesV1.Edge0223.actual_execution
end SourceHeightEdgesV1.Block06
#print axioms SourceHeightEdgesV1.Block06.all
