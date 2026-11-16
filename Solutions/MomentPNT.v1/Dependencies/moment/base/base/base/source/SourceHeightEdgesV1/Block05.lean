import SourceHeightEdgesV1.Edge0160
import SourceHeightEdgesV1.Edge0161
import SourceHeightEdgesV1.Edge0162
import SourceHeightEdgesV1.Edge0163
import SourceHeightEdgesV1.Edge0164
import SourceHeightEdgesV1.Edge0165
import SourceHeightEdgesV1.Edge0166
import SourceHeightEdgesV1.Edge0167
import SourceHeightEdgesV1.Edge0168
import SourceHeightEdgesV1.Edge0169
import SourceHeightEdgesV1.Edge0170
import SourceHeightEdgesV1.Edge0171
import SourceHeightEdgesV1.Edge0172
import SourceHeightEdgesV1.Edge0173
import SourceHeightEdgesV1.Edge0174
import SourceHeightEdgesV1.Edge0175
import SourceHeightEdgesV1.Edge0176
import SourceHeightEdgesV1.Edge0177
import SourceHeightEdgesV1.Edge0178
import SourceHeightEdgesV1.Edge0179
import SourceHeightEdgesV1.Edge0180
import SourceHeightEdgesV1.Edge0181
import SourceHeightEdgesV1.Edge0182
import SourceHeightEdgesV1.Edge0183
import SourceHeightEdgesV1.Edge0184
import SourceHeightEdgesV1.Edge0185
import SourceHeightEdgesV1.Edge0186
import SourceHeightEdgesV1.Edge0187
import SourceHeightEdgesV1.Edge0188
import SourceHeightEdgesV1.Edge0189
import SourceHeightEdgesV1.Edge0190
import SourceHeightEdgesV1.Edge0191
namespace SourceHeightEdgesV1.Block05
open ScopedC ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem all (j : Nat) (hj : j<32) : SynergyHeightC.FullMainEdges.ExactEdges (32*5+j) := by
 interval_cases j <;> first
  | exact SourceHeightEdgesV1.Edge0160.actual_execution
  | exact SourceHeightEdgesV1.Edge0161.actual_execution
  | exact SourceHeightEdgesV1.Edge0162.actual_execution
  | exact SourceHeightEdgesV1.Edge0163.actual_execution
  | exact SourceHeightEdgesV1.Edge0164.actual_execution
  | exact SourceHeightEdgesV1.Edge0165.actual_execution
  | exact SourceHeightEdgesV1.Edge0166.actual_execution
  | exact SourceHeightEdgesV1.Edge0167.actual_execution
  | exact SourceHeightEdgesV1.Edge0168.actual_execution
  | exact SourceHeightEdgesV1.Edge0169.actual_execution
  | exact SourceHeightEdgesV1.Edge0170.actual_execution
  | exact SourceHeightEdgesV1.Edge0171.actual_execution
  | exact SourceHeightEdgesV1.Edge0172.actual_execution
  | exact SourceHeightEdgesV1.Edge0173.actual_execution
  | exact SourceHeightEdgesV1.Edge0174.actual_execution
  | exact SourceHeightEdgesV1.Edge0175.actual_execution
  | exact SourceHeightEdgesV1.Edge0176.actual_execution
  | exact SourceHeightEdgesV1.Edge0177.actual_execution
  | exact SourceHeightEdgesV1.Edge0178.actual_execution
  | exact SourceHeightEdgesV1.Edge0179.actual_execution
  | exact SourceHeightEdgesV1.Edge0180.actual_execution
  | exact SourceHeightEdgesV1.Edge0181.actual_execution
  | exact SourceHeightEdgesV1.Edge0182.actual_execution
  | exact SourceHeightEdgesV1.Edge0183.actual_execution
  | exact SourceHeightEdgesV1.Edge0184.actual_execution
  | exact SourceHeightEdgesV1.Edge0185.actual_execution
  | exact SourceHeightEdgesV1.Edge0186.actual_execution
  | exact SourceHeightEdgesV1.Edge0187.actual_execution
  | exact SourceHeightEdgesV1.Edge0188.actual_execution
  | exact SourceHeightEdgesV1.Edge0189.actual_execution
  | exact SourceHeightEdgesV1.Edge0190.actual_execution
  | exact SourceHeightEdgesV1.Edge0191.actual_execution
end SourceHeightEdgesV1.Block05
#print axioms SourceHeightEdgesV1.Block05.all
