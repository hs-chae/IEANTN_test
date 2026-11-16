import SourceHeightEdgesV1.Edge0128
import SourceHeightEdgesV1.Edge0129
import SourceHeightEdgesV1.Edge0130
import SourceHeightEdgesV1.Edge0131
import SourceHeightEdgesV1.Edge0132
import SourceHeightEdgesV1.Edge0133
import SourceHeightEdgesV1.Edge0134
import SourceHeightEdgesV1.Edge0135
import SourceHeightEdgesV1.Edge0136
import SourceHeightEdgesV1.Edge0137
import SourceHeightEdgesV1.Edge0138
import SourceHeightEdgesV1.Edge0139
import SourceHeightEdgesV1.Edge0140
import SourceHeightEdgesV1.Edge0141
import SourceHeightEdgesV1.Edge0142
import SourceHeightEdgesV1.Edge0143
import SourceHeightEdgesV1.Edge0144
import SourceHeightEdgesV1.Edge0145
import SourceHeightEdgesV1.Edge0146
import SourceHeightEdgesV1.Edge0147
import SourceHeightEdgesV1.Edge0148
import SourceHeightEdgesV1.Edge0149
import SourceHeightEdgesV1.Edge0150
import SourceHeightEdgesV1.Edge0151
import SourceHeightEdgesV1.Edge0152
import SourceHeightEdgesV1.Edge0153
import SourceHeightEdgesV1.Edge0154
import SourceHeightEdgesV1.Edge0155
import SourceHeightEdgesV1.Edge0156
import SourceHeightEdgesV1.Edge0157
import SourceHeightEdgesV1.Edge0158
import SourceHeightEdgesV1.Edge0159
namespace SourceHeightEdgesV1.Block04
open ScopedC ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem all (j : Nat) (hj : j<32) : SynergyHeightC.FullMainEdges.ExactEdges (32*4+j) := by
 interval_cases j <;> first
  | exact SourceHeightEdgesV1.Edge0128.actual_execution
  | exact SourceHeightEdgesV1.Edge0129.actual_execution
  | exact SourceHeightEdgesV1.Edge0130.actual_execution
  | exact SourceHeightEdgesV1.Edge0131.actual_execution
  | exact SourceHeightEdgesV1.Edge0132.actual_execution
  | exact SourceHeightEdgesV1.Edge0133.actual_execution
  | exact SourceHeightEdgesV1.Edge0134.actual_execution
  | exact SourceHeightEdgesV1.Edge0135.actual_execution
  | exact SourceHeightEdgesV1.Edge0136.actual_execution
  | exact SourceHeightEdgesV1.Edge0137.actual_execution
  | exact SourceHeightEdgesV1.Edge0138.actual_execution
  | exact SourceHeightEdgesV1.Edge0139.actual_execution
  | exact SourceHeightEdgesV1.Edge0140.actual_execution
  | exact SourceHeightEdgesV1.Edge0141.actual_execution
  | exact SourceHeightEdgesV1.Edge0142.actual_execution
  | exact SourceHeightEdgesV1.Edge0143.actual_execution
  | exact SourceHeightEdgesV1.Edge0144.actual_execution
  | exact SourceHeightEdgesV1.Edge0145.actual_execution
  | exact SourceHeightEdgesV1.Edge0146.actual_execution
  | exact SourceHeightEdgesV1.Edge0147.actual_execution
  | exact SourceHeightEdgesV1.Edge0148.actual_execution
  | exact SourceHeightEdgesV1.Edge0149.actual_execution
  | exact SourceHeightEdgesV1.Edge0150.actual_execution
  | exact SourceHeightEdgesV1.Edge0151.actual_execution
  | exact SourceHeightEdgesV1.Edge0152.actual_execution
  | exact SourceHeightEdgesV1.Edge0153.actual_execution
  | exact SourceHeightEdgesV1.Edge0154.actual_execution
  | exact SourceHeightEdgesV1.Edge0155.actual_execution
  | exact SourceHeightEdgesV1.Edge0156.actual_execution
  | exact SourceHeightEdgesV1.Edge0157.actual_execution
  | exact SourceHeightEdgesV1.Edge0158.actual_execution
  | exact SourceHeightEdgesV1.Edge0159.actual_execution
end SourceHeightEdgesV1.Block04
#print axioms SourceHeightEdgesV1.Block04.all
