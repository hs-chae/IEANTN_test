import SourceHeightEdgesV1.Edge0032
import SourceHeightEdgesV1.Edge0033
import SourceHeightEdgesV1.Edge0034
import SourceHeightEdgesV1.Edge0035
import SourceHeightEdgesV1.Edge0036
import SourceHeightEdgesV1.Edge0037
import SourceHeightEdgesV1.Edge0038
import SourceHeightEdgesV1.Edge0039
import SourceHeightEdgesV1.Edge0040
import SourceHeightEdgesV1.Edge0041
import SourceHeightEdgesV1.Edge0042
import SourceHeightEdgesV1.Edge0043
import SourceHeightEdgesV1.Edge0044
import SourceHeightEdgesV1.Edge0045
import SourceHeightEdgesV1.Edge0046
import SourceHeightEdgesV1.Edge0047
import SourceHeightEdgesV1.Edge0048
import SourceHeightEdgesV1.Edge0049
import SourceHeightEdgesV1.Edge0050
import SourceHeightEdgesV1.Edge0051
import SourceHeightEdgesV1.Edge0052
import SourceHeightEdgesV1.Edge0053
import SourceHeightEdgesV1.Edge0054
import SourceHeightEdgesV1.Edge0055
import SourceHeightEdgesV1.Edge0056
import SourceHeightEdgesV1.Edge0057
import SourceHeightEdgesV1.Edge0058
import SourceHeightEdgesV1.Edge0059
import SourceHeightEdgesV1.Edge0060
import SourceHeightEdgesV1.Edge0061
import SourceHeightEdgesV1.Edge0062
import SourceHeightEdgesV1.Edge0063
namespace SourceHeightEdgesV1.Block01
open ScopedC ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem all (j : Nat) (hj : j<32) : SynergyHeightC.FullMainEdges.ExactEdges (32*1+j) := by
 interval_cases j <;> first
  | exact SourceHeightEdgesV1.Edge0032.actual_execution
  | exact SourceHeightEdgesV1.Edge0033.actual_execution
  | exact SourceHeightEdgesV1.Edge0034.actual_execution
  | exact SourceHeightEdgesV1.Edge0035.actual_execution
  | exact SourceHeightEdgesV1.Edge0036.actual_execution
  | exact SourceHeightEdgesV1.Edge0037.actual_execution
  | exact SourceHeightEdgesV1.Edge0038.actual_execution
  | exact SourceHeightEdgesV1.Edge0039.actual_execution
  | exact SourceHeightEdgesV1.Edge0040.actual_execution
  | exact SourceHeightEdgesV1.Edge0041.actual_execution
  | exact SourceHeightEdgesV1.Edge0042.actual_execution
  | exact SourceHeightEdgesV1.Edge0043.actual_execution
  | exact SourceHeightEdgesV1.Edge0044.actual_execution
  | exact SourceHeightEdgesV1.Edge0045.actual_execution
  | exact SourceHeightEdgesV1.Edge0046.actual_execution
  | exact SourceHeightEdgesV1.Edge0047.actual_execution
  | exact SourceHeightEdgesV1.Edge0048.actual_execution
  | exact SourceHeightEdgesV1.Edge0049.actual_execution
  | exact SourceHeightEdgesV1.Edge0050.actual_execution
  | exact SourceHeightEdgesV1.Edge0051.actual_execution
  | exact SourceHeightEdgesV1.Edge0052.actual_execution
  | exact SourceHeightEdgesV1.Edge0053.actual_execution
  | exact SourceHeightEdgesV1.Edge0054.actual_execution
  | exact SourceHeightEdgesV1.Edge0055.actual_execution
  | exact SourceHeightEdgesV1.Edge0056.actual_execution
  | exact SourceHeightEdgesV1.Edge0057.actual_execution
  | exact SourceHeightEdgesV1.Edge0058.actual_execution
  | exact SourceHeightEdgesV1.Edge0059.actual_execution
  | exact SourceHeightEdgesV1.Edge0060.actual_execution
  | exact SourceHeightEdgesV1.Edge0061.actual_execution
  | exact SourceHeightEdgesV1.Edge0062.actual_execution
  | exact SourceHeightEdgesV1.Edge0063.actual_execution
end SourceHeightEdgesV1.Block01
#print axioms SourceHeightEdgesV1.Block01.all
