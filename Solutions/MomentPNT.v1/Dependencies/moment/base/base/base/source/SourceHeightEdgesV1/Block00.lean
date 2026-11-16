import SourceHeightEdgesV1.Edge0000
import SourceHeightEdgesV1.Edge0001
import SourceHeightEdgesV1.Edge0002
import SourceHeightEdgesV1.Edge0003
import SourceHeightEdgesV1.Edge0004
import SourceHeightEdgesV1.Edge0005
import SourceHeightEdgesV1.Edge0006
import SourceHeightEdgesV1.Edge0007
import SourceHeightEdgesV1.Edge0008
import SourceHeightEdgesV1.Edge0009
import SourceHeightEdgesV1.Edge0010
import SourceHeightEdgesV1.Edge0011
import SourceHeightEdgesV1.Edge0012
import SourceHeightEdgesV1.Edge0013
import SourceHeightEdgesV1.Edge0014
import SourceHeightEdgesV1.Edge0015
import SourceHeightEdgesV1.Edge0016
import SourceHeightEdgesV1.Edge0017
import SourceHeightEdgesV1.Edge0018
import SourceHeightEdgesV1.Edge0019
import SourceHeightEdgesV1.Edge0020
import SourceHeightEdgesV1.Edge0021
import SourceHeightEdgesV1.Edge0022
import SourceHeightEdgesV1.Edge0023
import SourceHeightEdgesV1.Edge0024
import SourceHeightEdgesV1.Edge0025
import SourceHeightEdgesV1.Edge0026
import SourceHeightEdgesV1.Edge0027
import SourceHeightEdgesV1.Edge0028
import SourceHeightEdgesV1.Edge0029
import SourceHeightEdgesV1.Edge0030
import SourceHeightEdgesV1.Edge0031
namespace SourceHeightEdgesV1.Block00
open ScopedC ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem all (j : Nat) (hj : j<32) : SynergyHeightC.FullMainEdges.ExactEdges (32*0+j) := by
 interval_cases j <;> first
  | exact SourceHeightEdgesV1.Edge0000.actual_execution
  | exact SourceHeightEdgesV1.Edge0001.actual_execution
  | exact SourceHeightEdgesV1.Edge0002.actual_execution
  | exact SourceHeightEdgesV1.Edge0003.actual_execution
  | exact SourceHeightEdgesV1.Edge0004.actual_execution
  | exact SourceHeightEdgesV1.Edge0005.actual_execution
  | exact SourceHeightEdgesV1.Edge0006.actual_execution
  | exact SourceHeightEdgesV1.Edge0007.actual_execution
  | exact SourceHeightEdgesV1.Edge0008.actual_execution
  | exact SourceHeightEdgesV1.Edge0009.actual_execution
  | exact SourceHeightEdgesV1.Edge0010.actual_execution
  | exact SourceHeightEdgesV1.Edge0011.actual_execution
  | exact SourceHeightEdgesV1.Edge0012.actual_execution
  | exact SourceHeightEdgesV1.Edge0013.actual_execution
  | exact SourceHeightEdgesV1.Edge0014.actual_execution
  | exact SourceHeightEdgesV1.Edge0015.actual_execution
  | exact SourceHeightEdgesV1.Edge0016.actual_execution
  | exact SourceHeightEdgesV1.Edge0017.actual_execution
  | exact SourceHeightEdgesV1.Edge0018.actual_execution
  | exact SourceHeightEdgesV1.Edge0019.actual_execution
  | exact SourceHeightEdgesV1.Edge0020.actual_execution
  | exact SourceHeightEdgesV1.Edge0021.actual_execution
  | exact SourceHeightEdgesV1.Edge0022.actual_execution
  | exact SourceHeightEdgesV1.Edge0023.actual_execution
  | exact SourceHeightEdgesV1.Edge0024.actual_execution
  | exact SourceHeightEdgesV1.Edge0025.actual_execution
  | exact SourceHeightEdgesV1.Edge0026.actual_execution
  | exact SourceHeightEdgesV1.Edge0027.actual_execution
  | exact SourceHeightEdgesV1.Edge0028.actual_execution
  | exact SourceHeightEdgesV1.Edge0029.actual_execution
  | exact SourceHeightEdgesV1.Edge0030.actual_execution
  | exact SourceHeightEdgesV1.Edge0031.actual_execution
end SourceHeightEdgesV1.Block00
#print axioms SourceHeightEdgesV1.Block00.all
