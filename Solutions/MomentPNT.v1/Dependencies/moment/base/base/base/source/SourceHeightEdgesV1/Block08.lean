import SourceHeightEdgesV1.Edge0256
import SourceHeightEdgesV1.Edge0257
import SourceHeightEdgesV1.Edge0258
import SourceHeightEdgesV1.Edge0259
import SourceHeightEdgesV1.Edge0260
import SourceHeightEdgesV1.Edge0261
import SourceHeightEdgesV1.Edge0262
import SourceHeightEdgesV1.Edge0263
import SourceHeightEdgesV1.Edge0264
import SourceHeightEdgesV1.Edge0265
import SourceHeightEdgesV1.Edge0266
import SourceHeightEdgesV1.Edge0267
import SourceHeightEdgesV1.Edge0268
import SourceHeightEdgesV1.Edge0269
import SourceHeightEdgesV1.Edge0270
import SourceHeightEdgesV1.Edge0271
import SourceHeightEdgesV1.Edge0272
import SourceHeightEdgesV1.Edge0273
import SourceHeightEdgesV1.Edge0274
import SourceHeightEdgesV1.Edge0275
import SourceHeightEdgesV1.Edge0276
import SourceHeightEdgesV1.Edge0277
import SourceHeightEdgesV1.Edge0278
import SourceHeightEdgesV1.Edge0279
import SourceHeightEdgesV1.Edge0280
import SourceHeightEdgesV1.Edge0281
import SourceHeightEdgesV1.Edge0282
import SourceHeightEdgesV1.Edge0283
import SourceHeightEdgesV1.Edge0284
import SourceHeightEdgesV1.Edge0285
import SourceHeightEdgesV1.Edge0286
import SourceHeightEdgesV1.Edge0287
namespace SourceHeightEdgesV1.Block08
open ScopedC ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem all (j : Nat) (hj : j<32) : SynergyHeightC.FullMainEdges.ExactEdges (32*8+j) := by
 interval_cases j <;> first
  | exact SourceHeightEdgesV1.Edge0256.actual_execution
  | exact SourceHeightEdgesV1.Edge0257.actual_execution
  | exact SourceHeightEdgesV1.Edge0258.actual_execution
  | exact SourceHeightEdgesV1.Edge0259.actual_execution
  | exact SourceHeightEdgesV1.Edge0260.actual_execution
  | exact SourceHeightEdgesV1.Edge0261.actual_execution
  | exact SourceHeightEdgesV1.Edge0262.actual_execution
  | exact SourceHeightEdgesV1.Edge0263.actual_execution
  | exact SourceHeightEdgesV1.Edge0264.actual_execution
  | exact SourceHeightEdgesV1.Edge0265.actual_execution
  | exact SourceHeightEdgesV1.Edge0266.actual_execution
  | exact SourceHeightEdgesV1.Edge0267.actual_execution
  | exact SourceHeightEdgesV1.Edge0268.actual_execution
  | exact SourceHeightEdgesV1.Edge0269.actual_execution
  | exact SourceHeightEdgesV1.Edge0270.actual_execution
  | exact SourceHeightEdgesV1.Edge0271.actual_execution
  | exact SourceHeightEdgesV1.Edge0272.actual_execution
  | exact SourceHeightEdgesV1.Edge0273.actual_execution
  | exact SourceHeightEdgesV1.Edge0274.actual_execution
  | exact SourceHeightEdgesV1.Edge0275.actual_execution
  | exact SourceHeightEdgesV1.Edge0276.actual_execution
  | exact SourceHeightEdgesV1.Edge0277.actual_execution
  | exact SourceHeightEdgesV1.Edge0278.actual_execution
  | exact SourceHeightEdgesV1.Edge0279.actual_execution
  | exact SourceHeightEdgesV1.Edge0280.actual_execution
  | exact SourceHeightEdgesV1.Edge0281.actual_execution
  | exact SourceHeightEdgesV1.Edge0282.actual_execution
  | exact SourceHeightEdgesV1.Edge0283.actual_execution
  | exact SourceHeightEdgesV1.Edge0284.actual_execution
  | exact SourceHeightEdgesV1.Edge0285.actual_execution
  | exact SourceHeightEdgesV1.Edge0286.actual_execution
  | exact SourceHeightEdgesV1.Edge0287.actual_execution
end SourceHeightEdgesV1.Block08
#print axioms SourceHeightEdgesV1.Block08.all
