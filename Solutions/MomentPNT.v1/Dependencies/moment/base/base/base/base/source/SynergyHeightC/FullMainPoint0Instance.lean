/- Complete actual source point evaluation in the first actual main frame. -/
import SynergyHeightC.FullMainPoint0
namespace SynergyHeightC.FullMainPoint0
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem checked_source_main_point : checked=true := by decide +kernel

theorem actual_source_main_point :
    ∃ c d, PointExecuteAPI.modelOutputs FullMainEdge.right=some (c,d) ∧
      PointExecuteAPI.SourcePointOutputs FullMainEdge.afterRight FullMainEdge.right c d :=
  source_outputs_of_checked checked_source_main_point

#print axioms checked_source_main_point
#print axioms actual_source_main_point
end SynergyHeightC.FullMainPoint0
