/- Actual source pointHeight call at the first main-loop frame. This is a
new fixed-input source proof, not transport of a bare-cache certificate. -/
import SynergyHeightC.FullMainEdgeInstance
namespace SynergyHeightC.FullMainPoint0
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def checked : Bool := FullContractPointExecute.checkedModel FullMainEdge.afterRight FullMainEdge.right

theorem actual_buffers : PointExecuteAPI.cAddress FullMainEdge.afterRight = ⟨21,0,[]⟩ ∧
    PointExecuteAPI.dAddress FullMainEdge.afterRight = ⟨22,0,[]⟩ := by constructor <;> rfl

theorem source_outputs_of_checked (h : checked=true) :
    ∃ c d, PointExecuteAPI.modelOutputs FullMainEdge.right=some (c,d) ∧
      PointExecuteAPI.SourcePointOutputs FullMainEdge.afterRight FullMainEdge.right c d :=
  FullContractPointExecute.source_outputs_of_checkedModel h

#print axioms actual_buffers
#print axioms source_outputs_of_checked
end SynergyHeightC.FullMainPoint0
