/- The actual main-loop caller frame, with only the accumulated total and
loop index varying. These are states, not assumed source executions. -/
import SynergyHeightC.FullMainEdgeInstance
namespace SynergyHeightC.FullMainFrame
open ScopedC ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def throughLeft (total : ProofBox) (i : Nat) : State :=
  allocate (allocate (allocate FullMainPrefix.afterSpan "I" "total"
    (some (SynergyC.SourceIntervalMath.represented total)))
    "unsigned int" "i" (some (FullMainPrefix.unsigned32 i)))
    "I" "left" (some (SynergyC.SourceIntervalMath.represented
      ((SynergyAnalytic.HeightPoint.logCell i).getD ⟨0,0⟩)))
def base (total : ProofBox) (i : Nat) : State :=
  allocate (throughLeft total i) "I" "right" (some (SynergyC.SourceIntervalMath.represented
    ((SynergyAnalytic.HeightPoint.logCell (i+1)).getD ⟨0,0⟩)))

theorem first_base : base ⟨0,0⟩ 0 = FullMainEdge.afterRight := by rfl

theorem base_heap_length (total : ProofBox) (i : Nat) : (base total i).heap.length=21 := by rfl

theorem actual_buffer_addresses (total : ProofBox) (i : Nat) :
    PointExecuteAPI.cAddress (base total i)=⟨21,0,[]⟩ ∧
      PointExecuteAPI.dAddress (base total i)=⟨22,0,[]⟩ := by constructor <;> rfl

theorem total_address (total : ProofBox) (i : Nat) :
    Machine.getVar (base total i) "total"=some ⟨17,0,[]⟩ := by rfl

#print axioms first_base
#print axioms actual_buffer_addresses
#print axioms total_address
end SynergyHeightC.FullMainFrame
