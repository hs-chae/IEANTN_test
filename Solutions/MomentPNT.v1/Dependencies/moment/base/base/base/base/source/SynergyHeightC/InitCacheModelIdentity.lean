/- The candidate state is proof data, not an accepted source execution.
   This theorem only identifies its constant-array words with the existing
   mathematical model. The separate actual-source state check is mandatory. -/
import SynergyHeightC.InitCacheProposal
import SynergyAnalytic.HeightPointConstants
import SynergyC.SourceIntervalMath

namespace SynergyHeightC.InitCacheModelIdentity
open ScopedC ScopedC.Machine
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem proposed_constant_array (arena : NatArena.Arena) :
    (InitCacheProposal.postState arena).heap[13]? = some {
      type:="I"
      cells:=SynergyAnalytic.HeightPoint.constantValues.map
        (fun a => some (SynergyC.SourceIntervalMath.represented a))
      isArray:=true
      writable:=true} := by
  rfl

theorem proposed_heap_population (arena : NatArena.Arena) :
    (InitCacheProposal.postState arena).heap.length = 14 := by rfl

theorem proposed_constant_address (arena : NatArena.Arena) :
    Machine.getVar (InitCacheProposal.postState arena) "constantNodes" =
      some ⟨13,0,[]⟩ := by rfl

#print axioms proposed_constant_array
#print axioms proposed_heap_population
#print axioms proposed_constant_address
end SynergyHeightC.InitCacheModelIdentity
