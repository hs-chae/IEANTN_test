/- Complete actual fixed initializer, using only already verified C contracts.
No application cache, returned arena or numerical output is assumed. -/
import SynergyHeightC.FullContractInit
namespace SynergyHeightC.FullContractInit
open ScopedC ScopedC.Machine
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem checked_init : checked = true := by decide +kernel

theorem actual_source_init_empty :
    ArraySourceCalls.SourceCall SynergyC.Header.layout Bundle.code 16
      "initializePointConstants" [] Initialization.state .unit
      (InitCacheProposal.postState NatArena.empty) :=
  source_empty_of_checked checked_init

#print axioms checked_init
#print axioms actual_source_init_empty
end SynergyHeightC.FullContractInit
