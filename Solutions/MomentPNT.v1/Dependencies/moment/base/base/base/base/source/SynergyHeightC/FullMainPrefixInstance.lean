/- Exact first five declarations after source-verified initialization.
The source main, source algorithms, and local-variable lifetime stay unchanged. -/
import SynergyHeightC.FullMainPrefix
namespace SynergyHeightC.FullMainPrefix
open ScopedC ScopedC.Machine
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem checked_prefix : checked = true := by decide +kernel

theorem actual_source_prefix :
    Loops.SeqRun (ArraySourceCalls.Eval SynergyC.Header.layout service)
      (ArraySourceCalls.Declare SynergyC.Header.layout service) truth ArraySourceCalls.Scope
      statements cache (.continuing prefixState) := prefix_of_checked checked_prefix

#print axioms checked_prefix
#print axioms actual_source_prefix
end SynergyHeightC.FullMainPrefix
