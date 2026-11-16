/- Actual first-loop endpoint construction from the accepted main prefix. -/
import SynergyHeightC.FullMainEdge
namespace SynergyHeightC.FullMainEdge
open ScopedC ScopedC.Machine
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem checked_edges : checked=true := by decide +kernel

theorem actual_source_edges :
    Loops.SeqRun (ArraySourceCalls.Eval SynergyC.Header.layout FullMainPrefix.service)
      (ArraySourceCalls.Declare SynergyC.Header.layout FullMainPrefix.service) truth ArraySourceCalls.Scope
      statements FullMainPrefix.prefixState (.continuing afterRight) := edges_of_checked checked_edges

#print axioms checked_edges
#print axioms actual_source_edges
end SynergyHeightC.FullMainEdge
