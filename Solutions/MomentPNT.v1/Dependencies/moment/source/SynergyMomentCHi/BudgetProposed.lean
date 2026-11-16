/- Additive proposed-state consumer; all previous source budget objects stay unchanged. -/
import SynergyMomentCHi.Budget
namespace SynergyMomentCHi.BudgetProposed
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedNumerical SynergyMomentC Budget
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000
def afterProposed (total next : ProofBox) (i : Nat) (c d : ProofBox) : State :=
 storeInterval (afterW total i c d) 17 next

theorem source_of_proposed_execution {kind : Kind} {total next c d : ProofBox} {i : Nat}
 (execution : run kind total i c d=some (.continuing (afterProposed total next i c d))) :
 Loops.SeqRun (ArraySourceCalls.Eval SynergyC.Header.layout SynergyHeightC.FullMainPrefix.service)
   (ArraySourceCalls.Declare SynergyC.Header.layout SynergyHeightC.FullMainPrefix.service)
   truth ArraySourceCalls.Scope (Budget.statements kind) (before total i c d)
   (.continuing (afterProposed total next i c d)) := by
 have eq : run kind total i c d=ArraySourceExecute.statements SynergyC.Header.layout
     SynergyHeightC.FullMainPrefix.service 128 2048 (Budget.statements kind) (before total i c d) := by
   unfold run
   rfl
 have actual:=Eq.mp (congrArg (fun result=>result=some
   (.continuing (afterProposed total next i c d))) eq) execution
 exact (ArraySourceExecute.sound SynergyC.Header.layout SynergyHeightC.FullMainPrefix.service
   128 2048).2.1 (Budget.statements kind) (before total i c d)
     (.continuing (afterProposed total next i c d)) actual


#print axioms source_of_proposed_execution
end SynergyMomentCHi.BudgetProposed
