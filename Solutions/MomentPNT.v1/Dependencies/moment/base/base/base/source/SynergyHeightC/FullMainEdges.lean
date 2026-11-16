/- Actual source endpoint construction in every selected main-loop frame.
This interface supplies no execution result until a finite proof is provided. -/
import SynergyHeightC.FullMainFrame
namespace SynergyHeightC.FullMainEdges
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def loopState (total : ProofBox) (i : Nat) : State :=
  allocate (allocate FullMainPrefix.afterSpan "I" "total"
    (some (SynergyC.SourceIntervalMath.represented total)))
    "unsigned int" "i" (some (FullMainPrefix.unsigned32 i))

@[irreducible] def run (total : ProofBox) (i : Nat) : Option ArraySourceExecute.Outcome :=
  ArraySourceExecute.statements SynergyC.Header.layout FullMainPrefix.service 128 2048
    FullMainEdge.statements (loopState total i)

def ExactEdges (i : Nat) : Prop := ∀ total : ProofBox,
  run total i=some (.continuing (FullMainFrame.base total i))

theorem first_loop_state : loopState ⟨0,0⟩ 0=FullMainPrefix.prefixState := by rfl

theorem actual_source_edges {i : Nat} (h : ExactEdges i) (total : ProofBox) :
    Loops.SeqRun (ArraySourceCalls.Eval SynergyC.Header.layout FullMainPrefix.service)
      (ArraySourceCalls.Declare SynergyC.Header.layout FullMainPrefix.service) truth ArraySourceCalls.Scope
      FullMainEdge.statements (loopState total i) (.continuing (FullMainFrame.base total i)) := by
  have run_eq : run total i=ArraySourceExecute.statements SynergyC.Header.layout FullMainPrefix.service
      128 2048 FullMainEdge.statements (loopState total i) := by unfold run; rfl
  have exec := Eq.mp (congrArg (fun r=>r=some (.continuing (FullMainFrame.base total i))) run_eq) (h total)
  exact (ArraySourceExecute.sound SynergyC.Header.layout FullMainPrefix.service 128 2048).2.1
    FullMainEdge.statements (loopState total i) (.continuing (FullMainFrame.base total i)) exec

#print axioms first_loop_state
#print axioms actual_source_edges
end SynergyHeightC.FullMainEdges
