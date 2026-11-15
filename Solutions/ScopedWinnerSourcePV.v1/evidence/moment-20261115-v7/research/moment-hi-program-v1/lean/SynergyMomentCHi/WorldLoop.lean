/- Full high-only moment while, composed from actual body execution proofs.
The totals is proof metadata: this generic theorem supplies no numerical
value or successful application execution. Every row premise must be proved
before a concrete program theorem can use it. -/
import SynergyMomentCHi.WorldIteration
import SynergyHeightC.MainWorldGuard

namespace SynergyMomentCHi.WorldLoop
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedNumerical SynergyHeightC SynergyMomentC
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 100000

abbrev RowRun (kind : Kind) (platform : ScopedIO.WorldIO.Platform)
    (fault : ScopedIO.WorldIO.FaultPolicy) (totals : Nat → ProofBox)
    (streams : Nat → ScopedIO.Stream) (i : Nat) : Prop :=
  ScopedIO.WorldSource.Run SynergyC.Header.layout FullMainPrefix.service
    (EmitUService.call platform fault) platform (.sequence (loopStatements kind))
    ⟨FullMainEdges.loopState (totals i) i,streams i⟩
    (.continuing ⟨FullMainEdges.loopState (totals (i+1)) (i+1),streams (i+1)⟩)

theorem while_suffix (kind : Kind) (platform : ScopedIO.WorldIO.Platform)
    (fault : ScopedIO.WorldIO.FaultPolicy) (totals : Nat → ProofBox)
    (streams : Nat → ScopedIO.Stream)
    (rows : ∀ i,i<768 → RowRun kind platform fault totals streams i)
    (remaining i : Nat) (endpoint : i+remaining=768) :
    Loops.WhileRun
      (ScopedIO.WorldSource.Eval SynergyC.Header.layout FullMainPrefix.service
        (EmitUService.call platform fault) platform)
      (ScopedIO.WorldSource.Declare SynergyC.Header.layout FullMainPrefix.service)
      truth ScopedIO.WorldSource.Scope MainWorldGuard.guard (.sequence (loopStatements kind))
      ⟨FullMainEdges.loopState (totals i) i,streams i⟩
      (.continuing ⟨FullMainEdges.loopState (totals 768) 768,streams 768⟩) := by
  induction remaining generalizing i with
  | zero =>
    have last : i=768 := by omega
    subst i
    exact Loops.WhileRun.done
      (MainWorldGuard.world_guard (EmitUService.call platform fault) platform
        (streams 768) (totals 768) 768 (by decide)) (by decide)
  | succ remaining ih =>
    have hi : i<768 := by omega
    exact Loops.WhileRun.next
      (MainWorldGuard.world_guard (EmitUService.call platform fault) platform
        (streams i) (totals i) i (by omega))
      (by have truthBoolean (b : Bool) :
            truth (Machine.boolean SynergyC.Header.layout b)=b := by cases b <;> rfl
          rw [truthBoolean]
          exact decide_eq_true hi)
      (rows i hi) (ih (i+1) (by omega))

theorem actual_while (kind : Kind) (platform : ScopedIO.WorldIO.Platform)
    (fault : ScopedIO.WorldIO.FaultPolicy) (totals : Nat → ProofBox)
    (streams : Nat → ScopedIO.Stream)
    (rows : ∀ i,i<768 → RowRun kind platform fault totals streams i) :
    ScopedIO.WorldSource.Run SynergyC.Header.layout FullMainPrefix.service
      (EmitUService.call platform fault) platform
      (.whileLoop MainWorldGuard.guard (.sequence (loopStatements kind)))
      ⟨FullMainEdges.loopState (totals 0) 0,streams 0⟩
      (.continuing ⟨FullMainEdges.loopState (totals 768) 768,streams 768⟩) :=
  Loops.StmtRun.whileLoop (while_suffix kind platform fault totals streams rows 768 0 rfl)

#print axioms while_suffix
#print axioms actual_while
end SynergyMomentCHi.WorldLoop
