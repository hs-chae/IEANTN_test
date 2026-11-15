/- Actual whole 768-cell C while loop, conditional only on its checked I/O trace.
Every point, endpoint and numerical source execution is already discharged. -/
import SynergyHeightC.MainWorldAllIterations
namespace SynergyHeightC.MainWorldLoop
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 100000

abbrev RowRun (platform : ScopedIO.WorldIO.Platform) (fault : ScopedIO.WorldIO.FaultPolicy)
    (streams : Nat → ScopedIO.Stream) (i : Nat) : Prop :=
  ScopedIO.WorldSource.Run SynergyC.Header.layout FullMainPrefix.service
    (EmitUService.call platform fault) platform (.sequence PointExecuteAPI.loopStatements)
    ⟨FullMainEdges.loopState (SourceMainBudgetV1.Data.total i) i,streams i⟩
    (.continuing ⟨FullMainEdges.loopState (SourceMainBudgetV1.Data.total (i+1)) (i+1),streams (i+1)⟩)

/-- This condition records actual successful checked emitter calls, not an
application-result or numerical-success assumption. Failed/partial I/O remains
possible and does not satisfy this normal-path condition. -/
def CheckedRowCalls (platform : ScopedIO.WorldIO.Platform)
    (fault : ScopedIO.WorldIO.FaultPolicy) (streams : Nat → ScopedIO.Stream) : Prop :=
  ∀ i, i < 768 → ∃ c d middle after,
    PointExecuteAPI.modelOutputs (MainInputPointComposition.input i)=some (c,d) ∧
    EmitUService.call platform fault "emitU" [SynergyC.Word512.value (MainWeightModel.adjustedC c).hi]
      ⟨MainBudgetExecute.afterBudget (SourceMainBudgetV1.Data.total i) i c d,streams i⟩=
      some (.unit,middle) ∧
    EmitUService.call platform fault "emitU" [SynergyC.Word512.value d.hi]
      middle=some (.unit,after) ∧ after.stream=streams (i+1)

theorem rows_of_checked_calls (platform : ScopedIO.WorldIO.Platform)
    (fault : ScopedIO.WorldIO.FaultPolicy) (streams : Nat → ScopedIO.Stream)
    (checked : CheckedRowCalls platform fault streams) :
    ∀ i, i < 768 → RowRun platform fault streams i := by
  intro i hi
  obtain ⟨c,d,model,body⟩ := MainWorldAllIterations.actual_rows i hi
  obtain ⟨actualC,actualD,middle,after,actualModel,first,second,state⟩ := checked i hi
  have pair : (actualC,actualD)=(c,d) := Option.some.inj (actualModel.symm.trans model)
  have ceq : actualC=c := congrArg Prod.fst pair
  have deq : actualD=d := congrArg Prod.snd pair
  subst actualC
  subst actualD
  have result := (body platform fault (streams i) middle after first second).1
  rw [state] at result
  exact result

theorem while_suffix (platform : ScopedIO.WorldIO.Platform)
    (fault : ScopedIO.WorldIO.FaultPolicy) (streams : Nat → ScopedIO.Stream)
    (rows : ∀ i, i < 768 → RowRun platform fault streams i)
    (remaining i : Nat) (endpoint : i+remaining=768) :
    Loops.WhileRun
      (ScopedIO.WorldSource.Eval SynergyC.Header.layout FullMainPrefix.service
        (EmitUService.call platform fault) platform)
      (ScopedIO.WorldSource.Declare SynergyC.Header.layout FullMainPrefix.service)
      truth ScopedIO.WorldSource.Scope MainWorldGuard.guard
      (.sequence PointExecuteAPI.loopStatements)
      ⟨FullMainEdges.loopState (SourceMainBudgetV1.Data.total i) i,streams i⟩
      (.continuing ⟨FullMainEdges.loopState (SourceMainBudgetV1.Data.total 768) 768,streams 768⟩) := by
  induction remaining generalizing i with
  | zero =>
      have last : i=768 := by omega
      subst i
      exact Loops.WhileRun.done
        (MainWorldGuard.world_guard (EmitUService.call platform fault) platform
          (streams 768) (SourceMainBudgetV1.Data.total 768) 768 (by decide)) (by decide)
  | succ remaining ih =>
      have hi : i < 768 := by omega
      exact Loops.WhileRun.next
        (MainWorldGuard.world_guard (EmitUService.call platform fault) platform
          (streams i) (SourceMainBudgetV1.Data.total i) i (by omega))
        (by have truthBoolean (b : Bool) :
          truth (Machine.boolean SynergyC.Header.layout b)=b := by cases b <;> rfl
            rw [truthBoolean]
            exact decide_eq_true hi)
        (rows i hi) (ih (i+1) (by omega))

theorem actual_while (platform : ScopedIO.WorldIO.Platform)
    (fault : ScopedIO.WorldIO.FaultPolicy) (streams : Nat → ScopedIO.Stream)
    (checked : CheckedRowCalls platform fault streams) :
    ScopedIO.WorldSource.Run SynergyC.Header.layout FullMainPrefix.service
      (EmitUService.call platform fault) platform
      (.whileLoop MainWorldGuard.guard (.sequence PointExecuteAPI.loopStatements))
      ⟨FullMainEdges.loopState (SourceMainBudgetV1.Data.total 0) 0,streams 0⟩
      (.continuing ⟨FullMainEdges.loopState (SourceMainBudgetV1.Data.total 768) 768,streams 768⟩) :=
  Loops.StmtRun.whileLoop (while_suffix platform fault streams
    (rows_of_checked_calls platform fault streams checked) 768 0 rfl)

#print axioms rows_of_checked_calls
#print axioms while_suffix
#print axioms actual_while
end SynergyHeightC.MainWorldLoop
