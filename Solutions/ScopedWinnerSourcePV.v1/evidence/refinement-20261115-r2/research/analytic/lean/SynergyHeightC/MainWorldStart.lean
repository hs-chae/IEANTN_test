/- Actual C global initialization and first six main statements in the explicit
I/O world. No initial application representation is trusted. -/
import SynergyHeightC.FullMainInitialization
import SynergyHeightC.MainWorldService
import SynergyHeightC.MainWorldLoop
namespace SynergyHeightC.MainWorldStart
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 100000

theorem prefix_execution : ArraySourceExecute.statements SynergyC.Header.layout
    FullMainPrefix.service 128 2048 FullMainPrefix.statements FullMainPrefix.cache=
    some (.continuing FullMainPrefix.prefixState) := by
  obtain ⟨arena,run⟩ := ArrayStages.hasNext_sound FullMainPrefix.checked_prefix
  have definition : FullMainPrefix.run=ArraySourceExecute.statements SynergyC.Header.layout
      FullMainPrefix.service 128 2048 FullMainPrefix.statements FullMainPrefix.cache := by
    unfold FullMainPrefix.run
    rfl
  have execution := Eq.mp (congrArg (fun result=>result=some
    (.continuing (ArrayStages.withArena FullMainPrefix.prefixState arena))) definition) run
  have arenaExact :=
    (NatEffects.statements_effect SynergyC.Header.layout FullMainPrefix.service
      FullMainPrefix.service_keeps 128 2048).2.1 FullMainPrefix.statements FullMainPrefix.cache
      (.continuing (ArrayStages.withArena FullMainPrefix.prefixState arena)) execution
  have empty : arena=NatArena.empty := arenaExact
  have state : ArrayStages.withArena FullMainPrefix.prefixState arena=FullMainPrefix.prefixState := by
    rw [empty]
    rfl
  rw [state] at execution
  exact execution

theorem lift_evaluation {cfg : Layout} {pure : Machine.Call}
    (service : ScopedIO.WorldIO.Call) (platform : ScopedIO.WorldIO.Platform)
    (stream : ScopedIO.Stream) {e : Expr} {s t : State}
    (old : ArraySourceCalls.Run cfg pure (.eval e) s (.continuing t)) :
    ScopedIO.WorldSource.Run cfg pure service platform (.eval e)
      ⟨s,stream⟩ (.continuing ⟨t,stream⟩) := by
  cases old with
  | evaluate run =>
      obtain ⟨fuel,execution⟩ := run
      exact Loops.StmtRun.evaluate (ScopedIO.WorldSource.Eval.pure execution)

theorem first_six (service : ScopedIO.WorldIO.Call) (platform : ScopedIO.WorldIO.Platform)
    (stream : ScopedIO.Stream) :
    Loops.SeqRun (ScopedIO.WorldSource.Eval SynergyC.Header.layout FullMainPrefix.service
      service platform) (ScopedIO.WorldSource.Declare SynergyC.Header.layout FullMainPrefix.service)
      truth ScopedIO.WorldSource.Scope (PointExecuteAPI.mainStatements.take 6)
      ⟨Initialization.state,stream⟩ (.continuing ⟨FullMainPrefix.prefixState,stream⟩) := by
  rw [FullMainPrefix.actual_main_prefix]
  have initStatement := lift_evaluation service platform stream
    FullMainInitialization.actual_init_statement
  exact Loops.SeqRun.next initStatement
    ((ScopedIO.WorldLift.pure_sound SynergyC.Header.layout FullMainPrefix.service service
      platform stream 128 2048).2.1 _ _ _ prefix_execution)

theorem actual_main_arguments : bindArgs SynergyC.Header.layout Generated.f_main.parameters []
    Initialization.state=some Initialization.state := by rfl

theorem pop_final (total : ProofBox) :
    Machine.popScope Initialization.state (FullMainEdges.loopState total 768)=FullMainPrefix.cache := by
  have cacheLength : InitCacheProposal.heap.length=14 := by rfl
  have takeCache : List.take 14 InitCacheProposal.heap=InitCacheProposal.heap := by
    rw [←cacheLength]
    exact List.take_length
  simp [Machine.popScope,Initialization.state,FullMainEdges.loopState,FullMainPrefix.afterSpan,
    FullMainPrefix.afterHeight,FullMainPrefix.afterCells,FullMainPrefix.cache,
    InitCacheProposal.postState,Machine.allocate,List.take_append,cacheLength,takeCache]

#print axioms prefix_execution
#print axioms lift_evaluation
#print axioms first_six
#print axioms actual_main_arguments
#print axioms pop_final
end SynergyHeightC.MainWorldStart
