/- Complete unchanged C main on its actual checked normal-I/O path.
All initialization, 768 loop bodies, output, flush checks, scopes and return execute. -/
import SynergyHeightC.MainWorldStart
import SynergyHeightC.MainWorldFlush
namespace SynergyHeightC.MainWorldMain
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedNumerical ScopedIO
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 100000

theorem source_partition : PointExecuteAPI.mainStatements=
    PointExecuteAPI.mainStatements.take 6++
      [.whileLoop MainWorldGuard.guard (.sequence PointExecuteAPI.loopStatements)]++
      PointExecuteAPI.mainStatements.drop 7 := by rfl

theorem actual_body (platform : WorldIO.Platform) (fault : WorldIO.FaultPolicy)
    (streams : Nat → Stream) (checked : MainWorldLoop.CheckedRowCalls platform fault streams)
    (ranges : SynergyC.SourceIntervalMath.representable (SourceMainBudgetV1.Data.total 768))
    (emitted flushed : WorldIO.World)
    (emit : EmitIService.call platform fault "emitI"
      [SynergyC.SourceIntervalMath.represented (SourceMainBudgetV1.Data.total 768)]
      ⟨FullMainEdges.loopState (SourceMainBudgetV1.Data.total 768) 768,streams 768⟩=
      some (.unit,emitted))
    (flush : WorldIO.stdio platform fault "fflush" [WorldIO.stdoutValue platform] emitted=
      some (WorldIO.signed32 0,flushed)) :
    WorldSource.Run SynergyC.Header.layout FullMainPrefix.service
      (MainWorldService.call platform fault) platform Generated.f_main.body
      ⟨Initialization.state,streams 0⟩
      (.returned ⟨FullMainPrefix.cache,flushed.stream⟩ (WorldIO.signed32 0)) ∧
    flushed.stream.accepted=(streams 768).accepted++
      EmitUBuffer.bytes (SourceMainBudgetV1.Data.total 768).lo++
      EmitUBuffer.bytes (SourceMainBudgetV1.Data.total 768).hi ∧
    flushed.stream.delivered=flushed.stream.accepted.length := by
  have startRun := MainWorldStart.first_six (MainWorldService.call platform fault)
    platform (streams 0)
  have loopRun := WorldServiceMap.statement (MainWorldService.emitU_included platform fault)
    (MainWorldLoop.actual_while platform fault streams checked)
  have start : FullMainEdges.loopState (SourceMainBudgetV1.Data.total 0) 0=
      FullMainPrefix.prefixState := by
    rw [SourceMainBudgetV1.Data.total_zero]
    exact FullMainEdges.first_loop_state
  rw [start] at loopRun
  have output := MainTotalOutput.actual_emitI platform fault (SourceMainBudgetV1.Data.total 768)
    768 ranges.1 ranges.2 (streams 768) emit
  have emitRun : WorldSource.Run SynergyC.Header.layout FullMainPrefix.service
      (MainWorldService.call platform fault) platform
      (.eval (.call (.var "emitI") [.var "total"]))
      ⟨FullMainEdges.loopState (SourceMainBudgetV1.Data.total 768) 768,streams 768⟩
      (.continuing emitted) := Loops.StmtRun.evaluate (WorldServiceMap.evaluation
    (MainWorldService.emitI_included platform fault) output.1)
  have flushRun := MainWorldFlush.actual_flush platform fault (SourceMainBudgetV1.Data.total 768)
    768 emitted output.2.1 flush
  have lastRun := MainWorldFlush.actual_return (MainWorldService.call platform fault) platform flushed
  have footer := Loops.SeqRun.next emitRun
    (Loops.SeqRun.next flushRun.1 (Loops.SeqRun.returned (tail:=[]) lastRun))
  rw [←MainWorldFlush.source_partition] at footer
  have loopThenFooter := Loops.SeqRun.next loopRun footer
  have whole := EmitUSource.world_seq_append startRun loopThenFooter
  have combined : PointExecuteAPI.mainStatements.take 6++
      (.whileLoop MainWorldGuard.guard (.sequence PointExecuteAPI.loopStatements)::
        PointExecuteAPI.mainStatements.drop 7)=PointExecuteAPI.mainStatements :=
    source_partition.symm
  rw [combined] at whole
  have finalMemory : flushed.app=FullMainEdges.loopState (SourceMainBudgetV1.Data.total 768) 768 :=
    flushRun.2.1.trans output.2.1
  have body : WorldSource.Run SynergyC.Header.layout FullMainPrefix.service
      (MainWorldService.call platform fault) platform Generated.f_main.body
      ⟨Initialization.state,streams 0⟩
      (.returned ⟨FullMainPrefix.cache,flushed.stream⟩ (WorldIO.signed32 0)) := by
    change WorldSource.Run _ _ _ _ (.sequence PointExecuteAPI.mainStatements) _ _
    refine Loops.StmtRun.sequence whole ⟨rfl,?_⟩
    change (⟨FullMainPrefix.cache,flushed.stream⟩ : WorldIO.World)=
      ⟨Machine.popScope Initialization.state flushed.app,flushed.stream⟩
    rw [finalMemory,MainWorldStart.pop_final]
  refine ⟨body,flushRun.2.2.1.trans output.2.2,?_⟩
  rw [flushRun.2.2.2,flushRun.2.2.1]

#print axioms source_partition
#print axioms actual_body
end SynergyHeightC.MainWorldMain
