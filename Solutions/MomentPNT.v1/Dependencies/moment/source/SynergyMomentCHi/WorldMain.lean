/- Complete new source entry body from proved actual rows and checked stdio.
Initialization, unchanged output/flush/return and scope cleanup are reused.
Generic total values are never trusted numerical or application-success facts. -/
import SynergyMomentCHi.WorldLoop
import SynergyHeightC.MainWorldStart
import SynergyHeightC.MainWorldFlush
namespace SynergyMomentCHi.WorldMain
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedNumerical ScopedIO SynergyHeightC SynergyMomentC
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 100000

def statements (kind : Kind) : List Stmt :=
  PointExecuteAPI.mainStatements.take 6 ++
    [.whileLoop MainWorldGuard.guard (.sequence (loopStatements kind))] ++
    PointExecuteAPI.mainStatements.drop 7

theorem source_partition (kind : Kind) : (entry kind).body = .sequence (statements kind) := rfl

theorem statement_partition (kind : Kind) : statements kind=
    PointExecuteAPI.mainStatements.take 6++
      [.whileLoop MainWorldGuard.guard (.sequence (loopStatements kind))]++
      PointExecuteAPI.mainStatements.drop 7 := by rfl

theorem actual_body (kind : Kind) (platform : WorldIO.Platform) (fault : WorldIO.FaultPolicy)
    (totals : Nat → ProofBox) (zero : totals 0=⟨0,0⟩)
    (streams : Nat → Stream)
    (rows : ∀ i,i<768 → WorldLoop.RowRun kind platform fault totals streams i)
    (ranges : SynergyC.SourceIntervalMath.representable (totals 768))
    (emitted flushed : WorldIO.World)
    (emit : EmitIService.call platform fault "emitI"
      [SynergyC.SourceIntervalMath.represented (totals 768)]
      ⟨FullMainEdges.loopState (totals 768) 768,streams 768⟩=
      some (.unit,emitted))
    (flush : WorldIO.stdio platform fault "fflush" [WorldIO.stdoutValue platform] emitted=
      some (WorldIO.signed32 0,flushed)) :
    WorldSource.Run SynergyC.Header.layout FullMainPrefix.service
      (MainWorldService.call platform fault) platform (entry kind).body
      ⟨Initialization.state,streams 0⟩
      (.returned ⟨FullMainPrefix.cache,flushed.stream⟩ (WorldIO.signed32 0)) ∧
    flushed.stream.accepted=(streams 768).accepted++
      EmitUBuffer.bytes (totals 768).lo++
      EmitUBuffer.bytes (totals 768).hi ∧
    flushed.stream.delivered=flushed.stream.accepted.length := by
  have startRun := MainWorldStart.first_six (MainWorldService.call platform fault)
    platform (streams 0)
  have loopRun := WorldServiceMap.statement (MainWorldService.emitU_included platform fault)
    (WorldLoop.actual_while kind platform fault totals streams rows)
  have start : FullMainEdges.loopState (totals 0) 0=
      FullMainPrefix.prefixState := by
    rw [zero]
    exact FullMainEdges.first_loop_state
  rw [start] at loopRun
  have output := MainTotalOutput.actual_emitI platform fault (totals 768)
    768 ranges.1 ranges.2 (streams 768) emit
  have emitRun : WorldSource.Run SynergyC.Header.layout FullMainPrefix.service
      (MainWorldService.call platform fault) platform
      (.eval (.call (.var "emitI") [.var "total"]))
      ⟨FullMainEdges.loopState (totals 768) 768,streams 768⟩
      (.continuing emitted) := Loops.StmtRun.evaluate (WorldServiceMap.evaluation
    (MainWorldService.emitI_included platform fault) output.1)
  have flushRun := MainWorldFlush.actual_flush platform fault (totals 768)
    768 emitted output.2.1 flush
  have lastRun := MainWorldFlush.actual_return (MainWorldService.call platform fault) platform flushed
  have footer := Loops.SeqRun.next emitRun
    (Loops.SeqRun.next flushRun.1 (Loops.SeqRun.returned (tail:=[]) lastRun))
  rw [←MainWorldFlush.source_partition] at footer
  have loopThenFooter := Loops.SeqRun.next loopRun footer
  have whole := EmitUSource.world_seq_append startRun loopThenFooter
  have combined : PointExecuteAPI.mainStatements.take 6++
      (.whileLoop MainWorldGuard.guard (.sequence (loopStatements kind))::
        PointExecuteAPI.mainStatements.drop 7)=statements kind := rfl
  rw [combined] at whole
  have finalMemory : flushed.app=FullMainEdges.loopState (totals 768) 768 :=
    flushRun.2.1.trans output.2.1
  have body : WorldSource.Run SynergyC.Header.layout FullMainPrefix.service
      (MainWorldService.call platform fault) platform (entry kind).body
      ⟨Initialization.state,streams 0⟩
      (.returned ⟨FullMainPrefix.cache,flushed.stream⟩ (WorldIO.signed32 0)) := by
    change WorldSource.Run _ _ _ _ (.sequence (statements kind)) _ _
    refine Loops.StmtRun.sequence whole ⟨rfl,?_⟩
    change (⟨FullMainPrefix.cache,flushed.stream⟩ : WorldIO.World)=
      ⟨Machine.popScope Initialization.state flushed.app,flushed.stream⟩
    rw [finalMemory,MainWorldStart.pop_final]
  refine ⟨body,flushRun.2.2.1.trans output.2.2,?_⟩
  rw [flushRun.2.2.2,flushRun.2.2.1]

#print axioms source_partition
#print axioms statement_partition
#print axioms actual_body
end SynergyMomentCHi.WorldMain
