/- Actual main footer: both same-memory upper words are emitted, then i increments. -/
import SynergyMomentCHi.WorldFooterFields
namespace SynergyMomentCHi.WorldFooter
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedNumerical SynergyHeightC SynergyMomentC
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 100000

theorem actual_footer (kind : Kind) (platform : ScopedIO.WorldIO.Platform)
    (fault : ScopedIO.WorldIO.FaultPolicy) (total next : ProofBox) (i : Nat) (c d : ProofBox)
    (bound : i+1<2^32) (stream : ScopedIO.Stream) (middle after : ScopedIO.WorldIO.World)
    (first : EmitUService.call platform fault "emitU"
      [SynergyC.Word512.value (MainWeightModel.adjustedC c).hi]
      ⟨BudgetProposed.afterProposed total next i c d,stream⟩=some (.unit,middle))
    (second : EmitUService.call platform fault "emitU" [SynergyC.Word512.value d.hi]
      middle=some (.unit,after)) :
    Loops.SeqRun (ScopedIO.WorldSource.Eval SynergyC.Header.layout FullMainPrefix.service
      (EmitUService.call platform fault) platform)
      (ScopedIO.WorldSource.Declare SynergyC.Header.layout FullMainPrefix.service)
      truth ScopedIO.WorldSource.Scope ((loopStatements kind).drop 9)
      ⟨BudgetProposed.afterProposed total next i c d,stream⟩
      (.continuing ⟨WorldFooterState.afterIncrement total next i c d,after.stream⟩) ∧
    after.stream.accepted=stream.accepted++EmitUBuffer.bytes (MainWeightModel.adjustedC c).hi++
      EmitUBuffer.bytes d.hi := by
  have firstFacts := EmitUReturnFacts.call_word_output platform fault
    (MainWeightModel.adjustedC c).hi _ middle .unit first
  have secondFacts := EmitUReturnFacts.call_word_output platform fault d.hi middle after .unit second
  have sameAfter : after.app=BudgetProposed.afterProposed total next i c d :=
    secondFacts.2.1.trans firstFacts.2.1
  have cEval : ScopedIO.WorldSource.Eval SynergyC.Header.layout FullMainPrefix.service
      (EmitUService.call platform fault) platform (.field "." (.var "c") "hi")
      ⟨BudgetProposed.afterProposed total next i c d,stream⟩
      ⟨BudgetProposed.afterProposed total next i c d,stream⟩
      (SynergyC.Word512.value (MainWeightModel.adjustedC c).hi) :=
    .pure (WorldFooterFields.eval_c_hi FullMainPrefix.service total next i c d)
  have dEval := WorldFooterFields.world_d_hi FullMainPrefix.service
    (EmitUService.call platform fault) platform middle total next i c d firstFacts.2.1
  have increment := WorldFooterFields.world_increment FullMainPrefix.service
    (EmitUService.call platform fault) platform after total next i c d bound sameAfter
  constructor
  · rw [WorldFooterState.actual_footer kind]
    exact Loops.SeqRun.next
      (Loops.StmtRun.evaluate (.call (.cons cEval (.nil _)) first))
      (Loops.SeqRun.next (Loops.StmtRun.evaluate (.call (.cons dEval (.nil _)) second))
        (Loops.SeqRun.next (Loops.StmtRun.evaluate increment) (Loops.SeqRun.nil _)))
  · rw [secondFacts.2.2,firstFacts.2.2]

#print axioms actual_footer
end SynergyMomentCHi.WorldFooter
