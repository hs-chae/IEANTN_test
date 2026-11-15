/- Actual high-only moment loop body. The next accumulator is an arbitrary
parameter until a concrete checked budget execution supplies it; no numerical
prefix or mathematical term is assumed by this source-composition theorem. -/
import SynergyMomentCHi.WorldFooter
import SynergyHeightC.MainWorldPrefix

namespace SynergyMomentCHi.WorldIteration
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedNumerical SynergyHeightC SynergyMomentC
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 100000

theorem source_partition (kind : Kind) : loopStatements kind =
    PointExecuteAPI.loopStatements.take 4 ++
      (Budget.statements kind ++ (loopStatements kind).drop 9) := by
  cases kind <;> rfl

theorem actual_budget (kind : Kind) (service : ScopedIO.WorldIO.Call)
    (platform : ScopedIO.WorldIO.Platform) (stream : ScopedIO.Stream)
    (total next c d : ProofBox) (i : Nat)
    (execution : Budget.run kind total i c d=some
      (.continuing (BudgetProposed.afterProposed total next i c d))) :
    Loops.SeqRun
      (ScopedIO.WorldSource.Eval SynergyC.Header.layout FullMainPrefix.service service platform)
      (ScopedIO.WorldSource.Declare SynergyC.Header.layout FullMainPrefix.service)
      truth ScopedIO.WorldSource.Scope (Budget.statements kind)
      ⟨Budget.before total i c d,stream⟩
      (.continuing ⟨BudgetProposed.afterProposed total next i c d,stream⟩) := by
  have eq : Budget.run kind total i c d=ArraySourceExecute.statements
      SynergyC.Header.layout FullMainPrefix.service 128 2048 (Budget.statements kind)
      (Budget.before total i c d) := by
    unfold Budget.run
    rfl
  have actual := Eq.mp (congrArg (fun result => result=some
    (.continuing (BudgetProposed.afterProposed total next i c d))) eq) execution
  exact (ScopedIO.WorldLift.pure_sound SynergyC.Header.layout FullMainPrefix.service
    service platform stream 128 2048).2.1 _ _ _ actual

theorem actual_body (kind : Kind) (platform : ScopedIO.WorldIO.Platform)
    (fault : ScopedIO.WorldIO.FaultPolicy) {i : Nat} (edges : FullMainEdges.ExactEdges i)
    (total next c d : ProofBox) (bound : i+1<2^32)
    (pointRun : FullContractPointExecute.run (FullMainFrame.base total i)
      (MainInputPointComposition.input i)=some
      (.unit,PointExecuteAPI.filled (FullMainFrame.base total i) c d))
    (budgetRun : Budget.run kind total i c d=some
      (.continuing (BudgetProposed.afterProposed total next i c d)))
    (stream : ScopedIO.Stream) (middle after : ScopedIO.WorldIO.World)
    (first : EmitUService.call platform fault "emitU"
      [SynergyC.Word512.value (MainWeightModel.adjustedC c).hi]
      ⟨BudgetProposed.afterProposed total next i c d,stream⟩=some (.unit,middle))
    (second : EmitUService.call platform fault "emitU" [SynergyC.Word512.value d.hi]
      middle=some (.unit,after)) :
    ScopedIO.WorldSource.Run SynergyC.Header.layout FullMainPrefix.service
      (EmitUService.call platform fault) platform (.sequence (loopStatements kind))
      ⟨FullMainEdges.loopState total i,stream⟩
      (.continuing ⟨FullMainEdges.loopState next (i+1),after.stream⟩) ∧
    after.stream.accepted=stream.accepted++EmitUBuffer.bytes (MainWeightModel.adjustedC c).hi++
      EmitUBuffer.bytes d.hi := by
  have pointPrefix := MainWorldPrefix.actual_point_prefix (EmitUService.call platform fault)
    platform stream edges total c d pointRun
  have budget := actual_budget kind (EmitUService.call platform fault)
    platform stream total next c d i budgetRun
  have footer := WorldFooter.actual_footer kind platform fault total next i c d bound
    stream middle after first second
  have all := EmitUSource.world_seq_append pointPrefix
    (EmitUSource.world_seq_append budget footer.1)
  rw [←source_partition kind] at all
  refine ⟨Loops.StmtRun.sequence all ?_,footer.2⟩
  change (⟨FullMainEdges.loopState next (i+1),after.stream⟩ : ScopedIO.WorldIO.World)=
    ⟨Machine.popScope (FullMainEdges.loopState total i)
      (WorldFooterState.afterIncrement total next i c d),after.stream⟩
  rw [WorldFooterState.restores_loop_state]

#print axioms source_partition
#print axioms actual_budget
#print axioms actual_body
end SynergyMomentCHi.WorldIteration
