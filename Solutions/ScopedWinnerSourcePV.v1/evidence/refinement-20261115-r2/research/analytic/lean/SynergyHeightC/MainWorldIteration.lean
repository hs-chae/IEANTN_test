/- One actual main-loop body: source inputs, actual point output, actual C budget,
same-memory binary outputs, index update and canonical scoped-state restoration.
The finite input/point/budget providers and actual I/O calls are explicit. -/
import SynergyHeightC.MainWorldPrefix
import SynergyHeightC.MainWorldFooter
namespace SynergyHeightC.MainWorldIteration
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 100000

theorem source_partition : PointExecuteAPI.loopStatements=
    PointExecuteAPI.loopStatements.take 4++
      (MainBudgetExecute.statements++PointExecuteAPI.loopStatements.drop 9) := by rfl

theorem actual_body (platform : ScopedIO.WorldIO.Platform)
    (fault : ScopedIO.WorldIO.FaultPolicy) {i : Nat} (edges : FullMainEdges.ExactEdges i)
    (total c d : ProofBox) (bound : i+1<2^32)
    (pointRun : FullContractPointExecute.run (FullMainFrame.base total i)
      (MainInputPointComposition.input i)=some
      (.unit,PointExecuteAPI.filled (FullMainFrame.base total i) c d))
    (budgetRun : MainBudgetExecute.run total i c d=some
      (.continuing (MainBudgetExecute.afterBudget total i c d)))
    (stream : ScopedIO.Stream) (middle after : ScopedIO.WorldIO.World)
    (first : EmitUService.call platform fault "emitU"
      [SynergyC.Word512.value (MainWeightModel.adjustedC c).hi]
      ⟨MainBudgetExecute.afterBudget total i c d,stream⟩=some (.unit,middle))
    (second : EmitUService.call platform fault "emitU" [SynergyC.Word512.value d.hi]
      middle=some (.unit,after)) :
    ScopedIO.WorldSource.Run SynergyC.Header.layout FullMainPrefix.service
      (EmitUService.call platform fault) platform (.sequence PointExecuteAPI.loopStatements)
      ⟨FullMainEdges.loopState total i,stream⟩
      (.continuing ⟨FullMainEdges.loopState (MainFooterState.nextTotal total i c d) (i+1),after.stream⟩) ∧
    after.stream.accepted=stream.accepted++EmitUBuffer.bytes (MainWeightModel.adjustedC c).hi++
      EmitUBuffer.bytes d.hi := by
  have pointPrefix := MainWorldPrefix.actual_point_prefix (EmitUService.call platform fault)
    platform stream edges total c d pointRun
  have budget := MainWorldPrefix.actual_budget (EmitUService.call platform fault)
    platform stream total c d i budgetRun
  have footer := MainWorldFooter.actual_footer platform fault total i c d bound
    stream middle after first second
  have all := EmitUSource.world_seq_append pointPrefix
    (EmitUSource.world_seq_append budget footer.1)
  rw [←source_partition] at all
  refine ⟨Loops.StmtRun.sequence all ?_,footer.2⟩
  change (⟨FullMainEdges.loopState (MainFooterState.nextTotal total i c d) (i+1),after.stream⟩ :
      ScopedIO.WorldIO.World)=
    ⟨Machine.popScope (FullMainEdges.loopState total i)
      (MainFooterState.afterIncrement total i c d),after.stream⟩
  rw [MainFooterState.restores_loop_state]

#print axioms actual_body
end SynergyHeightC.MainWorldIteration
