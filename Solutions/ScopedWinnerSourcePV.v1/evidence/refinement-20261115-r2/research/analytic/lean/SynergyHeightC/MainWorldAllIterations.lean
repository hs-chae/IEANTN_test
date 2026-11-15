/- All finite numerical/source providers are instantiated in each actual main body.
Actual checked I/O calls remain explicit normal-execution conditions. -/
import SynergyHeightC.MainWorldGuard
import SourceMainBudgetV1.All
import SourceHeightEdgesV1.All
import SourceMainFramesV1.AllExecution
namespace SynergyHeightC.MainWorldAllIterations
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 100000

theorem actual_rows (i : Nat) (hi : i < 768) :
    ∃ c d, PointExecuteAPI.modelOutputs (MainInputPointComposition.input i)=some (c,d) ∧
    ∀ (platform : ScopedIO.WorldIO.Platform) (fault : ScopedIO.WorldIO.FaultPolicy)
      (stream : ScopedIO.Stream) (middle after : ScopedIO.WorldIO.World),
    EmitUService.call platform fault "emitU" [SynergyC.Word512.value (MainWeightModel.adjustedC c).hi]
      ⟨MainBudgetExecute.afterBudget (SourceMainBudgetV1.Data.total i) i c d,stream⟩=
      some (.unit,middle) →
    EmitUService.call platform fault "emitU" [SynergyC.Word512.value d.hi]
      middle=some (.unit,after) →
    ScopedIO.WorldSource.Run SynergyC.Header.layout FullMainPrefix.service
      (EmitUService.call platform fault) platform (.sequence PointExecuteAPI.loopStatements)
      ⟨FullMainEdges.loopState (SourceMainBudgetV1.Data.total i) i,stream⟩
      (.continuing ⟨FullMainEdges.loopState (SourceMainBudgetV1.Data.total (i+1)) (i+1),after.stream⟩) ∧
    after.stream.accepted=stream.accepted++EmitUBuffer.bytes (MainWeightModel.adjustedC c).hi++
      EmitUBuffer.bytes d.hi := by
  obtain ⟨input,pair,leftDefined,rightDefined,model,budgetRun,recurrence⟩ :=
    SourceMainBudgetV1.All.cells i hi
  have sameInput : MainInputPointComposition.input i=input := by
    simp only [MainInputPointComposition.input,rightDefined,Option.getD_some]
  have hiGrid : i < logCellCount := hi
  obtain ⟨pointInput,pointPair,pointDefined,pointModel,pointRun⟩ :=
    SourceMainFramesV1.AllExecution.executions i hiGrid (SourceMainBudgetV1.Data.total i)
  have inputIdentity : pointInput=input := Option.some.inj (pointDefined.symm.trans rightDefined)
  subst pointInput
  have pairIdentity : pointPair=pair := Option.some.inj (pointModel.symm.trans model)
  subst pointPair
  rw [←sameInput] at model pointRun
  refine ⟨pair.1,pair.2,model,?_⟩
  intro platform fault stream middle after first second
  have body := MainWorldIteration.actual_body platform fault
    (SourceHeightEdgesV1.All.edges i hiGrid) (SourceMainBudgetV1.Data.total i) pair.1 pair.2
    (by omega) pointRun budgetRun stream middle after first second
  change MainFooterState.nextTotal (SourceMainBudgetV1.Data.total i) i pair.1 pair.2=
    SourceMainBudgetV1.Data.total (i+1) at recurrence
  rw [recurrence] at body
  exact body

#print axioms actual_rows
end SynergyHeightC.MainWorldAllIterations
