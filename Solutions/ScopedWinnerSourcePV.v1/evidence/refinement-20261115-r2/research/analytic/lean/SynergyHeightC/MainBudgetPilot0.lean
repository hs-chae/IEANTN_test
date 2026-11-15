/- Kernel-checked actual C arithmetic suffix, first iteration. -/
import SynergyHeightC.MainBudgetExecute
import SourceMainFramesV1.Point0000
open Lean Meta Elab Tactic
namespace SynergyHeightC.MainBudgetPilot0
open ScopedC ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem execution :
    MainBudgetExecute.run ⟨0,0⟩ 0
      SourceMainFramesV1.Point0000.outputs.1 SourceMainFramesV1.Point0000.outputs.2=
      some (.continuing (MainBudgetExecute.afterBudget ⟨0,0⟩ 0
        SourceMainFramesV1.Point0000.outputs.1 SourceMainFramesV1.Point0000.outputs.2)) := by
  unfold MainBudgetExecute.run
  run_tac do
    let goal ← getMainGoal
    let target ← goal.getType
    let args := target.getAppArgs
    unless target.getAppFn.isConstOf ``Eq && args.size == 3 do
      throwError "expected actual source-state equality"
    goal.assign (←mkEqRefl args[1]!)

theorem actual_source :
    Loops.SeqRun (ArraySourceCalls.Eval SynergyC.Header.layout FullMainPrefix.service)
      (ArraySourceCalls.Declare SynergyC.Header.layout FullMainPrefix.service)
      truth ArraySourceCalls.Scope MainBudgetExecute.statements
      (MainBudgetExecute.before ⟨0,0⟩ 0
        SourceMainFramesV1.Point0000.outputs.1 SourceMainFramesV1.Point0000.outputs.2)
      (.continuing (MainBudgetExecute.afterBudget ⟨0,0⟩ 0
        SourceMainFramesV1.Point0000.outputs.1 SourceMainFramesV1.Point0000.outputs.2)) :=
  MainBudgetExecute.source_of_execution execution

#print axioms execution
#print axioms actual_source
end SynergyHeightC.MainBudgetPilot0
