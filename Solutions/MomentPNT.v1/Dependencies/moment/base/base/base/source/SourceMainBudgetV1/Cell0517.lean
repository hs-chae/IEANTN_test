/- Exact actual C arithmetic suffix for cell517/768.
Proposed prefix integers are accepted only through kernel-checked execution and recurrence. -/
import SynergyHeightC.MainBudgetExecute
import SourceMainFramesV1.Point0517
import Lean.Util.CollectAxioms
open Lean Meta Elab Tactic
namespace SourceMainBudgetV1.Cell0517
open ScopedC ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def total : ProofBox := ⟨2800097519691082659038746083142411501,2800097519691082659038815740627983378⟩
def nextTotal : ProofBox := ⟨2801024025028235661512522632769659586,2801024025028235661512592828753125672⟩
theorem input_total_range : 0≤total.lo ∧ total.lo≤total.hi ∧ total.hi<ProofBox.scale 128 := by
 decide +kernel
theorem execution : SynergyHeightC.MainBudgetExecute.run total 517
 SourceMainFramesV1.Point0517.outputs.1 SourceMainFramesV1.Point0517.outputs.2=
 some (.continuing (SynergyHeightC.MainBudgetExecute.afterBudget total 517
  SourceMainFramesV1.Point0517.outputs.1 SourceMainFramesV1.Point0517.outputs.2)) := by
 unfold SynergyHeightC.MainBudgetExecute.run
 run_tac do
  let goal ← getMainGoal
  let target ← goal.getType
  let args := target.getAppArgs
  unless target.getAppFn.isConstOf ``Eq && args.size==3 do
   throwError "expected actual source-state equality"
  goal.assign (←mkEqRefl args[1]!)
theorem next_total : ProofBox.add total (SynergyHeightC.MainWeightModel.term
 (SynergyHeightC.MainBudgetExecute.left 517) (SynergyHeightC.MainBudgetExecute.right 517)
 SourceMainFramesV1.Point0517.outputs.1 SourceMainFramesV1.Point0517.outputs.2)=nextTotal := by decide +kernel
theorem actual_source :
 Loops.SeqRun (ArraySourceCalls.Eval SynergyC.Header.layout SynergyHeightC.FullMainPrefix.service)
  (ArraySourceCalls.Declare SynergyC.Header.layout SynergyHeightC.FullMainPrefix.service)
  truth ArraySourceCalls.Scope SynergyHeightC.MainBudgetExecute.statements
  (SynergyHeightC.MainBudgetExecute.before total 517 SourceMainFramesV1.Point0517.outputs.1 SourceMainFramesV1.Point0517.outputs.2)
  (.continuing (SynergyHeightC.MainBudgetExecute.afterBudget total 517
   SourceMainFramesV1.Point0517.outputs.1 SourceMainFramesV1.Point0517.outputs.2)) :=
 SynergyHeightC.MainBudgetExecute.source_of_execution execution
end SourceMainBudgetV1.Cell0517
open Lean Elab
run_elab do
 let env ← getEnv
 for n in ([`SourceMainBudgetV1.Cell0517.input_total_range,`SourceMainBudgetV1.Cell0517.execution,`SourceMainBudgetV1.Cell0517.next_total,`SourceMainBudgetV1.Cell0517.actual_source] : List Name) do
  let some ci := env.find? n | throwError "missing actual source-budget root"
  let ax ← Lean.collectAxioms n
  logInfo m!"SOURCE_BUDGET_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
