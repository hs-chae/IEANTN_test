/- Exact actual C arithmetic suffix for cell134/768.
Proposed prefix integers are accepted only through kernel-checked execution and recurrence. -/
import SynergyHeightC.MainBudgetExecute
import SourceMainFramesV1.Point0134
import Lean.Util.CollectAxioms
open Lean Meta Elab Tactic
namespace SourceMainBudgetV1.Cell0134
open ScopedC ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def total : ProofBox := ⟨1343391244030985526974378261252093050,1343391244030985526974383113355125428⟩
def nextTotal : ProofBox := ⟨1351324631101860621430595064215265143,1351324631101860621430599963190427847⟩
theorem input_total_range : 0≤total.lo ∧ total.lo≤total.hi ∧ total.hi<ProofBox.scale 128 := by
 decide +kernel
theorem execution : SynergyHeightC.MainBudgetExecute.run total 134
 SourceMainFramesV1.Point0134.outputs.1 SourceMainFramesV1.Point0134.outputs.2=
 some (.continuing (SynergyHeightC.MainBudgetExecute.afterBudget total 134
  SourceMainFramesV1.Point0134.outputs.1 SourceMainFramesV1.Point0134.outputs.2)) := by
 unfold SynergyHeightC.MainBudgetExecute.run
 run_tac do
  let goal ← getMainGoal
  let target ← goal.getType
  let args := target.getAppArgs
  unless target.getAppFn.isConstOf ``Eq && args.size==3 do
   throwError "expected actual source-state equality"
  goal.assign (←mkEqRefl args[1]!)
theorem next_total : ProofBox.add total (SynergyHeightC.MainWeightModel.term
 (SynergyHeightC.MainBudgetExecute.left 134) (SynergyHeightC.MainBudgetExecute.right 134)
 SourceMainFramesV1.Point0134.outputs.1 SourceMainFramesV1.Point0134.outputs.2)=nextTotal := by decide +kernel
theorem actual_source :
 Loops.SeqRun (ArraySourceCalls.Eval SynergyC.Header.layout SynergyHeightC.FullMainPrefix.service)
  (ArraySourceCalls.Declare SynergyC.Header.layout SynergyHeightC.FullMainPrefix.service)
  truth ArraySourceCalls.Scope SynergyHeightC.MainBudgetExecute.statements
  (SynergyHeightC.MainBudgetExecute.before total 134 SourceMainFramesV1.Point0134.outputs.1 SourceMainFramesV1.Point0134.outputs.2)
  (.continuing (SynergyHeightC.MainBudgetExecute.afterBudget total 134
   SourceMainFramesV1.Point0134.outputs.1 SourceMainFramesV1.Point0134.outputs.2)) :=
 SynergyHeightC.MainBudgetExecute.source_of_execution execution
end SourceMainBudgetV1.Cell0134
open Lean Elab
run_elab do
 let env ← getEnv
 for n in ([`SourceMainBudgetV1.Cell0134.input_total_range,`SourceMainBudgetV1.Cell0134.execution,`SourceMainBudgetV1.Cell0134.next_total,`SourceMainBudgetV1.Cell0134.actual_source] : List Name) do
  let some ci := env.find? n | throwError "missing actual source-budget root"
  let ax ← Lean.collectAxioms n
  logInfo m!"SOURCE_BUDGET_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
