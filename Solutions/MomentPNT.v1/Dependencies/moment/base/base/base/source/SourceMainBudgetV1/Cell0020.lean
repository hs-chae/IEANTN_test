/- Exact actual C arithmetic suffix for cell20/768.
Proposed prefix integers are accepted only through kernel-checked execution and recurrence. -/
import SynergyHeightC.MainBudgetExecute
import SourceMainFramesV1.Point0020
import Lean.Util.CollectAxioms
open Lean Meta Elab Tactic
namespace SourceMainBudgetV1.Cell0020
open ScopedC ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def total : ProofBox := ⟨238277476423939459706008456504152992,238277476423939459706009033766648125⟩
def nextTotal : ProofBox := ⟨249821278715704598121390142356073968,249821278715704598121390749587401320⟩
theorem input_total_range : 0≤total.lo ∧ total.lo≤total.hi ∧ total.hi<ProofBox.scale 128 := by
 decide +kernel
theorem execution : SynergyHeightC.MainBudgetExecute.run total 20
 SourceMainFramesV1.Point0020.outputs.1 SourceMainFramesV1.Point0020.outputs.2=
 some (.continuing (SynergyHeightC.MainBudgetExecute.afterBudget total 20
  SourceMainFramesV1.Point0020.outputs.1 SourceMainFramesV1.Point0020.outputs.2)) := by
 unfold SynergyHeightC.MainBudgetExecute.run
 run_tac do
  let goal ← getMainGoal
  let target ← goal.getType
  let args := target.getAppArgs
  unless target.getAppFn.isConstOf ``Eq && args.size==3 do
   throwError "expected actual source-state equality"
  goal.assign (←mkEqRefl args[1]!)
theorem next_total : ProofBox.add total (SynergyHeightC.MainWeightModel.term
 (SynergyHeightC.MainBudgetExecute.left 20) (SynergyHeightC.MainBudgetExecute.right 20)
 SourceMainFramesV1.Point0020.outputs.1 SourceMainFramesV1.Point0020.outputs.2)=nextTotal := by decide +kernel
theorem actual_source :
 Loops.SeqRun (ArraySourceCalls.Eval SynergyC.Header.layout SynergyHeightC.FullMainPrefix.service)
  (ArraySourceCalls.Declare SynergyC.Header.layout SynergyHeightC.FullMainPrefix.service)
  truth ArraySourceCalls.Scope SynergyHeightC.MainBudgetExecute.statements
  (SynergyHeightC.MainBudgetExecute.before total 20 SourceMainFramesV1.Point0020.outputs.1 SourceMainFramesV1.Point0020.outputs.2)
  (.continuing (SynergyHeightC.MainBudgetExecute.afterBudget total 20
   SourceMainFramesV1.Point0020.outputs.1 SourceMainFramesV1.Point0020.outputs.2)) :=
 SynergyHeightC.MainBudgetExecute.source_of_execution execution
end SourceMainBudgetV1.Cell0020
open Lean Elab
run_elab do
 let env ← getEnv
 for n in ([`SourceMainBudgetV1.Cell0020.input_total_range,`SourceMainBudgetV1.Cell0020.execution,`SourceMainBudgetV1.Cell0020.next_total,`SourceMainBudgetV1.Cell0020.actual_source] : List Name) do
  let some ci := env.find? n | throwError "missing actual source-budget root"
  let ax ← Lean.collectAxioms n
  logInfo m!"SOURCE_BUDGET_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
