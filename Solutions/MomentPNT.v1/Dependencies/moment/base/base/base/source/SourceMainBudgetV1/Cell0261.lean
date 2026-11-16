/- Exact actual C arithmetic suffix for cell261/768.
Proposed prefix integers are accepted only through kernel-checked execution and recurrence. -/
import SynergyHeightC.MainBudgetExecute
import SourceMainFramesV1.Point0261
import Lean.Util.CollectAxioms
open Lean Meta Elab Tactic
namespace SourceMainBudgetV1.Cell0261
open ScopedC ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def total : ProofBox := ⟨2141458834550551845313638274473598342,2141458834550551845313651172660660829⟩
def nextTotal : ProofBox := ⟨2146215026476971100828258190120500895,2146215026476971100828271173609523956⟩
theorem input_total_range : 0≤total.lo ∧ total.lo≤total.hi ∧ total.hi<ProofBox.scale 128 := by
 decide +kernel
theorem execution : SynergyHeightC.MainBudgetExecute.run total 261
 SourceMainFramesV1.Point0261.outputs.1 SourceMainFramesV1.Point0261.outputs.2=
 some (.continuing (SynergyHeightC.MainBudgetExecute.afterBudget total 261
  SourceMainFramesV1.Point0261.outputs.1 SourceMainFramesV1.Point0261.outputs.2)) := by
 unfold SynergyHeightC.MainBudgetExecute.run
 run_tac do
  let goal ← getMainGoal
  let target ← goal.getType
  let args := target.getAppArgs
  unless target.getAppFn.isConstOf ``Eq && args.size==3 do
   throwError "expected actual source-state equality"
  goal.assign (←mkEqRefl args[1]!)
theorem next_total : ProofBox.add total (SynergyHeightC.MainWeightModel.term
 (SynergyHeightC.MainBudgetExecute.left 261) (SynergyHeightC.MainBudgetExecute.right 261)
 SourceMainFramesV1.Point0261.outputs.1 SourceMainFramesV1.Point0261.outputs.2)=nextTotal := by decide +kernel
theorem actual_source :
 Loops.SeqRun (ArraySourceCalls.Eval SynergyC.Header.layout SynergyHeightC.FullMainPrefix.service)
  (ArraySourceCalls.Declare SynergyC.Header.layout SynergyHeightC.FullMainPrefix.service)
  truth ArraySourceCalls.Scope SynergyHeightC.MainBudgetExecute.statements
  (SynergyHeightC.MainBudgetExecute.before total 261 SourceMainFramesV1.Point0261.outputs.1 SourceMainFramesV1.Point0261.outputs.2)
  (.continuing (SynergyHeightC.MainBudgetExecute.afterBudget total 261
   SourceMainFramesV1.Point0261.outputs.1 SourceMainFramesV1.Point0261.outputs.2)) :=
 SynergyHeightC.MainBudgetExecute.source_of_execution execution
end SourceMainBudgetV1.Cell0261
open Lean Elab
run_elab do
 let env ← getEnv
 for n in ([`SourceMainBudgetV1.Cell0261.input_total_range,`SourceMainBudgetV1.Cell0261.execution,`SourceMainBudgetV1.Cell0261.next_total,`SourceMainBudgetV1.Cell0261.actual_source] : List Name) do
  let some ci := env.find? n | throwError "missing actual source-budget root"
  let ax ← Lean.collectAxioms n
  logInfo m!"SOURCE_BUDGET_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
