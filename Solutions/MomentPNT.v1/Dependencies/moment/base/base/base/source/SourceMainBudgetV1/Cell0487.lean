/- Exact actual C arithmetic suffix for cell487/768.
Proposed prefix integers are accepted only through kernel-checked execution and recurrence. -/
import SynergyHeightC.MainBudgetExecute
import SourceMainFramesV1.Point0487
import Lean.Util.CollectAxioms
open Lean Meta Elab Tactic
namespace SourceMainBudgetV1.Cell0487
open ScopedC ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def total : ProofBox := ⟨2768053078280441562785698214157007177,2768053078280441562785753965652618940⟩
def nextTotal : ProofBox := ⟨2769260488892040982652639054867342024,2769260488892040982652695208532156313⟩
theorem input_total_range : 0≤total.lo ∧ total.lo≤total.hi ∧ total.hi<ProofBox.scale 128 := by
 decide +kernel
theorem execution : SynergyHeightC.MainBudgetExecute.run total 487
 SourceMainFramesV1.Point0487.outputs.1 SourceMainFramesV1.Point0487.outputs.2=
 some (.continuing (SynergyHeightC.MainBudgetExecute.afterBudget total 487
  SourceMainFramesV1.Point0487.outputs.1 SourceMainFramesV1.Point0487.outputs.2)) := by
 unfold SynergyHeightC.MainBudgetExecute.run
 run_tac do
  let goal ← getMainGoal
  let target ← goal.getType
  let args := target.getAppArgs
  unless target.getAppFn.isConstOf ``Eq && args.size==3 do
   throwError "expected actual source-state equality"
  goal.assign (←mkEqRefl args[1]!)
theorem next_total : ProofBox.add total (SynergyHeightC.MainWeightModel.term
 (SynergyHeightC.MainBudgetExecute.left 487) (SynergyHeightC.MainBudgetExecute.right 487)
 SourceMainFramesV1.Point0487.outputs.1 SourceMainFramesV1.Point0487.outputs.2)=nextTotal := by decide +kernel
theorem actual_source :
 Loops.SeqRun (ArraySourceCalls.Eval SynergyC.Header.layout SynergyHeightC.FullMainPrefix.service)
  (ArraySourceCalls.Declare SynergyC.Header.layout SynergyHeightC.FullMainPrefix.service)
  truth ArraySourceCalls.Scope SynergyHeightC.MainBudgetExecute.statements
  (SynergyHeightC.MainBudgetExecute.before total 487 SourceMainFramesV1.Point0487.outputs.1 SourceMainFramesV1.Point0487.outputs.2)
  (.continuing (SynergyHeightC.MainBudgetExecute.afterBudget total 487
   SourceMainFramesV1.Point0487.outputs.1 SourceMainFramesV1.Point0487.outputs.2)) :=
 SynergyHeightC.MainBudgetExecute.source_of_execution execution
end SourceMainBudgetV1.Cell0487
open Lean Elab
run_elab do
 let env ← getEnv
 for n in ([`SourceMainBudgetV1.Cell0487.input_total_range,`SourceMainBudgetV1.Cell0487.execution,`SourceMainBudgetV1.Cell0487.next_total,`SourceMainBudgetV1.Cell0487.actual_source] : List Name) do
  let some ci := env.find? n | throwError "missing actual source-budget root"
  let ax ← Lean.collectAxioms n
  logInfo m!"SOURCE_BUDGET_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
