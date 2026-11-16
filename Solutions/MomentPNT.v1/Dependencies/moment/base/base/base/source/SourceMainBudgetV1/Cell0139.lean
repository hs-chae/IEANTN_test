/- Exact actual C arithmetic suffix for cell139/768.
Proposed prefix integers are accepted only through kernel-checked execution and recurrence. -/
import SynergyHeightC.MainBudgetExecute
import SourceMainFramesV1.Point0139
import Lean.Util.CollectAxioms
open Lean Meta Elab Tactic
namespace SourceMainBudgetV1.Cell0139
open ScopedC ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def total : ProofBox := ⟨1382774031560268865175137774554638341,1382774031560268865175142863026949979⟩
def nextTotal : ProofBox := ⟨1390565621142670788024753842579834165,1390565621142670788024758978934416616⟩
theorem input_total_range : 0≤total.lo ∧ total.lo≤total.hi ∧ total.hi<ProofBox.scale 128 := by
 decide +kernel
theorem execution : SynergyHeightC.MainBudgetExecute.run total 139
 SourceMainFramesV1.Point0139.outputs.1 SourceMainFramesV1.Point0139.outputs.2=
 some (.continuing (SynergyHeightC.MainBudgetExecute.afterBudget total 139
  SourceMainFramesV1.Point0139.outputs.1 SourceMainFramesV1.Point0139.outputs.2)) := by
 unfold SynergyHeightC.MainBudgetExecute.run
 run_tac do
  let goal ← getMainGoal
  let target ← goal.getType
  let args := target.getAppArgs
  unless target.getAppFn.isConstOf ``Eq && args.size==3 do
   throwError "expected actual source-state equality"
  goal.assign (←mkEqRefl args[1]!)
theorem next_total : ProofBox.add total (SynergyHeightC.MainWeightModel.term
 (SynergyHeightC.MainBudgetExecute.left 139) (SynergyHeightC.MainBudgetExecute.right 139)
 SourceMainFramesV1.Point0139.outputs.1 SourceMainFramesV1.Point0139.outputs.2)=nextTotal := by decide +kernel
theorem actual_source :
 Loops.SeqRun (ArraySourceCalls.Eval SynergyC.Header.layout SynergyHeightC.FullMainPrefix.service)
  (ArraySourceCalls.Declare SynergyC.Header.layout SynergyHeightC.FullMainPrefix.service)
  truth ArraySourceCalls.Scope SynergyHeightC.MainBudgetExecute.statements
  (SynergyHeightC.MainBudgetExecute.before total 139 SourceMainFramesV1.Point0139.outputs.1 SourceMainFramesV1.Point0139.outputs.2)
  (.continuing (SynergyHeightC.MainBudgetExecute.afterBudget total 139
   SourceMainFramesV1.Point0139.outputs.1 SourceMainFramesV1.Point0139.outputs.2)) :=
 SynergyHeightC.MainBudgetExecute.source_of_execution execution
end SourceMainBudgetV1.Cell0139
open Lean Elab
run_elab do
 let env ← getEnv
 for n in ([`SourceMainBudgetV1.Cell0139.input_total_range,`SourceMainBudgetV1.Cell0139.execution,`SourceMainBudgetV1.Cell0139.next_total,`SourceMainBudgetV1.Cell0139.actual_source] : List Name) do
  let some ci := env.find? n | throwError "missing actual source-budget root"
  let ax ← Lean.collectAxioms n
  logInfo m!"SOURCE_BUDGET_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
