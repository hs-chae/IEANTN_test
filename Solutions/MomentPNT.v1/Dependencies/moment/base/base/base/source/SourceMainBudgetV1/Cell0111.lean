/- Exact actual C arithmetic suffix for cell111/768.
Proposed prefix integers are accepted only through kernel-checked execution and recurrence. -/
import SynergyHeightC.MainBudgetExecute
import SourceMainFramesV1.Point0111
import Lean.Util.CollectAxioms
open Lean Meta Elab Tactic
namespace SourceMainBudgetV1.Cell0111
open ScopedC ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def total : ProofBox := ⟨1152938257088271115404837879496481039,1152938257088271115404841706128577823⟩
def nextTotal : ProofBox := ⟨1161541742121852349759538872993275184,1161541742121852349759542742204061064⟩
theorem input_total_range : 0≤total.lo ∧ total.lo≤total.hi ∧ total.hi<ProofBox.scale 128 := by
 decide +kernel
theorem execution : SynergyHeightC.MainBudgetExecute.run total 111
 SourceMainFramesV1.Point0111.outputs.1 SourceMainFramesV1.Point0111.outputs.2=
 some (.continuing (SynergyHeightC.MainBudgetExecute.afterBudget total 111
  SourceMainFramesV1.Point0111.outputs.1 SourceMainFramesV1.Point0111.outputs.2)) := by
 unfold SynergyHeightC.MainBudgetExecute.run
 run_tac do
  let goal ← getMainGoal
  let target ← goal.getType
  let args := target.getAppArgs
  unless target.getAppFn.isConstOf ``Eq && args.size==3 do
   throwError "expected actual source-state equality"
  goal.assign (←mkEqRefl args[1]!)
theorem next_total : ProofBox.add total (SynergyHeightC.MainWeightModel.term
 (SynergyHeightC.MainBudgetExecute.left 111) (SynergyHeightC.MainBudgetExecute.right 111)
 SourceMainFramesV1.Point0111.outputs.1 SourceMainFramesV1.Point0111.outputs.2)=nextTotal := by decide +kernel
theorem actual_source :
 Loops.SeqRun (ArraySourceCalls.Eval SynergyC.Header.layout SynergyHeightC.FullMainPrefix.service)
  (ArraySourceCalls.Declare SynergyC.Header.layout SynergyHeightC.FullMainPrefix.service)
  truth ArraySourceCalls.Scope SynergyHeightC.MainBudgetExecute.statements
  (SynergyHeightC.MainBudgetExecute.before total 111 SourceMainFramesV1.Point0111.outputs.1 SourceMainFramesV1.Point0111.outputs.2)
  (.continuing (SynergyHeightC.MainBudgetExecute.afterBudget total 111
   SourceMainFramesV1.Point0111.outputs.1 SourceMainFramesV1.Point0111.outputs.2)) :=
 SynergyHeightC.MainBudgetExecute.source_of_execution execution
end SourceMainBudgetV1.Cell0111
open Lean Elab
run_elab do
 let env ← getEnv
 for n in ([`SourceMainBudgetV1.Cell0111.input_total_range,`SourceMainBudgetV1.Cell0111.execution,`SourceMainBudgetV1.Cell0111.next_total,`SourceMainBudgetV1.Cell0111.actual_source] : List Name) do
  let some ci := env.find? n | throwError "missing actual source-budget root"
  let ax ← Lean.collectAxioms n
  logInfo m!"SOURCE_BUDGET_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
