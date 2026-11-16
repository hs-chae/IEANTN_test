/- Actual source loop endpoint declarations for cell557/768, every accumulated total. -/
import SynergyHeightC.FullMainEdges
import Lean.Util.CollectAxioms
open Lean Meta Elab Tactic
namespace SourceHeightEdgesV1.Edge0557
open ScopedC ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem left_defined : SynergyAnalytic.HeightPoint.logCell 557=some
 ((SynergyAnalytic.HeightPoint.logCell 557).getD ⟨0,0⟩) := by decide +kernel
theorem right_defined : SynergyAnalytic.HeightPoint.logCell 558=some
 ((SynergyAnalytic.HeightPoint.logCell 558).getD ⟨0,0⟩) := by decide +kernel
theorem actual_execution (total : ProofBox) :
 SynergyHeightC.FullMainEdges.run total 557=
  some (.continuing (SynergyHeightC.FullMainFrame.base total 557)) := by
 unfold SynergyHeightC.FullMainEdges.run
 run_tac do
  let goal ← getMainGoal
  let target ← goal.getType
  let args := target.getAppArgs
  unless target.getAppFn.isConstOf ``Eq && args.size==3 do
   throwError "expected actual source execution equality"
  goal.assign (←mkEqRefl args[1]!)
  logInfo "KERNEL_REFLEXIVITY_GOAL_ASSIGNED; mandatory declaration kernel check"
theorem source_edges (total : ProofBox) :
 Loops.SeqRun (ArraySourceCalls.Eval SynergyC.Header.layout SynergyHeightC.FullMainPrefix.service)
  (ArraySourceCalls.Declare SynergyC.Header.layout SynergyHeightC.FullMainPrefix.service)
  truth ArraySourceCalls.Scope SynergyHeightC.FullMainEdge.statements
  (SynergyHeightC.FullMainEdges.loopState total 557)
  (.continuing (SynergyHeightC.FullMainFrame.base total 557)) :=
 SynergyHeightC.FullMainEdges.actual_source_edges actual_execution total
end SourceHeightEdgesV1.Edge0557
open Lean Elab
run_elab do
 let env ← getEnv
 for n in ([`SourceHeightEdgesV1.Edge0557.left_defined,`SourceHeightEdgesV1.Edge0557.right_defined,`SourceHeightEdgesV1.Edge0557.actual_execution,`SourceHeightEdgesV1.Edge0557.source_edges] : List Name) do
  let some ci := env.find? n | throwError "missing source-edge root {n}"
  let ax ← Lean.collectAxioms n
  logInfo m!"SOURCE_EDGE_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
