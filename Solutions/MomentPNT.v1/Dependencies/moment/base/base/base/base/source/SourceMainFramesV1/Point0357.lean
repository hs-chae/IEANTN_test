/- Actual unchanged C point358/768 in its real main frame, for every accumulated total. -/
import SynergyHeightC.FramedPointReplayAPI
import SynergyHeightC.FullMainFrame
import SynergyAnalytic.HeightPointLogGridDefs
import Lean.Util.CollectAxioms
open Lean Meta Elab Tactic
namespace SourceMainFramesV1.Point0357
open ScopedC ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def input : ProofBox := (SynergyAnalytic.HeightPoint.logCell 358).getD ⟨0,0⟩
def outputs : ProofBox × ProofBox :=
 (SynergyHeightC.PointExecuteAPI.modelOutputs input).getD (⟨0,0⟩,⟨0,0⟩)
theorem input_defined : SynergyAnalytic.HeightPoint.logCell 358=some input := by decide +kernel
theorem outputs_defined : SynergyHeightC.PointExecuteAPI.modelOutputs input=some outputs := by decide +kernel
/-- This tactic constructs only Eq.refl. Mandatory declaration kernel checking
must validate the entire actual C execution/state equality; no TC skip or oracle. -/
theorem execution (total : ProofBox) :
 SynergyHeightC.FullContractPointExecute.run (SynergyHeightC.FullMainFrame.base total 357) input=
 some (.unit,SynergyHeightC.PointExecuteAPI.filled
  (SynergyHeightC.FullMainFrame.base total 357) outputs.1 outputs.2) := by
 unfold SynergyHeightC.FullContractPointExecute.run
 run_tac do
  let goal ← getMainGoal
  let target ← goal.getType
  let args := target.getAppArgs
  unless target.getAppFn.isConstOf ``Eq && args.size == 3 do
   throwError "expected source execution equality"
  goal.assign (← mkEqRefl args[1]!)
theorem source_outputs (total : ProofBox) :
 SynergyHeightC.PointExecuteAPI.SourcePointOutputs
  (SynergyHeightC.FullMainFrame.base total 357) input outputs.1 outputs.2 :=
 SynergyHeightC.FramedPointReplayAPI.source_of_execution (execution total)
end SourceMainFramesV1.Point0357
open Lean Elab
run_elab do
 let env ← getEnv
 for n in ([`SourceMainFramesV1.Point0357.input_defined,`SourceMainFramesV1.Point0357.outputs_defined,`SourceMainFramesV1.Point0357.execution,`SourceMainFramesV1.Point0357.source_outputs] : List Name) do
  let some ci := env.find? n | throwError "missing sourcepoint {n}"
  let ax ← Lean.collectAxioms n
  logInfo m!"SOURCE_POINT_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
